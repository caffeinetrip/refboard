'use strict';

const { ipcRenderer } = require('electron');
const nodePath = require('path');
const fs = require('fs');
const os = require('os');
const crypto = require('crypto');
const { pathToFileURL } = require('url');

let parseGIF;
let decompressFrames;
try {
  ({ parseGIF, decompressFrames } = require('gifuct-js'));
} catch (e) {
  parseGIF = null;
  decompressFrames = null;
}

const APP_VERSION = 2;
const APP_TYPE = 'game-analysis-library';

const $ = id => document.getElementById(id);
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
const now = () => new Date().toISOString();
const esc = value => String(value ?? '')
  .replace(/&/g, '&amp;')
  .replace(/</g, '&lt;')
  .replace(/>/g, '&gt;')
  .replace(/"/g, '&quot;');

const SESSION_CACHE_DIR = nodePath.join(os.tmpdir(), 'refboard-analysis-' + process.pid);
try { fs.mkdirSync(SESSION_CACHE_DIR, { recursive: true }); } catch (e) {}

function sessionCacheKey(fp) {
  return crypto.createHash('md5').update(fp).digest('hex');
}

function sessionCacheWrite(fp, data) {
  try {
    fs.writeFileSync(nodePath.join(SESSION_CACHE_DIR, sessionCacheKey(fp) + '.json'), JSON.stringify(data));
  } catch (e) {}
}

function sessionCacheClear() {
  try {
    fs.readdirSync(SESSION_CACHE_DIR).forEach(f => fs.unlinkSync(nodePath.join(SESSION_CACHE_DIR, f)));
  } catch (e) {}
}

process.on('exit', sessionCacheClear);

function defaultQuestionTemplates() {
  return [
    ['q_core_loop', 'Core loop', 'What does the player repeat again and again?', 'Design'],
    ['q_run_length', 'Run length', 'How long is one run, wave, attempt, or cycle?', 'Structure'],
    ['q_in_run_progress', 'In-run progress', 'What gives a sense of progress during the run?', 'Progress'],
    ['q_next_run', 'Next run', 'What makes the player start one more run?', 'Progress'],
    ['q_win_fail', 'Win / fail state', 'How does the game handle victory, failure, score, or soft failure?', 'Design'],
    ['q_meta_progression', 'Meta progression', 'What does the player get between runs?', 'Progress'],
    ['q_relics', 'Relics / upgrades', 'How do items, relics, symbols, upgrades, and synergies work?', 'Systems'],
    ['q_pacing', 'Pacing', 'Where are the spikes, valleys, boring moments, and wow moments?', 'Feel'],
    ['q_ui_ux', 'UI / UX', 'What is instantly clear, and what creates friction?', 'UX'],
    ['q_polish', 'Polish', 'Which animations, sounds, effects, and feedback are worth remembering?', 'Polish'],
    ['q_steal', 'Steal this', 'What can be adapted for your own game?', 'Takeaways'],
    ['q_avoid', 'Avoid this', 'What should definitely not be repeated?', 'Takeaways'],
  ].map((row, order) => ({
    id: row[0],
    title: row[1],
    prompt: row[2],
    category: row[3],
    enabled: true,
    order,
  }));
}

function freshState() {
  return {
    projectPath: null,
    projectName: 'Untitled',
    modified: false,
    view: 'library',
    activeGameId: null,
    activeTab: 'questions',
    activeMediaId: null,
    questionTemplates: defaultQuestionTemplates(),
    games: [],
    media: [],
  };
}

let S = freshState();

let V = {
  zoom: 1,
  panX: 0,
  panY: 0,
  panning: false,
  px: 0,
  py: 0,
  speed: 1,
  frameMode: 'playback',
  currentMediaId: null,
  currentMediaType: null,
  gifFrames: null,
  gifRenderedFrames: null,
  gifIdx: 0,
  gifPlaying: false,
  gifTimer: null,
  gifTotalDuration: 0,
  tlDragging: false,
};

let activeGifCache = null;
let toastTimer = null;
let modalCb = null;

function getActiveGame() {
  return S.games.find(g => g.id === S.activeGameId) || null;
}

function getMediaById(id) {
  return S.media.find(m => m.id === id) || null;
}

function getGameMedia(gameId, kind) {
  return S.media
    .filter(m => m.gameId === gameId && (!kind || m.kind === kind))
    .sort((a, b) => String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
}

function orderedTemplates() {
  return [...S.questionTemplates].sort((a, b) => (a.order ?? 0) - (b.order ?? 0));
}

function enabledTemplates() {
  return orderedTemplates().filter(t => t.enabled !== false);
}

function ensureGameShape(game) {
  game.genre ??= '';
  game.status ??= '';
  game.link ??= '';
  game.iconMediaId ??= null;
  game.coverMediaId ??= null;
  game.answers ??= {};
  game.notes ??= { blocks: [] };
  game.notes.blocks ??= [];
  game.collapsedQuestions ??= [];
  game.createdAt ??= now();
  game.updatedAt ??= now();
  return game;
}

function ensureAnswer(game, questionId) {
  ensureGameShape(game);
  if (!game.answers[questionId]) {
    game.answers[questionId] = {
      blocks: [{ id: uid(), type: 'text', text: '' }],
      updatedAt: now(),
    };
  }
  if (!Array.isArray(game.answers[questionId].blocks)) game.answers[questionId].blocks = [];
  if (!game.answers[questionId].blocks.some(b => b.type === 'text')) {
    game.answers[questionId].blocks.unshift({ id: uid(), type: 'text', text: '' });
  }
  return game.answers[questionId];
}

function textBlock(blocks) {
  let block = blocks.find(b => b.type === 'text');
  if (!block) {
    block = { id: uid(), type: 'text', text: '' };
    blocks.unshift(block);
  }
  return block;
}

function touchGame(gameId) {
  const game = S.games.find(g => g.id === gameId);
  if (game) game.updatedAt = now();
}

function markDirty() {
  S.modified = true;
  updateChrome();
}

function updateChrome() {
  $('project-name').textContent = S.projectName + (S.modified ? ' •' : '');
  document.querySelectorAll('.nav-btn').forEach(btn => {
    btn.classList.toggle('active', btn.dataset.view === S.view);
  });
}

function toast(msg) {
  const el = $('toast');
  el.textContent = msg;
  el.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => el.classList.remove('show'), 1900);
}

function showLoading(text = 'Loading...') {
  $('loading-overlay').classList.remove('hidden');
  document.querySelector('.loading-text').textContent = text;
}

function hideLoading() {
  $('loading-overlay').classList.add('hidden');
}

function askText(title, value, okLabel, cb) {
  $('modal-title').textContent = title;
  $('modal-inp').value = value || '';
  $('modal-ok').textContent = okLabel || 'OK';
  modalCb = cb;
  $('modal-bg').classList.remove('hidden');
  setTimeout(() => {
    $('modal-inp').focus();
    $('modal-inp').select();
  }, 0);
}

function closeModal() {
  $('modal-bg').classList.add('hidden');
  modalCb = null;
}

function setView(view) {
  if (S.view !== 'game' || view !== 'game') stopViewer();
  S.view = view;
  renderApp();
}

function openGame(gameId, tab = 'questions') {
  stopViewer();
  S.view = 'game';
  S.activeGameId = gameId;
  S.activeTab = tab;
  S.activeMediaId = null;
  renderApp();
}

function renderApp() {
  updateChrome();
  renderMiniGames();
  if (S.view === 'templates') renderTemplates();
  else if (S.view === 'game') renderGameWorkspace();
  else renderLibrary();
}

function renderMiniGames() {
  const wrap = $('mini-game-list');
  wrap.innerHTML = '';
  const games = [...S.games]
    .sort((a, b) => String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')))
    .slice(0, 24);

  if (!games.length) {
    wrap.innerHTML = '<div class="card-sub">Empty</div>';
    return;
  }

  games.forEach(game => {
    const row = document.createElement('div');
    row.className = 'mini-game' + (S.activeGameId === game.id && S.view === 'game' ? ' active' : '');
    row.innerHTML = `<span class="mini-dot"></span><span class="mini-title">${esc(game.title)}</span>`;
    row.onclick = () => openGame(game.id, S.activeTab || 'questions');
    wrap.appendChild(row);
  });
}

function renderLibrary() {
  stopViewer();
  const main = $('main');
  main.innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Games</h1>
        </div>
        <div class="head-actions">
          <button class="ghost-btn" id="library-templates">Questions</button>
          <button class="inline-btn" id="library-new-game">+ Game</button>
        </div>
      </div>
      <div class="screen-scroll" id="library-body"></div>
    </section>`;

  $('library-new-game').onclick = createGameFlow;
  $('library-templates').onclick = () => setView('templates');

  const body = $('library-body');
  if (!S.games.length) {
    body.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">Empty</div>
          <button class="inline-btn" id="empty-new-game">+ Game</button>
        </div>
      </div>`;
    $('empty-new-game').onclick = createGameFlow;
    return;
  }

  body.innerHTML = '<div class="games-grid" id="games-grid"></div>';
  const grid = $('games-grid');
  [...S.games]
    .sort((a, b) => String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')))
    .forEach(game => grid.appendChild(buildGameCard(game)));
}

function buildGameCard(game) {
  const card = document.createElement('div');
  card.className = 'game-card';
  const cover = getMediaById(game.iconMediaId) || getMediaById(game.coverMediaId) || getGameMedia(game.id)[0];
  card.innerHTML = `
    <div class="game-card-main">
      <div class="game-cover">${cover ? mediaPreviewHTML(cover, true) : esc((game.title || 'GAME').slice(0, 3).toUpperCase())}</div>
      <div class="game-name">${esc(game.title)}</div>
    </div>
    <div class="card-sub">${formatShortDate(game.updatedAt)}</div>`;
  card.onclick = () => openGame(game.id);
  return card;
}

function renderTemplates() {
  stopViewer();
  const main = $('main');
  main.innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Questions</h1>
        </div>
        <div class="head-actions">
          <button class="ghost-btn" id="back-library">Games</button>
          <button class="inline-btn" id="add-template">+ Question</button>
        </div>
      </div>
      <div class="screen-scroll">
        <div class="template-card">
          <div id="templates-list"></div>
        </div>
      </div>
    </section>`;

  $('back-library').onclick = () => setView('library');
  $('add-template').onclick = addTemplateFlow;
  renderTemplateRows();
}

function renderTemplateRows() {
  const list = $('templates-list');
  list.innerHTML = '';
  orderedTemplates().forEach((template, index) => {
    const row = document.createElement('div');
    row.className = 'template-row';
    row.innerHTML = `
      <div class="field">
        <label class="field-label">Question</label>
        <input class="text-input tmpl-title" value="${esc(template.title)}">
      </div>
      <div class="field">
        <label class="field-label">Prompt</label>
        <textarea class="text-area tmpl-prompt" style="min-height:74px">${esc(template.prompt)}</textarea>
      </div>
      <label class="check-wrap"><input type="checkbox" class="tmpl-enabled" ${template.enabled !== false ? 'checked' : ''}> Enabled</label>
      <div class="card-actions">
        <button class="mini-btn tmpl-up" title="Move up">Up</button>
        <button class="mini-btn tmpl-down" title="Move down">Down</button>
        <button class="danger-btn tmpl-delete">Delete</button>
      </div>`;

    row.querySelector('.tmpl-title').oninput = e => {
      template.title = e.target.value;
      markDirty();
    };
    row.querySelector('.tmpl-prompt').oninput = e => {
      template.prompt = e.target.value;
      markDirty();
    };
    row.querySelector('.tmpl-enabled').onchange = e => {
      template.enabled = e.target.checked;
      markDirty();
    };
    row.querySelector('.tmpl-up').onclick = () => moveTemplate(index, -1);
    row.querySelector('.tmpl-down').onclick = () => moveTemplate(index, 1);
    row.querySelector('.tmpl-delete').onclick = () => {
      if (!confirm(`Delete question "${template.title}"? Answers will stay in the file, but will be hidden.`)) return;
      S.questionTemplates = S.questionTemplates.filter(t => t.id !== template.id);
      normalizeTemplateOrder();
      markDirty();
      renderTemplateRows();
    };
    list.appendChild(row);
  });
}

function normalizeTemplateOrder() {
  orderedTemplates().forEach((template, i) => { template.order = i; });
}

function moveTemplate(index, dir) {
  const list = orderedTemplates();
  const to = index + dir;
  if (to < 0 || to >= list.length) return;
  const tmp = list[index].order;
  list[index].order = list[to].order;
  list[to].order = tmp;
  normalizeTemplateOrder();
  markDirty();
  renderTemplateRows();
}

function addTemplateFlow() {
  askText('New Question', '', 'Create', title => {
    S.questionTemplates.push({
      id: 'q_' + uid(),
      title,
      prompt: '',
      category: 'Custom',
      enabled: true,
      order: S.questionTemplates.length,
    });
    markDirty();
    renderApp();
  });
}

function renderGameWorkspace() {
  const game = getActiveGame();
  if (!game) {
    S.view = 'library';
    renderLibrary();
    return;
  }
  ensureGameShape(game);

  const tabs = [
    ['questions', 'Questions'],
    ['notes', 'Notes'],
    ['photos', 'Photos'],
    ['videos', 'Videos'],
  ];
  const icon = getMediaById(game.iconMediaId);

  $('main').innerHTML = `
    <section class="game-workspace">
      <div class="game-header">
        <div class="game-top">
          <div class="game-main-row">
            <button class="game-icon" id="game-icon" title="Icon">${icon ? mediaPreviewHTML(icon, true) : '+'}</button>
            <input id="game-title" class="game-title-input" value="${esc(game.title)}" spellcheck="false">
          </div>
          <div class="head-actions">
            <button class="ghost-btn" id="game-back">Games</button>
            <button class="ghost-btn" id="set-game-icon">Icon</button>
            <button class="danger-btn" id="delete-game">Delete</button>
          </div>
        </div>
        <div class="tabs">
          ${tabs.map(([id, label]) => `<button class="tab-btn ${S.activeTab === id ? 'active' : ''}" data-tab="${id}">${label}</button>`).join('')}
        </div>
      </div>
      <div class="tab-content" id="tab-content"></div>
    </section>`;

  $('game-back').onclick = () => setView('library');
  $('game-icon').onclick = () => setGameIcon(game);
  $('set-game-icon').onclick = () => setGameIcon(game);
  $('delete-game').onclick = deleteActiveGame;
  $('game-title').oninput = e => {
    game.title = e.target.value;
    touchGame(game.id);
    markDirty();
    renderMiniGames();
  };

  document.querySelectorAll('.tab-btn').forEach(btn => {
    btn.onclick = () => {
      if (S.activeTab !== btn.dataset.tab) stopViewer();
      S.activeTab = btn.dataset.tab;
      S.activeMediaId = null;
      renderGameWorkspace();
    };
  });

  if (S.activeTab === 'notes') renderNotesTab(game);
  else if (S.activeTab === 'photos') renderMediaTab(game, 'photo');
  else if (S.activeTab === 'videos') renderMediaTab(game, 'video');
  else renderQuestionsTab(game);
}

function renderQuestionsTab(game) {
  hidePlayback();
  const content = $('tab-content');
  const templates = enabledTemplates();
  content.innerHTML = `
    <div class="tab-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div>
            <div class="eyebrow">Questions</div>
          </div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="edit-templates">Template</button>
        </div>
      </div>
      <div class="question-list" id="question-list"></div>
    </div>`;

  $('edit-templates').onclick = () => setView('templates');
  const list = $('question-list');
  if (!templates.length) {
    list.innerHTML = '<div class="block-card"><div class="empty-title">No questions</div></div>';
    return;
  }

  templates.forEach(template => {
    const answer = ensureAnswer(game, template.id);
    const txt = textBlock(answer.blocks);
    const collapsed = game.collapsedQuestions.includes(template.id);
    const mediaBlocks = answer.blocks.filter(b => b.type === 'media');
    const card = document.createElement('div');
    card.className = 'question-card';
    card.innerHTML = `
      <div class="card-head">
        <div>
          <h3 class="card-title">${esc(template.title)}</h3>
          <div class="card-sub">${esc(template.prompt || '')}</div>
        </div>
        <div class="card-actions">
          <button class="mini-btn collapse-question">${collapsed ? 'Open' : 'Collapse'}</button>
        </div>
      </div>
      <div class="card-body ${collapsed ? 'hidden' : ''}">
        <textarea class="text-area question-answer" placeholder="Answer...">${esc(txt.text)}</textarea>
        <div class="toolbar" style="margin:12px 0 0">
          <div class="toolbar-left">
            <button class="ghost-btn add-answer-media">+ Media</button>
          </div>
        </div>
        <div class="media-attachments">${mediaBlocks.map(block => mediaChipHTML(block.mediaId, block.id)).join('')}</div>
      </div>`;

    card.querySelector('.collapse-question').onclick = () => {
      if (collapsed) game.collapsedQuestions = game.collapsedQuestions.filter(id => id !== template.id);
      else game.collapsedQuestions.push(template.id);
      markDirty();
      renderQuestionsTab(game);
    };
    const textarea = card.querySelector('.question-answer');
    if (textarea) {
      textarea.oninput = e => {
        txt.text = e.target.value;
        answer.updatedAt = now();
        touchGame(game.id);
        markDirty();
      };
    }
    const addMedia = card.querySelector('.add-answer-media');
    if (addMedia) addMedia.onclick = () => addQuestionMedia(game, template.id);

    card.querySelectorAll('[data-remove-block]').forEach(btn => {
      btn.onclick = () => {
        answer.blocks = answer.blocks.filter(b => b.id !== btn.dataset.removeBlock);
        answer.updatedAt = now();
        touchGame(game.id);
        markDirty();
        renderQuestionsTab(game);
      };
    });
    list.appendChild(card);
  });
}

function renderNotesTab(game) {
  hidePlayback();
  const blocks = game.notes.blocks;
  $('tab-content').innerHTML = `
    <div class="tab-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div>
            <div class="eyebrow">Notes</div>
          </div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="add-note-text">+ Text</button>
          <button class="ghost-btn" id="add-note-image">+ Photo</button>
          <button class="ghost-btn" id="add-note-video">+ Video</button>
        </div>
      </div>
      <div class="notes-list" id="notes-list"></div>
    </div>`;

  $('add-note-text').onclick = () => {
    blocks.push({ id: uid(), type: 'text', text: '' });
    touchGame(game.id);
    markDirty();
    renderNotesTab(game);
  };
  $('add-note-image').onclick = () => addNoteMedia(game, 'photo');
  $('add-note-video').onclick = () => addNoteMedia(game, 'video');

  const list = $('notes-list');
  if (!blocks.length) {
    list.innerHTML = '<div class="block-card"><div class="empty-title">Empty</div></div>';
    return;
  }

  blocks.forEach(block => {
    const card = document.createElement('div');
    card.className = 'note-card';
    if (block.type === 'text') {
      card.innerHTML = `
        <div class="card-head">
          <h3 class="card-title">Text</h3>
          <div class="card-actions"><button class="danger-btn delete-note">Delete</button></div>
        </div>
        <div class="card-body">
          <textarea class="text-area note-text" placeholder="Note...">${esc(block.text)}</textarea>
        </div>`;
      card.querySelector('.note-text').oninput = e => {
        block.text = e.target.value;
        touchGame(game.id);
        markDirty();
      };
    } else {
      const media = getMediaById(block.mediaId);
      card.innerHTML = `
        <div class="card-head">
          <div>
            <h3 class="card-title">${esc(media?.name || 'Missing file')}</h3>
            <div class="card-sub">${esc(mediaKindLabel(media?.kind))}</div>
          </div>
          <div class="card-actions">
            ${media ? '<button class="ghost-btn open-note-media">Open</button>' : ''}
            <button class="danger-btn delete-note">Delete</button>
          </div>
        </div>
        <div class="card-body">
          <div class="media-attachments">${mediaChipHTML(block.mediaId, block.id, false)}</div>
          <div class="field" style="margin-top:12px">
            <label class="field-label">Caption</label>
            <input class="text-input note-caption" value="${esc(block.caption || '')}" placeholder="">
          </div>
        </div>`;
      const cap = card.querySelector('.note-caption');
      if (cap) cap.oninput = e => {
        block.caption = e.target.value;
        touchGame(game.id);
        markDirty();
      };
      const open = card.querySelector('.open-note-media');
      if (open && media) open.onclick = () => {
        S.activeTab = media.kind === 'video' ? 'videos' : 'photos';
        S.activeMediaId = media.id;
        renderGameWorkspace();
      };
    }

    card.querySelector('.delete-note').onclick = () => {
      game.notes.blocks = game.notes.blocks.filter(b => b.id !== block.id);
      touchGame(game.id);
      markDirty();
      renderNotesTab(game);
    };
    list.appendChild(card);
  });
}

function renderMediaTab(game, kind) {
  const label = kind === 'video' ? 'Videos' : 'Photos';

  $('tab-content').innerHTML = `
    <div class="media-workspace">
      <aside class="media-panel">
        <div class="media-panel-head">
          <div>
            <div class="pane-label">${label}</div>
          </div>
          <button class="mini-btn" id="add-media-btn">+</button>
        </div>
        <div class="media-list" id="media-list"></div>
      </aside>
      <section id="viewer-wrap">
        <div id="viewer-empty">
          <div class="empty-title">Empty</div>
        </div>
        <div id="viewer-stage" class="hidden">
          <canvas id="gif-canvas" class="hidden"></canvas>
          <img id="img-viewer" class="hidden" draggable="false">
          <video id="vid-viewer" class="hidden" loop></video>
        </div>
        <div id="zoom-hud">
          <button class="zh-btn" id="z-out">-</button>
          <span id="zoom-pct">100%</span>
          <button class="zh-btn" id="z-in">+</button>
          <button class="zh-btn" id="z-fit">Fit</button>
        </div>
      </section>
      <aside class="info-panel" id="info-panel">
        <div class="info-head"><span class="pane-label">Properties</span></div>
        <div class="info-body" id="info-body">
          <div class="card-sub">Select a file</div>
        </div>
      </aside>
    </div>`;

  $('add-media-btn').onclick = () => addMediaToActiveGame(kind);
  bindViewerEvents(kind);
  renderMediaList(game, kind);

  const selected = getMediaById(S.activeMediaId);
  if (selected && selected.gameId === game.id && selected.kind === kind) loadMedia(selected);
  else {
    clearViewer();
    hidePlayback();
  }
}

function renderMediaList(game, kind) {
  const list = $('media-list');
  const items = getGameMedia(game.id, kind);
  list.innerHTML = '';

  items.forEach(item => {
    const thumb = document.createElement('div');
    thumb.className = 'media-thumb' + (S.activeMediaId === item.id ? ' active' : '');
    thumb.innerHTML = `
      ${mediaPreviewHTML(item, true)}
      <span class="media-badge">${esc(item.type.toUpperCase())}</span>
      <div class="media-thumb-title">${esc(item.name)}</div>`;
    thumb.onclick = () => {
      S.activeMediaId = item.id;
      renderMediaList(game, kind);
      loadMedia(item);
    };
    list.appendChild(thumb);
  });

  const drop = document.createElement('div');
  drop.className = 'drop-card';
  drop.id = 'media-drop-card';
  drop.textContent = '+ Add';
  drop.onclick = () => addMediaToActiveGame(kind);
  drop.addEventListener('dragover', e => {
    e.preventDefault();
    drop.classList.add('drag-target');
  });
  drop.addEventListener('dragleave', () => drop.classList.remove('drag-target'));
  drop.addEventListener('drop', e => {
    e.preventDefault();
    drop.classList.remove('drag-target');
    addDroppedFiles(e.dataTransfer.files, kind);
  });
  list.appendChild(drop);
}

function renderInfo(item) {
  const body = $('info-body');
  if (!body || !item) return;
  const fp = resolveMediaPath(item);
  body.innerHTML = `
    <div class="field">
      <label class="field-label">Title</label>
      <input id="info-title" class="text-input" value="${esc(item.name)}">
    </div>
    <div class="field">
      <label class="field-label">Note</label>
      <textarea id="info-desc" class="text-area" placeholder="">${esc(item.description || '')}</textarea>
    </div>
    <div class="field">
      <label class="field-label">Tags</label>
      <input id="info-tags" class="text-input" value="${esc((item.tags || []).join(', '))}" placeholder="">
    </div>
    <button class="ghost-btn" id="make-cover">Use on card</button>
    <button class="danger-btn" id="remove-media">Remove</button>
    <div>
      <div class="meta-row"><span>Type</span><span class="meta-value">${esc(item.type)}</span></div>
      <div class="meta-row"><span>File</span><span class="meta-value">${esc(nodePath.basename(fp || item.path || ''))}</span></div>
    </div>`;

  $('info-title').oninput = e => {
    item.name = e.target.value;
    item.updatedAt = now();
    touchGame(item.gameId);
    markDirty();
    renderMediaList(getActiveGame(), item.kind);
  };
  $('info-desc').oninput = e => {
    item.description = e.target.value;
    item.updatedAt = now();
    touchGame(item.gameId);
    markDirty();
  };
  $('info-tags').oninput = e => {
    item.tags = e.target.value.split(',').map(s => s.trim()).filter(Boolean);
    item.updatedAt = now();
    touchGame(item.gameId);
    markDirty();
  };
  $('make-cover').onclick = () => {
    const game = getActiveGame();
    if (!game) return;
    game.coverMediaId = item.id;
    touchGame(game.id);
    markDirty();
    toast('Card updated');
  };
  $('remove-media').onclick = () => removeMedia(item.id);
}

function mediaChipHTML(mediaId, blockId, removable = true) {
  const media = getMediaById(mediaId);
  if (!media) {
    return `<div class="media-chip"><div class="media-chip-preview">Missing</div><div class="media-chip-foot"><span class="media-chip-name">Missing</span>${removable ? `<button class="mini-btn" data-remove-block="${esc(blockId)}">x</button>` : ''}</div></div>`;
  }
  return `
    <div class="media-chip">
      <div class="media-chip-preview">${mediaPreviewHTML(media, true)}</div>
      <div class="media-chip-foot">
        <span class="media-chip-name">${esc(media.name)}</span>
        ${removable ? `<button class="mini-btn" data-remove-block="${esc(blockId)}">x</button>` : ''}
      </div>
    </div>`;
}

function mediaPreviewHTML(media, compact = false) {
  const fp = resolveMediaPath(media);
  const url = fileUrl(fp);
  if (!fp || !fs.existsSync(fp)) return '<span>Missing</span>';
  if (media.type === 'video') return `<video src="${esc(url)}" muted preload="metadata"></video>`;
  if (media.type === 'gif' || media.type === 'image') return `<img src="${esc(url)}" draggable="false">`;
  return compact ? '<span>Media</span>' : `<span>${esc(media.type)}</span>`;
}

function mediaKindLabel(kind) {
  if (kind === 'photo') return 'photo';
  if (kind === 'video') return 'video';
  if (kind === 'icon') return 'icon';
  return 'media';
}

function createGameFlow() {
  askText('New Game', '', 'Create', title => {
    const game = ensureGameShape({
      id: 'g_' + uid(),
      title,
      genre: '',
      status: '',
      link: '',
      iconMediaId: null,
      coverMediaId: null,
      answers: {},
      notes: { blocks: [] },
      collapsedQuestions: [],
      createdAt: now(),
      updatedAt: now(),
    });
    S.games.push(game);
    S.activeGameId = game.id;
    S.activeTab = 'questions';
    S.view = 'game';
    markDirty();
    renderApp();
  });
}

async function setGameIcon(game) {
  const result = await ipcRenderer.invoke('dialog:open', {
    title: 'Game icon',
    filters: [{ name: 'Images', extensions: ['png', 'jpg', 'jpeg', 'webp', 'bmp', 'svg', 'gif'] }],
    properties: ['openFile'],
  });
  if (result.canceled || !result.filePaths?.length) return;
  const media = registerMediaFile(result.filePaths[0], game.id, 'icon');
  if (!media) {
    toast('Could not add icon');
    return;
  }
  game.iconMediaId = media.id;
  touchGame(game.id);
  markDirty();
  renderGameWorkspace();
}

function deleteActiveGame() {
  const game = getActiveGame();
  if (!game) return;
  if (!confirm(`Delete game "${game.title}"? Files in attachments stay on disk.`)) return;
  S.games = S.games.filter(g => g.id !== game.id);
  S.media = S.media.filter(m => m.gameId !== game.id);
  S.activeGameId = null;
  S.activeMediaId = null;
  S.view = 'library';
  stopViewer();
  markDirty();
  renderApp();
}

async function addQuestionMedia(game, questionId) {
  const files = await pickMediaFiles('mixed');
  if (!files.length) return;
  const answer = ensureAnswer(game, questionId);
  files.forEach(fp => {
    const type = inferMediaType(fp);
    const kind = type === 'video' || type === 'gif' ? 'video' : 'photo';
    const media = registerMediaFile(fp, game.id, kind);
    if (media) answer.blocks.push({ id: uid(), type: 'media', mediaId: media.id, caption: '' });
  });
  answer.updatedAt = now();
  touchGame(game.id);
  markDirty();
  renderQuestionsTab(game);
}

async function addNoteMedia(game, kind) {
  const files = await pickMediaFiles(kind);
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, game.id, kind);
    if (media) game.notes.blocks.push({ id: uid(), type: 'media', mediaId: media.id, caption: '' });
  });
  touchGame(game.id);
  markDirty();
  renderNotesTab(game);
}

async function addMediaToActiveGame(kind) {
  const game = getActiveGame();
  if (!game) return;
  const files = await pickMediaFiles(kind);
  if (!files.length) return;
  files.forEach(fp => registerMediaFile(fp, game.id, kind));
  touchGame(game.id);
  markDirty();
  renderMediaTab(game, kind);
  toast(`Added: ${files.length}`);
}

function addDroppedFiles(fileList, kind) {
  const game = getActiveGame();
  if (!game) return;
  const files = Array.from(fileList || []).map(f => f.path).filter(Boolean);
  const valid = files.filter(fp => kindAllowsFile(kind, fp));
  if (!valid.length) {
    toast(kind === 'video' ? 'Use video or GIF' : 'Use image or GIF');
    return;
  }
  valid.forEach(fp => registerMediaFile(fp, game.id, kind));
  touchGame(game.id);
  markDirty();
  renderMediaTab(game, kind);
  toast(`Added: ${valid.length}`);
}

async function pickMediaFiles(kind) {
  const extensions = kind === 'photo'
    ? ['png', 'jpg', 'jpeg', 'webp', 'bmp', 'svg', 'gif']
    : kind === 'video'
      ? ['mp4', 'webm', 'mov', 'mkv', 'gif']
      : ['png', 'jpg', 'jpeg', 'webp', 'bmp', 'svg', 'gif', 'mp4', 'webm', 'mov', 'mkv'];
  const result = await ipcRenderer.invoke('dialog:open', {
    title: 'Add media',
    filters: [{ name: 'Media', extensions }],
    properties: ['openFile', 'multiSelections'],
  });
  if (result.canceled || !result.filePaths?.length) return [];
  return result.filePaths.filter(fp => kind === 'mixed' || kindAllowsFile(kind, fp));
}

function registerMediaFile(fp, gameId, kind) {
  if (!fp || !fs.existsSync(fp)) return null;
  if (!kindAllowsFile(kind, fp)) return null;
  const id = 'm_' + uid();
  const type = inferMediaType(fp);
  const item = {
    id,
    gameId,
    kind,
    type,
    name: nodePath.basename(fp, nodePath.extname(fp)),
    path: fp,
    originalPath: fp,
    description: '',
    tags: [],
    copied: false,
    createdAt: now(),
    updatedAt: now(),
  };
  if (S.projectPath) copyMediaIntoProject(item, fp);
  S.media.push(item);
  return item;
}

function removeMedia(mediaId) {
  const media = getMediaById(mediaId);
  if (!media) return;
  if (!confirm(`Remove "${media.name}" from this library? The file stays on disk.`)) return;
  S.media = S.media.filter(m => m.id !== mediaId);
  S.games.forEach(game => {
    Object.values(game.answers || {}).forEach(answer => {
      answer.blocks = (answer.blocks || []).filter(block => block.mediaId !== mediaId);
    });
    if (game.notes?.blocks) game.notes.blocks = game.notes.blocks.filter(block => block.mediaId !== mediaId);
    if (game.iconMediaId === mediaId) game.iconMediaId = null;
    if (game.coverMediaId === mediaId) game.coverMediaId = null;
  });
  if (S.activeMediaId === mediaId) S.activeMediaId = null;
  stopViewer();
  touchGame(media.gameId);
  markDirty();
  renderGameWorkspace();
}

function inferMediaType(fp) {
  const ext = nodePath.extname(fp).toLowerCase();
  if (ext === '.gif') return 'gif';
  if (['.mp4', '.webm', '.mov', '.mkv'].includes(ext)) return 'video';
  return 'image';
}

function kindAllowsFile(kind, fp) {
  const type = inferMediaType(fp);
  if (kind === 'mixed') return true;
  if (kind === 'icon') return type === 'image' || type === 'gif';
  if (kind === 'photo') return type === 'image' || type === 'gif';
  if (kind === 'video') return type === 'video' || type === 'gif';
  return false;
}

function safeFileName(name) {
  return String(name || 'media').replace(/[<>:"/\\|?*\x00-\x1f]/g, '_').slice(0, 120);
}

function copyMediaIntoProject(item, sourcePath) {
  if (!S.projectPath || !sourcePath || !fs.existsSync(sourcePath)) return;
  const projectDir = nodePath.dirname(S.projectPath);
  const attachmentRoot = nodePath.basename(S.projectPath, nodePath.extname(S.projectPath)) + '_attachments';
  const relDir = nodePath.join(attachmentRoot, item.gameId);
  const absDir = nodePath.join(projectDir, relDir);
  fs.mkdirSync(absDir, { recursive: true });
  const destName = `${item.id}-${safeFileName(nodePath.basename(sourcePath))}`;
  const absDest = nodePath.join(absDir, destName);
  if (nodePath.resolve(sourcePath) !== nodePath.resolve(absDest)) {
    fs.copyFileSync(sourcePath, absDest);
  }
  item.path = nodePath.relative(projectDir, absDest);
  item.copied = true;
}

function ensureAllMediaCopied() {
  if (!S.projectPath) return;
  S.media.forEach(item => {
    const fp = resolveMediaPath(item);
    if (!fp || !fs.existsSync(fp)) return;
    if (!item.copied || nodePath.isAbsolute(item.path)) copyMediaIntoProject(item, fp);
  });
}

function resolveMediaPath(media) {
  if (!media) return '';
  const fp = media.path || media.originalPath || '';
  if (!fp) return '';
  if (nodePath.isAbsolute(fp)) return fp;
  if (!S.projectPath) return fp;
  return nodePath.join(nodePath.dirname(S.projectPath), fp);
}

function fileUrl(fp) {
  try { return pathToFileURL(fp).toString(); }
  catch (e) { return ''; }
}

function serializeProject() {
  return {
    version: APP_VERSION,
    type: APP_TYPE,
    questionTemplates: S.questionTemplates,
    games: S.games,
    media: S.media,
  };
}

function newProject() {
  if (S.modified && !confirm('Discard unsaved changes?')) return;
  stopViewer();
  sessionCacheClear();
  S = freshState();
  renderApp();
  toast('New library');
}

async function openProject() {
  if (S.modified && !confirm('Discard unsaved changes?')) return;
  const result = await ipcRenderer.invoke('dialog:open', {
    title: 'Open library',
    filters: [{ name: 'RefBoard', extensions: ['refboard'] }],
    properties: ['openFile'],
  });
  if (result.canceled || !result.filePaths?.length) return;
  const fp = result.filePaths[0];
  showLoading('Opening...');
  setTimeout(() => {
    try {
      const data = JSON.parse(fs.readFileSync(fp, 'utf8'));
      loadProjectData(data, fp);
      hideLoading();
      toast('Opened');
    } catch (e) {
      hideLoading();
      toast('Could not open');
    }
  }, 30);
}

function loadProjectData(data, fp) {
  stopViewer();
  sessionCacheClear();
  const next = freshState();
  next.projectPath = fp;
  next.projectName = nodePath.basename(fp, '.refboard');
  next.modified = false;

  if (data.version === APP_VERSION && data.type === APP_TYPE) {
    next.questionTemplates = Array.isArray(data.questionTemplates) && data.questionTemplates.length
      ? data.questionTemplates
      : defaultQuestionTemplates();
    next.games = Array.isArray(data.games) ? data.games.map(ensureGameShape) : [];
    next.media = Array.isArray(data.media) ? data.media : [];
  } else {
    const migrated = migrateV1ToV2(data, next.projectName);
    next.questionTemplates = migrated.questionTemplates;
    next.games = migrated.games.map(ensureGameShape);
    next.media = migrated.media;
  }

  next.view = 'library';
  next.activeGameId = null;
  next.activeTab = 'questions';
  next.activeMediaId = null;
  S = next;
  renderApp();
}

function migrateV1ToV2(data, projectName) {
  const gameId = 'g_' + uid();
  const game = ensureGameShape({
    id: gameId,
    title: projectName || 'Imported RefBoard',
    genre: '',
    status: 'imported',
    link: '',
    coverMediaId: null,
    answers: {},
    notes: { blocks: [] },
    collapsedQuestions: [],
    createdAt: now(),
    updatedAt: now(),
  });
  const media = [];
  const folders = Array.isArray(data.folders) ? data.folders : [];
  folders.forEach(folder => {
    (folder.pages || []).forEach(page => {
      if (page.comments) {
        game.notes.blocks.push({
          id: uid(),
          type: 'text',
          text: `# ${folder.name || 'Folder'} / ${page.name || 'Page'}\n\n${page.comments}`,
        });
      }
      (page.media || []).forEach(old => {
        const type = old.type || inferMediaType(old.path || '');
        const id = 'm_' + uid();
        media.push({
          id,
          gameId,
          kind: type === 'video' || type === 'gif' ? 'video' : 'photo',
          type,
          name: old.name || nodePath.basename(old.path || 'Media', nodePath.extname(old.path || '')),
          path: old.path,
          originalPath: old.path,
          description: old.description || '',
          tags: [],
          copied: false,
          createdAt: now(),
          updatedAt: now(),
        });
        if (!game.coverMediaId) game.coverMediaId = id;
      });
    });
  });
  return { questionTemplates: defaultQuestionTemplates(), games: [game], media };
}

function saveProject() {
  if (!S.projectPath) {
    saveAsProject();
    return;
  }
  doSave(S.projectPath);
}

async function saveAsProject() {
  const result = await ipcRenderer.invoke('dialog:save', {
    title: 'Save library',
    defaultPath: S.projectName + '.refboard',
    filters: [{ name: 'RefBoard', extensions: ['refboard'] }],
  });
  if (result.canceled || !result.filePath) return;
  doSave(result.filePath);
}

function doSave(fp) {
  try {
    S.projectPath = fp;
    S.projectName = nodePath.basename(fp, '.refboard');
    ensureAllMediaCopied();
    fs.writeFileSync(fp, JSON.stringify(serializeProject(), null, 2), 'utf8');
    S.modified = false;
    updateChrome();
    toast('Saved');
  } catch (e) {
    toast('Could not save');
  }
}

function stopViewer() {
  stopGif();
  const vid = $('vid-viewer');
  if (vid) {
    vid.pause();
    vid.removeAttribute('src');
    try { vid.load(); } catch (e) {}
  }
  evictActiveGif();
  hidePlayback();
  V.currentMediaId = null;
  V.currentMediaType = null;
}

function clearViewer() {
  stopGif();
  const empty = $('viewer-empty');
  const stage = $('viewer-stage');
  const img = $('img-viewer');
  const vid = $('vid-viewer');
  const canvas = $('gif-canvas');
  if (empty) empty.classList.remove('hidden');
  if (stage) stage.classList.add('hidden');
  if (img) {
    img.classList.add('hidden');
    img.removeAttribute('src');
  }
  if (vid) {
    vid.pause();
    vid.classList.add('hidden');
    vid.removeAttribute('src');
    try { vid.load(); } catch (e) {}
  }
  if (canvas) {
    canvas.classList.add('hidden');
    canvas.width = 0;
    canvas.height = 0;
  }
  V.currentMediaId = null;
  V.currentMediaType = null;
}

function loadMedia(item) {
  const fp = resolveMediaPath(item);
  if (!fp || !fs.existsSync(fp)) {
    toast('File missing');
    clearViewer();
    renderInfo(item);
    return;
  }

  stopGif();
  V.currentMediaId = item.id;
  V.currentMediaType = item.type;
  V.zoom = 1;
  V.panX = 0;
  V.panY = 0;
  updateZoomDisplay();

  $('viewer-empty')?.classList.add('hidden');
  $('viewer-stage')?.classList.remove('hidden');
  $('gif-canvas')?.classList.add('hidden');
  $('img-viewer')?.classList.add('hidden');
  $('vid-viewer')?.classList.add('hidden');

  const url = fileUrl(fp);
  if (item.type === 'video') {
    const vid = $('vid-viewer');
    vid.classList.remove('hidden');
    vid.src = url;
    vid.volume = Number($('vol-slider').value || 100) / 100;
    vid.playbackRate = V.speed;
    vid.play().catch(() => {});
    showPlayback();
    updateModeUI();
    updatePlayIcon();
  } else if (item.type === 'gif') {
    showPlayback();
    updateModeUI();
    if (V.frameMode === 'framebyframe') loadGif(fp, url);
    else showNativeGif(url);
  } else {
    const img = $('img-viewer');
    img.classList.remove('hidden');
    img.src = url;
    img.onload = fitToScreen;
    hidePlayback();
    setFrameDisplay('Photo');
  }
  renderInfo(item);
}

function bindViewerEvents(kind) {
  const wrap = $('viewer-wrap');
  const stage = $('viewer-stage');
  const vid = $('vid-viewer');
  if (!wrap || !stage) return;

  wrap.addEventListener('dragover', e => {
    e.preventDefault();
    wrap.classList.add('drag-over');
  });
  wrap.addEventListener('dragleave', () => wrap.classList.remove('drag-over'));
  wrap.addEventListener('drop', e => {
    e.preventDefault();
    wrap.classList.remove('drag-over');
    addDroppedFiles(e.dataTransfer.files, kind);
  });
  wrap.addEventListener('wheel', e => {
    e.preventDefault();
    changeZoom(e.deltaY < 0 ? 0.12 : -0.12);
  }, { passive: false });

  stage.addEventListener('mousedown', e => {
    if (e.button !== 0) return;
    V.panning = true;
    V.px = e.clientX;
    V.py = e.clientY;
  });

  $('z-in').onclick = () => changeZoom(0.25);
  $('z-out').onclick = () => changeZoom(-0.25);
  $('z-fit').onclick = fitToScreen;

  vid.addEventListener('timeupdate', () => {
    if (!V.tlDragging) setTimeline(vid.currentTime * 1000, vid.duration * 1000);
    if (V.frameMode === 'framebyframe') setFrameDisplay(`Frame ~${Math.floor(vid.currentTime * 30)} @ 30fps`);
  });
  vid.addEventListener('loadedmetadata', () => {
    setTimeline(0, vid.duration * 1000);
    fitToScreen();
  });
  vid.addEventListener('play', updatePlayIcon);
  vid.addEventListener('pause', updatePlayIcon);
}

document.addEventListener('mousemove', e => {
  if (!V.panning) return;
  V.panX += e.clientX - V.px;
  V.panY += e.clientY - V.py;
  V.px = e.clientX;
  V.py = e.clientY;
  applyXform(activeEl());
});

document.addEventListener('mouseup', () => {
  V.panning = false;
});

function activeEl() {
  const canvas = $('gif-canvas');
  const img = $('img-viewer');
  const vid = $('vid-viewer');
  if (canvas && !canvas.classList.contains('hidden')) return canvas;
  if (img && !img.classList.contains('hidden')) return img;
  return vid;
}

function applyXform(el) {
  if (!el) return;
  el.style.transform = `translate(${V.panX}px, ${V.panY}px) scale(${V.zoom})`;
}

function updateZoomDisplay() {
  const z = $('zoom-pct');
  if (z) z.textContent = Math.round(V.zoom * 100) + '%';
}

function changeZoom(delta) {
  V.zoom = Math.max(0.1, Math.min(10, V.zoom + delta));
  updateZoomDisplay();
  applyXform(activeEl());
}

function fitToScreen() {
  const el = activeEl();
  const wrap = $('viewer-wrap');
  if (!el || !wrap) return;
  const w = el.naturalWidth || el.videoWidth || el.width;
  const h = el.naturalHeight || el.videoHeight || el.height;
  if (!w || !h) return;
  const maxW = wrap.clientWidth * 0.9;
  const maxH = wrap.clientHeight * 0.84;
  V.zoom = Math.min(maxW / w, maxH / h, 1);
  V.panX = 0;
  V.panY = 0;
  updateZoomDisplay();
  applyXform(el);
}

function showPlayback() {
  $('playback-bar').classList.remove('hidden');
}

function hidePlayback() {
  $('playback-bar').classList.add('hidden');
}

function setFrameDisplay(value) {
  $('frame-display').textContent = value;
}

function setTimeline(curMs, totalMs) {
  const pct = totalMs > 0 ? Math.max(0, Math.min(100, (curMs / totalMs) * 100)) : 0;
  $('tl-fill').style.width = pct + '%';
  $('tl-thumb').style.left = pct + '%';
  $('t-current').textContent = fmtTime(curMs);
  $('t-total').textContent = fmtTime(totalMs);
}

function fmtTime(ms) {
  const sec = Math.floor((ms || 0) / 1000);
  const min = Math.floor(sec / 60);
  return `${min}:${String(sec % 60).padStart(2, '0')}`;
}

function updatePlayIcon() {
  const vid = $('vid-viewer');
  const playing = (vid && !vid.classList.contains('hidden') && !vid.paused) || V.gifPlaying;
  $('pb-play').textContent = playing ? 'Pause' : 'Play';
}

function updateModeUI() {
  const btn = $('btn-mode');
  btn.textContent = V.frameMode === 'framebyframe' ? 'Frames' : 'Player';
  btn.classList.toggle('fbf', V.frameMode === 'framebyframe');
}

function toggleMode() {
  const item = getMediaById(V.currentMediaId || S.activeMediaId);
  if (!item || (item.type !== 'gif' && item.type !== 'video')) return;
  V.frameMode = V.frameMode === 'playback' ? 'framebyframe' : 'playback';
  updateModeUI();
  loadMedia(item);
}

function evictActiveGif() {
  if (!activeGifCache) return;
  if (activeGifCache.rendered) {
    activeGifCache.rendered.forEach(c => {
      c.width = 0;
      c.height = 0;
    });
  }
  activeGifCache = null;
}

function preRenderGifFrames(frames, w, h) {
  const rendered = [];
  const comp = document.createElement('canvas');
  comp.width = w;
  comp.height = h;
  const compCtx = comp.getContext('2d');
  const prev = document.createElement('canvas');
  prev.width = w;
  prev.height = h;
  const prevCtx = prev.getContext('2d');
  const patch = document.createElement('canvas');
  const patchCtx = patch.getContext('2d');

  frames.forEach(frame => {
    if (frame.disposalType === 3) {
      prevCtx.clearRect(0, 0, w, h);
      prevCtx.drawImage(comp, 0, 0);
    }
    if (patch.width !== frame.dims.width || patch.height !== frame.dims.height) {
      patch.width = frame.dims.width;
      patch.height = frame.dims.height;
    }
    patchCtx.putImageData(new ImageData(new Uint8ClampedArray(frame.patch), frame.dims.width, frame.dims.height), 0, 0);
    compCtx.drawImage(patch, frame.dims.left, frame.dims.top);

    const fc = document.createElement('canvas');
    fc.width = w;
    fc.height = h;
    fc.getContext('2d').drawImage(comp, 0, 0);
    rendered.push(fc);

    if (frame.disposalType === 2) compCtx.clearRect(frame.dims.left, frame.dims.top, frame.dims.width, frame.dims.height);
    else if (frame.disposalType === 3) {
      compCtx.clearRect(0, 0, w, h);
      compCtx.drawImage(prev, 0, 0);
    }
  });

  comp.width = prev.width = patch.width = 0;
  comp.height = prev.height = patch.height = 0;
  return rendered;
}

function loadGif(fp, url) {
  if (!parseGIF || !decompressFrames) {
    showNativeGif(url);
    toast('GIF frame module missing');
    return;
  }
  if (activeGifCache && activeGifCache.fp === fp) {
    useGifFrames(activeGifCache.frames, activeGifCache.rendered, activeGifCache.w, activeGifCache.h);
    return;
  }

  evictActiveGif();
  showLoading('GIF...');
  setTimeout(() => {
    try {
      const buf = fs.readFileSync(fp);
      const ab = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);
      const gif = parseGIF(ab);
      const frames = decompressFrames(gif, true);
      if (!frames.length) throw new Error('No frames');
      const w = gif.lsd.width;
      const h = gif.lsd.height;
      const rendered = preRenderGifFrames(frames, w, h);
      sessionCacheWrite(fp, { w, h, count: frames.length, delays: frames.map(f => f.delay || 100) });
      activeGifCache = { fp, frames, rendered, w, h };
      hideLoading();
      useGifFrames(frames, rendered, w, h);
    } catch (e) {
      hideLoading();
      showNativeGif(url);
      toast('GIF frame mode failed');
    }
  }, 30);
}

function showNativeGif(url) {
  const img = $('img-viewer');
  $('gif-canvas').classList.add('hidden');
  img.classList.remove('hidden');
  img.src = url;
  img.onload = fitToScreen;
  V.gifFrames = null;
  V.gifRenderedFrames = null;
  setFrameDisplay('GIF');
  setTimeline(0, 0);
}

function useGifFrames(frames, rendered, w, h) {
  V.gifFrames = frames;
  V.gifRenderedFrames = rendered;
  V.gifIdx = 0;
  V.gifTotalDuration = frames.reduce((sum, frame) => sum + (frame.delay || 100), 0);
  const canvas = $('gif-canvas');
  canvas.width = w;
  canvas.height = h;
  canvas.classList.remove('hidden');
  $('img-viewer').classList.add('hidden');
  drawGifFrame(0);
  fitToScreen();
  updateFrameDisplay();
}

function drawGifFrame(idx) {
  const canvas = $('gif-canvas');
  if (!canvas || !V.gifRenderedFrames || idx >= V.gifRenderedFrames.length) return;
  const ctx = canvas.getContext('2d');
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.drawImage(V.gifRenderedFrames[idx], 0, 0);
}

function stopGif() {
  V.gifPlaying = false;
  if (V.gifTimer) {
    clearTimeout(V.gifTimer);
    V.gifTimer = null;
  }
  updatePlayIcon();
}

function playGif() {
  if (!V.gifFrames || V.frameMode !== 'framebyframe') return;
  V.gifPlaying = true;
  updatePlayIcon();
  const tick = () => {
    if (!V.gifPlaying || !V.gifFrames) return;
    V.gifTimer = setTimeout(() => {
      V.gifIdx = (V.gifIdx + 1) % V.gifFrames.length;
      drawGifFrame(V.gifIdx);
      updateFrameDisplay();
      tick();
    }, (V.gifFrames[V.gifIdx].delay || 100) / V.speed);
  };
  tick();
}

function updateFrameDisplay() {
  if (!V.gifFrames) return;
  setFrameDisplay(`Frame ${V.gifIdx + 1} / ${V.gifFrames.length}`);
  let elapsed = 0;
  for (let i = 0; i < V.gifIdx; i++) elapsed += V.gifFrames[i].delay || 100;
  setTimeline(elapsed, V.gifTotalDuration);
}

function initControls() {
  document.querySelectorAll('.nav-btn').forEach(btn => {
    btn.onclick = () => setView(btn.dataset.view);
  });
  $('quick-new-game').onclick = createGameFlow;

  $('btn-new').onclick = newProject;
  $('btn-open').onclick = openProject;
  $('btn-save').onclick = saveProject;
  $('btn-saveas').onclick = saveAsProject;
  $('btn-min').onclick = () => ipcRenderer.invoke('win:minimize');
  $('btn-max').onclick = () => ipcRenderer.invoke('win:maximize');
  $('btn-close').onclick = () => {
    if (S.modified && !confirm('Discard unsaved changes?')) return;
    ipcRenderer.invoke('win:close');
  };

  $('modal-cancel').onclick = closeModal;
  $('modal-ok').onclick = () => {
    const value = $('modal-inp').value.trim();
    if (!value) return;
    const cb = modalCb;
    closeModal();
    if (cb) cb(value);
  };
  $('modal-inp').addEventListener('keydown', e => {
    if (e.key === 'Enter') $('modal-ok').click();
    if (e.key === 'Escape') closeModal();
  });

  $('pb-play').onclick = () => {
    const vid = $('vid-viewer');
    if (vid && !vid.classList.contains('hidden')) {
      if (vid.paused) vid.play().catch(() => {});
      else vid.pause();
      updatePlayIcon();
    } else if (V.gifFrames && V.frameMode === 'framebyframe') {
      V.gifPlaying ? stopGif() : playGif();
    }
  };
  $('pb-prev').onclick = () => stepPlayback(-1);
  $('pb-next').onclick = () => stepPlayback(1);
  $('btn-mode').onclick = toggleMode;
  $('vol-slider').oninput = () => {
    const vid = $('vid-viewer');
    if (vid) vid.volume = Number($('vol-slider').value || 100) / 100;
  };
  $('btn-mute').onclick = () => {
    const vid = $('vid-viewer');
    if (!vid) return;
    vid.muted = !vid.muted;
    $('btn-mute').textContent = vid.muted ? 'Muted' : 'Sound';
  };
  document.querySelectorAll('.spd').forEach(btn => {
    btn.onclick = () => {
      document.querySelectorAll('.spd').forEach(b => b.classList.remove('active'));
      btn.classList.add('active');
      V.speed = Number(btn.dataset.v);
      const vid = $('vid-viewer');
      if (vid) vid.playbackRate = V.speed;
    };
  });

  const tlTrack = $('timeline-track');
  tlTrack.addEventListener('mousedown', e => {
    V.tlDragging = true;
    seekToMouse(e);
    document.addEventListener('mousemove', onTlMove);
    document.addEventListener('mouseup', onTlUp);
  });

  document.addEventListener('keydown', e => {
    if (['INPUT', 'TEXTAREA'].includes(e.target.tagName)) return;
    const k = e.key.toLowerCase();
    if (k === ' ') {
      e.preventDefault();
      $('pb-play').click();
    }
    if (k === 'arrowleft') {
      e.preventDefault();
      $('pb-prev').click();
    }
    if (k === 'arrowright') {
      e.preventDefault();
      $('pb-next').click();
    }
    if (k === 'f') fitToScreen();
    if (k === 'm') toggleMode();
    if (e.ctrlKey || e.metaKey) {
      if (k === 'n') {
        e.preventDefault();
        newProject();
      }
      if (k === 'o') {
        e.preventDefault();
        openProject();
      }
      if (k === 's') {
        e.preventDefault();
        e.shiftKey ? saveAsProject() : saveProject();
      }
    }
  });
}

function stepPlayback(dir) {
  const vid = $('vid-viewer');
  if (vid && !vid.classList.contains('hidden') && vid.duration) {
    const step = V.frameMode === 'framebyframe' ? 1 / 30 : 1;
    vid.currentTime = Math.max(0, Math.min(vid.duration, vid.currentTime + dir * step));
    return;
  }
  if (V.gifFrames && V.frameMode === 'framebyframe') {
    V.gifIdx = (V.gifIdx + dir + V.gifFrames.length) % V.gifFrames.length;
    drawGifFrame(V.gifIdx);
    updateFrameDisplay();
  }
}

function onTlMove(e) {
  if (V.tlDragging) seekToMouse(e);
}

function onTlUp() {
  V.tlDragging = false;
  document.removeEventListener('mousemove', onTlMove);
  document.removeEventListener('mouseup', onTlUp);
}

function seekToMouse(e) {
  const track = $('timeline-track');
  const rect = track.getBoundingClientRect();
  const pct = Math.max(0, Math.min(1, (e.clientX - rect.left) / rect.width));
  const vid = $('vid-viewer');
  if (vid && !vid.classList.contains('hidden') && vid.duration) {
    vid.currentTime = pct * vid.duration;
  } else if (V.gifFrames && V.frameMode === 'framebyframe') {
    V.gifIdx = Math.max(0, Math.min(V.gifFrames.length - 1, Math.floor(pct * V.gifFrames.length)));
    drawGifFrame(V.gifIdx);
    updateFrameDisplay();
  }
}

function formatShortDate(value) {
  if (!value) return 'today';
  try {
    return new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric' }).format(new Date(value));
  } catch (e) {
    return 'recently';
  }
}

initControls();
renderApp();
