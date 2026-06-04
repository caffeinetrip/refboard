'use strict';

const { ipcRenderer, clipboard } = require('electron');
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

const APP_VERSION = 6;
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

const IMPORTANCE_LEVELS = [
  { id: 'common', label: 'Common', short: 'C' },
  { id: 'noted', label: 'Noted', short: 'N' },
  { id: 'rare', label: 'Rare', short: 'R' },
  { id: 'important', label: 'Important', short: 'I' },
  { id: 'critical', label: 'Critical', short: '!' },
];

const KANBAN_COLUMNS = [
  ['ideas', 'Ideas'],
  ['todo', 'Todo'],
  ['doing', 'Doing'],
  ['done', 'Done'],
];

function freshState() {
  return {
    projectPath: null,
    projectName: 'Untitled',
    modified: false,
    view: 'library',
    activeGameId: null,
    activeTab: 'questions',
    activeMediaId: null,
    activeDailyNoteId: null,
    activePhotoBoardId: null,
    activeProjectId: null,
    activeProjectTab: 'doc',
    activeMilestoneId: null,
    activeKanbanBoardId: null,
    gameSearch: '',
    dailySearch: '',
    photoSearch: '',
    projectSearch: '',
    dailyNotes: [],
    photoBoards: [],
    projects: [],
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
let importanceMenuCloseHandler = null;
let milestoneMenuCloseHandler = null;
let categoryMenuCloseHandler = null;
let lastScrollState = [];
let scrollRestoreTimer = null;
let navStack = [];
let restoringRoute = false;

function getActiveGame() {
  return S.games.find(g => g.id === S.activeGameId) || null;
}

function getMediaById(id) {
  const media = S.media.find(m => m.id === id) || null;
  return media ? ensureMediaShape(media) : null;
}

function getGameMedia(gameId, kind) {
  return S.media
    .map(ensureMediaShape)
    .filter(m => m.gameId === gameId && (!kind || m.kind === kind) && m.scope === 'game')
    .sort((a, b) => (a.order ?? 0) - (b.order ?? 0) || String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
}

function getActiveDailyNote() {
  return S.dailyNotes.find(note => note.id === S.activeDailyNoteId) || null;
}

function getActivePhotoBoard() {
  return S.photoBoards.find(board => board.id === S.activePhotoBoardId) || null;
}

function getActiveProject() {
  return S.projects.find(project => project.id === S.activeProjectId) || null;
}

function getActiveMilestone(project) {
  if (!project) return null;
  return project.milestones.find(milestone => milestone.id === S.activeMilestoneId) || project.milestones[0] || null;
}

function getActiveKanbanBoard(milestone) {
  if (!milestone) return null;
  return milestone.boards.find(board => board.id === S.activeKanbanBoardId) || milestone.boards[0] || null;
}

function todayISO() {
  return new Date().toISOString().slice(0, 10);
}

function formatDateTitle(value) {
  if (!value) return 'No date';
  try {
    return new Intl.DateTimeFormat('en-US', { month: 'short', day: 'numeric', year: 'numeric' }).format(new Date(value + 'T00:00:00'));
  } catch (e) {
    return value;
  }
}

function searchMatches(parts, query) {
  const q = String(query || '').trim().toLowerCase();
  if (!q) return true;
  return parts.some(part => String(part || '').toLowerCase().includes(q));
}

function importanceLevel(value) {
  return IMPORTANCE_LEVELS.find(level => level.id === value) || IMPORTANCE_LEVELS[0];
}

function importanceRank(value) {
  return IMPORTANCE_LEVELS.findIndex(level => level.id === importanceLevel(value).id);
}

function sortByImportance(items) {
  items.sort((a, b) => importanceRank(b.importance) - importanceRank(a.importance) || String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')));
}

const SCROLL_KEEP_SELECTORS = [
  '.screen-scroll',
  '.tab-scroll',
  '.day-scroll',
  '.album-scroll',
  '.media-list',
  '.project-media-grid',
  '.masonry-grid',
  '.kanban-columns',
  '.task-list',
];

function scrollKeyFor(el, selector, index) {
  return el.id ? `#${el.id}` : `${selector}:${index}`;
}

function captureScrollState() {
  const seen = new Set();
  const state = [];
  SCROLL_KEEP_SELECTORS.forEach(selector => {
    document.querySelectorAll(selector).forEach((el, index) => {
      if (seen.has(el)) return;
      seen.add(el);
      state.push({
        key: scrollKeyFor(el, selector, index),
        top: el.scrollTop,
        left: el.scrollLeft,
      });
    });
  });
  return state;
}

function restoreScrollState(state) {
  if (!Array.isArray(state) || !state.length) return;
  SCROLL_KEEP_SELECTORS.forEach(selector => {
    document.querySelectorAll(selector).forEach((el, index) => {
      const key = scrollKeyFor(el, selector, index);
      const saved = state.find(item => item.key === key);
      if (!saved) return;
      el.scrollTop = saved.top;
      el.scrollLeft = saved.left;
    });
  });
}

function rememberScrollState() {
  lastScrollState = captureScrollState();
}

function scheduleScrollRestore() {
  const state = lastScrollState.length ? lastScrollState : captureScrollState();
  if (scrollRestoreTimer) cancelAnimationFrame(scrollRestoreTimer);
  scrollRestoreTimer = requestAnimationFrame(() => {
    scrollRestoreTimer = requestAnimationFrame(() => {
      restoreScrollState(state);
      scrollRestoreTimer = null;
    });
  });
}

function importanceOptions(value) {
  const active = importanceLevel(value).id;
  return IMPORTANCE_LEVELS
    .map(level => `<option value="${esc(level.id)}" ${level.id === active ? 'selected' : ''}>${esc(level.label)}</option>`)
    .join('');
}

function importanceBadgeHTML(value) {
  const level = importanceLevel(value);
  return `<button type="button" class="rarity-badge rarity-${esc(level.id)}" title="Importance: ${esc(level.label)}">${esc(level.short)}</button>`;
}

function importanceMenuButtonHTML(value) {
  const level = importanceLevel(value);
  return `<button class="kebab-btn" title="Importance: ${esc(level.label)}">...</button>`;
}

function bindImportanceTriggers(root, value, onPick) {
  if (!root) return;
  root.querySelectorAll('.rarity-badge, .kebab-btn').forEach(btn => {
    btn.onclick = e => {
      e.stopPropagation();
      openImportanceMenu(e.currentTarget, typeof value === 'function' ? value() : value, onPick);
    };
  });
}

function hasDragType(e, type) {
  return Array.from(e.dataTransfer?.types || []).includes(type);
}

function hasMoveDragType(e, type) {
  return hasDragType(e, type) || hasDragType(e, 'text/plain');
}

function getDraggedId(e, type) {
  return e.dataTransfer?.getData(type) || e.dataTransfer?.getData('text/plain') || '';
}

function openImportanceMenu(anchor, value, onPick) {
  closeImportanceMenu();
  closeCategoryMenu();
  closeMilestoneMenu();
  const menu = document.createElement('div');
  menu.id = 'importance-menu';
  menu.className = 'importance-menu';
  menu.innerHTML = IMPORTANCE_LEVELS.map(level => `
    <button class="importance-choice ${level.id === importanceLevel(value).id ? 'active' : ''}" data-importance="${esc(level.id)}">
      ${importanceBadgeHTML(level.id)}
      <span>${esc(level.label)}</span>
    </button>`).join('');
  document.body.appendChild(menu);
  const rect = anchor.getBoundingClientRect();
  menu.style.top = Math.min(window.innerHeight - menu.offsetHeight - 8, rect.bottom + 6) + 'px';
  menu.style.left = Math.max(8, Math.min(window.innerWidth - menu.offsetWidth - 8, rect.right - menu.offsetWidth)) + 'px';
  menu.querySelectorAll('[data-importance]').forEach(btn => {
    btn.onclick = e => {
      e.stopPropagation();
      onPick(btn.dataset.importance);
      closeImportanceMenu();
    };
  });
  importanceMenuCloseHandler = e => {
    if (menu.contains(e.target) || anchor.contains(e.target)) return;
    closeImportanceMenu();
  };
  setTimeout(() => document.addEventListener('mousedown', importanceMenuCloseHandler), 0);
}

function closeImportanceMenu() {
  if (importanceMenuCloseHandler) {
    document.removeEventListener('mousedown', importanceMenuCloseHandler);
    importanceMenuCloseHandler = null;
  }
  const menu = $('importance-menu');
  if (menu) menu.remove();
}

function openMilestoneMenu(anchor, project) {
  closeMilestoneMenu();
  closeImportanceMenu();
  closeCategoryMenu();
  const current = getActiveMilestone(project);
  const menu = document.createElement('div');
  menu.id = 'milestone-menu';
  menu.className = 'milestone-menu';
  menu.innerHTML = project.milestones.map(milestone => `
    <button class="milestone-choice ${milestone.id === current?.id ? 'active' : ''}" data-milestone="${esc(milestone.id)}">
      <span>${esc(milestone.title)}</span>
      <small>${milestoneStats(milestone).pct}%</small>
    </button>`).join('');
  document.body.appendChild(menu);
  const rect = anchor.getBoundingClientRect();
  menu.style.top = rect.bottom + 6 + 'px';
  menu.style.left = Math.max(8, Math.min(window.innerWidth - menu.offsetWidth - 8, rect.left)) + 'px';
  menu.querySelectorAll('[data-milestone]').forEach(btn => {
    btn.onclick = e => {
      e.stopPropagation();
      const next = project.milestones.find(item => item.id === btn.dataset.milestone);
      if (!next) return;
      S.activeMilestoneId = next.id;
      project.activeMilestoneId = next.id;
      S.activeKanbanBoardId = next.activeBoardId || next.boards[0]?.id || null;
      touchProject(project);
      markDirty();
      closeMilestoneMenu();
      renderProjectWorkspace(project);
    };
  });
  milestoneMenuCloseHandler = e => {
    if (menu.contains(e.target) || anchor.contains(e.target)) return;
    closeMilestoneMenu();
  };
  setTimeout(() => document.addEventListener('mousedown', milestoneMenuCloseHandler), 0);
}

function closeMilestoneMenu() {
  if (milestoneMenuCloseHandler) {
    document.removeEventListener('mousedown', milestoneMenuCloseHandler);
    milestoneMenuCloseHandler = null;
  }
  const menu = $('milestone-menu');
  if (menu) menu.remove();
}

function openCategoryMenu(anchor, categories, activeId, onPick, options = {}) {
  closeCategoryMenu();
  closeImportanceMenu();
  closeMilestoneMenu();
  const menu = document.createElement('div');
  menu.id = 'category-menu';
  menu.className = 'category-menu';
  const title = options.title || 'Categories';
  menu.innerHTML = `
    <div class="category-menu-title">${esc(title)}</div>
    ${categories.map(category => `
      <button class="category-choice ${sameId(category.id, activeId) ? 'active' : ''}" data-category="${esc(category.id)}">
        <span>${esc(category.title)}</span>
        ${typeof options.countFor === 'function' ? `<small>${options.countFor(category)}</small>` : ''}
      </button>`).join('')}`;
  document.body.appendChild(menu);
  const rect = anchor.getBoundingClientRect();
  menu.style.top = Math.min(window.innerHeight - menu.offsetHeight - 8, rect.bottom + 6) + 'px';
  menu.style.left = Math.max(8, Math.min(window.innerWidth - menu.offsetWidth - 8, rect.left)) + 'px';
  menu.querySelectorAll('[data-category]').forEach(btn => {
    btn.onclick = e => {
      e.stopPropagation();
      const category = categories.find(item => sameId(item.id, btn.dataset.category));
      if (category) onPick(category);
      closeCategoryMenu();
    };
  });
  categoryMenuCloseHandler = e => {
    if (menu.contains(e.target) || anchor.contains(e.target)) return;
    closeCategoryMenu();
  };
  setTimeout(() => document.addEventListener('mousedown', categoryMenuCloseHandler), 0);
}

function closeCategoryMenu() {
  if (categoryMenuCloseHandler) {
    document.removeEventListener('mousedown', categoryMenuCloseHandler);
    categoryMenuCloseHandler = null;
  }
  const menu = $('category-menu');
  if (menu) menu.remove();
}

function createTextBlock(text = '') {
  return {
    id: uid(),
    type: 'text',
    title: 'Text',
    text,
    importance: 'common',
    height: 180,
    categoryId: 'blockcat_default',
    createdAt: now(),
    updatedAt: now(),
  };
}

function sameId(a, b) {
  return String(a ?? '') === String(b ?? '');
}

function ensureBlockShape(block) {
  block.id = String(block.id ?? uid());
  block.type ??= 'text';
  block.title ??= block.type === 'text' ? 'Text' : '';
  block.text ??= '';
  block.caption ??= '';
  block.importance = importanceLevel(block.importance).id;
  block.categoryId = String(block.categoryId ?? 'blockcat_default');
  block.height = Math.max(120, Math.min(900, Number(block.height || (block.type === 'media' ? 270 : 180))));
  block.createdAt ??= now();
  block.updatedAt ??= now();
  return block;
}

function ensureDailyNoteShape(note) {
  note.id ??= 'dn_' + uid();
  note.date ??= todayISO();
  note.title ??= formatDateTitle(note.date);
  note.importance = importanceLevel(note.importance).id;
  ensureBlockContainerShape(note);
  note.createdAt ??= now();
  note.updatedAt ??= now();
  return note;
}

function ensurePhotoBoardShape(board) {
  board.id ??= 'pb_' + uid();
  board.title ??= 'Board';
  board.description ??= '';
  board.photoIds ??= [];
  board.photoIds = Array.isArray(board.photoIds) ? board.photoIds : [];
  board.createdAt ??= now();
  board.updatedAt ??= now();
  return board;
}

function createKanbanBoard(title = 'Ideas') {
  return {
    id: 'kb_' + uid(),
    title,
    columns: {
      ideas: [],
      todo: [],
      doing: [],
      done: [],
    },
    createdAt: now(),
    updatedAt: now(),
  };
}

function createMilestone(title = 'Milestone 1') {
  const board = createKanbanBoard('Ideas');
  return {
    id: 'ms_' + uid(),
    title,
    notes: '',
    boards: [board],
    activeBoardId: board.id,
    createdAt: now(),
    updatedAt: now(),
  };
}

function ensureTaskShape(task) {
  task.id ??= 'task_' + uid();
  task.title ??= 'Task';
  task.notes ??= '';
  task.importance = importanceLevel(task.importance).id;
  task.mediaIds ??= [];
  task.mediaIds = Array.isArray(task.mediaIds) ? task.mediaIds : [];
  task.createdAt ??= now();
  task.updatedAt ??= now();
  return task;
}

function ensureKanbanBoardShape(board) {
  board.id ??= 'kb_' + uid();
  board.title ??= 'Board';
  board.columns ??= {};
  KANBAN_COLUMNS.forEach(([key]) => {
    board.columns[key] = Array.isArray(board.columns[key]) ? board.columns[key].map(ensureTaskShape) : [];
  });
  board.createdAt ??= now();
  board.updatedAt ??= now();
  return board;
}

function ensureMilestoneShape(milestone) {
  milestone.id ??= 'ms_' + uid();
  milestone.title ??= 'Milestone';
  milestone.notes ??= '';
  milestone.celebratedAt ??= null;
  milestone.boards = Array.isArray(milestone.boards) && milestone.boards.length
    ? milestone.boards.map(ensureKanbanBoardShape)
    : [createKanbanBoard('Ideas')];
  milestone.activeBoardId ??= milestone.boards[0]?.id || null;
  milestone.createdAt ??= now();
  milestone.updatedAt ??= now();
  return milestone;
}

function ensureProjectShape(project) {
  project.id ??= 'pr_' + uid();
  project.title ??= 'Project';
  project.description ??= '';
  project.doc ??= { blocks: [] };
  project.doc = ensureBlockContainerShape(project.doc);
  project.notes = ensureBlockContainerShape(project.notes);
  ensureMediaCategoryBucket(project, 'photo');
  ensureMediaCategoryBucket(project, 'video');
  ensureMediaCategoryBucket(project, 'sound');
  project.milestones = Array.isArray(project.milestones) && project.milestones.length
    ? project.milestones.map(ensureMilestoneShape)
    : [createMilestone('Milestone 1')];
  project.activeMilestoneId ??= project.milestones[0]?.id || null;
  project.createdAt ??= now();
  project.updatedAt ??= now();
  return project;
}

function defaultBlockCategory() {
  return { id: 'blockcat_default', title: 'Main', createdAt: now(), updatedAt: now() };
}

function ensureBlockCategoryShape(category, fallback = 'Main') {
  category.id = String(category.id ?? 'blockcat_' + uid());
  category.title ??= fallback;
  category.createdAt ??= now();
  category.updatedAt ??= now();
  return category;
}

function blockMatchesCategory(block, categoryId) {
  return sameId(ensureBlockShape(block).categoryId, categoryId);
}

function visibleBlocksForCategory(blocks, categoryId) {
  return categoryId
    ? blocks.filter(block => blockMatchesCategory(block, categoryId))
    : blocks.map(ensureBlockShape);
}

function ensureBlockContainerShape(container) {
  if (!container || typeof container !== 'object') container = { blocks: [] };
  if (Array.isArray(container.blocks)) {
    container.blocks.forEach(ensureBlockShape);
  } else {
    container.blocks = [];
  }
  container.categories = Array.isArray(container.categories) && container.categories.length
    ? container.categories.map((category, index) => ensureBlockCategoryShape(category, index ? 'Category' : 'Main'))
    : [defaultBlockCategory()];
  container.activeCategoryId = String(container.activeCategoryId ?? container.categories[0]?.id ?? 'blockcat_default');
  container.blocks.forEach(block => {
    if (!container.categories.some(category => sameId(category.id, block.categoryId))) block.categoryId = container.categories[0].id;
  });
  return container;
}

function getActiveBlockCategory(container) {
  ensureBlockContainerShape(container);
  let category = container.categories.find(item => sameId(item.id, container.activeCategoryId));
  if (!category) {
    category = container.categories[0];
    container.activeCategoryId = category.id;
  }
  return category;
}

function addBlockCategory(container, onDone) {
  askText('New Category', '', 'Create', title => {
    const category = ensureBlockCategoryShape({
      id: 'blockcat_' + uid(),
      title,
      createdAt: now(),
      updatedAt: now(),
    });
    ensureBlockContainerShape(container);
    container.categories.push(category);
    container.activeCategoryId = category.id;
    onDone();
  });
}

function blockCategoryControlsHTML(container, prefix) {
  ensureBlockContainerShape(container);
  const active = getActiveBlockCategory(container);
  const activeCount = container.blocks.filter(block => blockMatchesCategory(block, active.id)).length;
  return `
    <div class="category-controls">
      <button type="button" class="category-menu-btn" id="${esc(prefix)}-category">
        <span>${esc(active.title)}</span>
        <small>${activeCount}</small>
        <span class="select-caret">v</span>
      </button>
      <button class="mini-btn" id="${esc(prefix)}-category-add">+ Category</button>
      <button class="ghost-btn" id="${esc(prefix)}-sort-importance">Sort importance</button>
      <button class="ghost-btn" id="${esc(prefix)}-copy-category">Copy category</button>
      <button class="ghost-btn" id="${esc(prefix)}-copy-all">Copy all</button>
    </div>`;
}

function bindBlockCategoryControls(container, prefix, onChange) {
  ensureBlockContainerShape(container);
  const btn = $(`${prefix}-category`);
  if (btn) {
    btn.onclick = e => {
      openCategoryMenu(e.currentTarget, container.categories, container.activeCategoryId, category => {
        container.activeCategoryId = category.id;
        onChange(true);
      }, {
        title: 'Note categories',
        countFor: category => container.blocks.filter(block => blockMatchesCategory(block, category.id)).length,
      });
    };
  }
  const add = $(`${prefix}-category-add`);
  if (add) add.onclick = () => addBlockCategory(container, () => onChange(true));
  const sort = $(`${prefix}-sort-importance`);
  if (sort) sort.onclick = () => {
    sortBlocksByImportance(container, getActiveBlockCategory(container).id);
    onChange(true);
  };
  const copyCategory = $(`${prefix}-copy-category`);
  if (copyCategory) copyCategory.onclick = () => copyBlockContainerToClipboard(container, getActiveBlockCategory(container).id);
  const copyAll = $(`${prefix}-copy-all`);
  if (copyAll) copyAll.onclick = () => copyBlockContainerToClipboard(container);
}

function mediaCategoryControlsHTML(owner, kind, prefix, scope) {
  const categories = getMediaCategories(owner, kind);
  const active = getActiveMediaCategory(owner, kind);
  const activeCount = mediaCategoryCount(owner.id, scope, kind, active.id);
  return `
    <div class="category-controls media-category-controls">
      <button type="button" class="category-menu-btn" id="${esc(prefix)}-category">
        <span>${esc(active.title)}</span>
        <small>${activeCount}</small>
        <span class="select-caret">v</span>
      </button>
      <button class="mini-btn" id="${esc(prefix)}-category-add">+ Category</button>
    </div>`;
}

function bindMediaCategoryControls(owner, kind, prefix, scope, onChange) {
  getMediaCategories(owner, kind);
  const btn = $(`${prefix}-category`);
  if (btn) {
    btn.onclick = e => {
      openCategoryMenu(e.currentTarget, getMediaCategories(owner, kind), getActiveMediaCategory(owner, kind).id, category => {
        setActiveMediaCategory(owner, kind, category.id);
        onChange(true);
      }, {
        title: `${mediaCategoryLabel(kind)} categories`,
        countFor: category => mediaCategoryCount(owner.id, scope, kind, category.id),
      });
    };
  }
  const add = $(`${prefix}-category-add`);
  if (add) add.onclick = () => createMediaCategoryFlow(owner, kind, () => onChange(true));
}

function createMediaCategoryFlow(owner, kind, onDone) {
  askText(`New ${mediaCategoryLabel(kind)} Category`, '', 'Create', title => {
    const category = ensureImageCategoryShape({
      id: 'imgcat_' + uid(),
      title,
      createdAt: now(),
      updatedAt: now(),
    });
    getMediaCategories(owner, kind).push(category);
    setActiveMediaCategory(owner, kind, category.id);
    onDone();
  });
}

function moveBlockBefore(blocks, draggedId, beforeId, categoryId) {
  if (!categoryId) return moveItemBefore(blocks, draggedId, beforeId);
  const visible = visibleBlocksForCategory(blocks, categoryId);
  if (!moveItemBefore(visible, draggedId, beforeId)) return false;
  let index = 0;
  blocks.splice(0, blocks.length, ...blocks.map(block => blockMatchesCategory(block, categoryId) ? visible[index++] : block));
  return true;
}

function moveBlockByOffset(blocks, blockId, offset, categoryId) {
  const visible = visibleBlocksForCategory(blocks, categoryId);
  const from = visible.findIndex(block => sameId(block.id, blockId));
  const to = from + offset;
  if (from < 0 || to < 0 || to >= visible.length) return false;
  const beforeId = offset < 0 ? visible[to].id : visible[to + 1]?.id || null;
  return categoryId
    ? moveBlockBefore(blocks, blockId, beforeId, categoryId)
    : moveItemBefore(blocks, blockId, beforeId);
}

function sortBlocksByImportance(container, categoryId) {
  ensureBlockContainerShape(container);
  const visible = visibleBlocksForCategory(container.blocks, categoryId);
  sortByImportance(visible);
  let index = 0;
  container.blocks.splice(0, container.blocks.length, ...container.blocks.map(block => blockMatchesCategory(block, categoryId) ? visible[index++] : block));
}

function sortMediaByImportance(items) {
  sortByImportance(items);
  items.forEach((item, index) => {
    item.order = index;
    item.updatedAt = now();
  });
}

function reorderMediaBefore(ownerId, scope, kind, categoryId, draggedId, beforeId) {
  const ordered = S.media
    .map(ensureMediaShape)
    .filter(media => (
      media.gameId === ownerId &&
      media.scope === scope &&
      media.kind === kind &&
      media.categoryId === categoryId
    ))
    .sort((a, b) => (a.order ?? 0) - (b.order ?? 0) || String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
  if (!moveItemBefore(ordered, draggedId, beforeId)) return false;
  ordered.forEach((media, index) => {
    media.order = index;
    media.updatedAt = now();
  });
  return true;
}

function persistBlockHeight(el, block, callbacks) {
  const save = () => {
    const next = Math.round(el.getBoundingClientRect().height);
    if (!next || Math.abs(next - Number(block.height || 0)) < 2) return;
    block.height = Math.max(120, Math.min(900, next));
    block.updatedAt = now();
    callbacks.onChange();
  };
  el.addEventListener('mouseup', save);
  el.addEventListener('blur', save);
}

function getProjectMedia(projectId, kind) {
  return S.media
    .map(ensureMediaShape)
    .filter(media => media.gameId === projectId && media.scope === 'projectMedia' && (!kind || media.kind === kind))
    .sort((a, b) => (a.order ?? 0) - (b.order ?? 0) || String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
}

function getBoardPhotos(board) {
  if (!board) return [];
  return (board.photoIds || [])
    .map(id => getMediaById(id))
    .filter(Boolean);
}

function getMilestoneTasks(milestone) {
  if (!milestone) return [];
  return milestone.boards.flatMap(board => KANBAN_COLUMNS.flatMap(([key]) => board.columns[key] || []));
}

function milestoneStats(milestone) {
  const scoped = milestone.boards.flatMap(board => ['todo', 'doing', 'done'].flatMap(key => board.columns[key] || []));
  const done = milestone.boards.reduce((sum, board) => sum + (board.columns.done || []).length, 0);
  const todo = milestone.boards.reduce((sum, board) => sum + (board.columns.todo || []).length, 0);
  const doing = milestone.boards.reduce((sum, board) => sum + (board.columns.doing || []).length, 0);
  const total = scoped.length;
  const pct = total ? Math.round((done / total) * 100) : 0;
  return {
    total,
    done,
    todo,
    doing,
    pct,
    closed: total > 0 && todo === 0 && doing === 0,
  };
}

function projectStats(project) {
  return (project?.milestones || []).reduce((acc, milestone) => {
    const stats = milestoneStats(milestone);
    acc.total += stats.total;
    acc.done += stats.done;
    return acc;
  }, { total: 0, done: 0 });
}

function touchProject(project) {
  if (project) project.updatedAt = now();
}

function defaultImageCategory() {
  return { id: 'imgcat_default', title: 'Main', createdAt: now(), updatedAt: now() };
}

function ensureImageCategoryShape(category, fallback = 'Main') {
  category.id ??= 'imgcat_' + uid();
  category.title ??= fallback;
  category.createdAt ??= now();
  category.updatedAt ??= now();
  return category;
}

const MEDIA_CATEGORY_FIELDS = {
  photo: ['imageCategories', 'activeImageCategoryId', 'Image'],
  video: ['videoCategories', 'activeVideoCategoryId', 'Video'],
  sound: ['soundCategories', 'activeSoundCategoryId', 'Audio'],
};

function mediaCategoryConfig(kind) {
  return MEDIA_CATEGORY_FIELDS[kind] || MEDIA_CATEGORY_FIELDS.photo;
}

function ensureMediaCategoryBucket(owner, kind) {
  const [listKey, activeKey] = mediaCategoryConfig(kind);
  owner[listKey] = Array.isArray(owner[listKey]) && owner[listKey].length
    ? owner[listKey].map((category, index) => ensureImageCategoryShape(category, index ? 'Category' : 'Main'))
    : [defaultImageCategory()];
  owner[activeKey] ??= owner[listKey][0]?.id || null;
  return owner[listKey];
}

function getMediaCategories(owner, kind) {
  return ensureMediaCategoryBucket(owner, kind);
}

function getActiveMediaCategory(owner, kind) {
  const [listKey, activeKey] = mediaCategoryConfig(kind);
  const categories = getMediaCategories(owner, kind);
  let category = categories.find(item => item.id === owner[activeKey]);
  if (!category) {
    category = categories[0];
    owner[activeKey] = category.id;
  }
  return category;
}

function setActiveMediaCategory(owner, kind, categoryId) {
  const [, activeKey] = mediaCategoryConfig(kind);
  const categories = getMediaCategories(owner, kind);
  const category = categories.find(item => item.id === categoryId) || categories[0];
  owner[activeKey] = category.id;
  return category;
}

function mediaCategoryCount(ownerId, scope, kind, categoryId) {
  return S.media
    .map(ensureMediaShape)
    .filter(media => media.gameId === ownerId && media.scope === scope && media.kind === kind && media.categoryId === categoryId)
    .length;
}

function mediaCategoryLabel(kind) {
  return mediaCategoryConfig(kind)[2];
}

function ensureMediaShape(media) {
  media.id ??= 'm_' + uid();
  media.scope ??= 'game';
  media.kind ??= media.type === 'audio' ? 'sound' : media.type === 'video' || media.type === 'gif' ? 'video' : 'photo';
  media.type ??= inferMediaType(media.path || media.originalPath || '');
  media.name ??= nodePath.basename(media.path || media.originalPath || 'Media', nodePath.extname(media.path || media.originalPath || ''));
  media.description ??= '';
  media.tags = Array.isArray(media.tags) ? media.tags : [];
  media.importance = importanceLevel(media.importance).id;
  media.order ??= 0;
  media.categoryId ??= 'imgcat_default';
  media.createdAt ??= now();
  media.updatedAt ??= now();
  return media;
}

function moveItemBefore(items, draggedId, beforeId) {
  const from = items.findIndex(item => sameId(item.id, draggedId));
  if (from < 0) return false;
  const [item] = items.splice(from, 1);
  let to = beforeId ? items.findIndex(next => sameId(next.id, beforeId)) : items.length;
  if (to < 0) to = items.length;
  items.splice(to, 0, item);
  return true;
}

function moveIdBefore(ids, draggedId, beforeId) {
  const from = ids.findIndex(id => sameId(id, draggedId));
  if (from < 0) return false;
  ids.splice(from, 1);
  let to = beforeId ? ids.findIndex(id => sameId(id, beforeId)) : ids.length;
  if (to < 0) to = ids.length;
  ids.splice(to, 0, draggedId);
  return true;
}

function bindSortableIdCard(card, id, mime, onMove) {
  card.draggable = true;
  card.addEventListener('dragstart', e => {
    if (['INPUT', 'TEXTAREA'].includes(e.target.tagName) || e.target.closest('.rarity-badge, .remove-board-photo, .remove-project-media, .remove-game-media')) {
      e.preventDefault();
      return;
    }
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData(mime, id);
    e.dataTransfer.setData('text/plain', id);
    card.classList.add('dragging');
    card.dataset.draggingCard = '1';
  });
  card.addEventListener('dragend', () => {
    card.classList.remove('dragging');
    card.classList.remove('drop-before');
    card.dataset.justDraggedCard = '1';
    delete card.dataset.draggingCard;
    setTimeout(() => delete card.dataset.justDraggedCard, 180);
  });
  card.addEventListener('click', e => {
    if (!card.dataset.draggingCard && !card.dataset.justDraggedCard) return;
    e.preventDefault();
    e.stopPropagation();
  }, true);
  card.addEventListener('dragover', e => {
    e.preventDefault();
    if (hasMoveDragType(e, mime)) card.classList.add('drop-before');
  });
  card.addEventListener('dragleave', () => card.classList.remove('drop-before'));
  card.addEventListener('drop', e => {
    e.preventDefault();
    card.classList.remove('drop-before');
    const draggedId = getDraggedId(e, mime);
    if (draggedId && draggedId !== id) onMove(draggedId, id);
  });
}

function placeBlockPlaceholder(list, placeholder, draggedId, clientY) {
  const beforeId = blockInsertBeforeId(list, draggedId, clientY);
  const beforeCard = beforeId
    ? Array.from(list.querySelectorAll('.note-card[data-block-id]')).find(item => item.dataset.blockId === beforeId)
    : null;
  const spacer = list.querySelector('.notes-spacer');
  list.insertBefore(placeholder, beforeCard || spacer || null);
}

function blockInsertBeforeId(list, draggedId, clientY) {
  const draggedKey = String(draggedId);
  const cards = Array.from(list.querySelectorAll('.note-card[data-block-id]'))
    .filter(item => item.dataset.blockId !== draggedKey);
  for (const target of cards) {
    const rect = target.getBoundingClientRect();
    if (clientY < rect.top + rect.height / 2) {
      return target.dataset.blockId || null;
    }
  }
  return null;
}

function blockOrderFromPlaceholder(list, placeholder, draggedId) {
  const draggedKey = String(draggedId);
  return Array.from(list.children)
    .map(child => {
      if (child === placeholder) return draggedKey;
      if (child.dataset?.blockId === draggedKey) return null;
      return child.dataset?.blockId || null;
    })
    .filter(Boolean);
}

function reorderBlocksByVisibleOrder(blocks, orderedIds, categoryId) {
  const visible = visibleBlocksForCategory(blocks, categoryId);
  const byId = new Map(visible.map(block => [String(block.id), block]));
  const ordered = orderedIds.map(id => byId.get(String(id))).filter(Boolean);
  if (ordered.length !== visible.length) return false;
  if (visible.every((block, index) => sameId(ordered[index]?.id, block.id))) return false;
  if (categoryId) {
    let index = 0;
    blocks.splice(0, blocks.length, ...blocks.map(block => blockMatchesCategory(block, categoryId) ? ordered[index++] : block));
  } else {
    blocks.splice(0, blocks.length, ...ordered);
  }
  return true;
}

function bindSortableBlock(card, blocks, block, categoryId, onReorder) {
  const blockId = String(ensureBlockShape(block).id);
  card.dataset.blockId = blockId;
  const handle = card.querySelector('.drag-handle');
  const head = card.querySelector('.card-head');
  if (!handle || !head) return;
  card.draggable = false;
  handle.draggable = false;
  handle.tabIndex = 0;
  handle.setAttribute('role', 'button');
  handle.setAttribute('aria-label', 'Move block');

  const startMove = e => {
    if (e.button !== undefined && e.button !== 0) return;
    if (e.target.closest('input, textarea, button, select, .rarity-badge, .note-media-open')) return;
    if (!e.target.closest('.drag-handle, .card-head')) return;
    const list = card.closest('.notes-list');
    if (!list) return;
    e.preventDefault();
    e.stopPropagation();

    const startX = e.clientX;
    const startY = e.clientY;
    let offsetX = 0;
    let offsetY = 0;
    let dragging = false;
    let placeholder = null;
    let preview = null;
    let previousCardStyle = null;
    const moveEventName = e.type === 'pointerdown' ? 'pointermove' : 'mousemove';
    const upEventName = e.type === 'pointerdown' ? 'pointerup' : 'mouseup';
    const cancelEventName = e.type === 'pointerdown' ? 'pointercancel' : 'mouseleave';

    const copyFieldValues = (source, clone) => {
      const sourceFields = source.querySelectorAll('input, textarea, select');
      clone.querySelectorAll('input, textarea, select').forEach((field, index) => {
        const sourceField = sourceFields[index];
        if (!sourceField) return;
        field.value = sourceField.value;
        if ('checked' in field) field.checked = sourceField.checked;
      });
    };

    const beginDrag = moveEvent => {
      const rect = card.getBoundingClientRect();
      offsetX = startX - rect.left;
      offsetY = startY - rect.top;
      previousCardStyle = card.getAttribute('style');
      placeholder = document.createElement('div');
      placeholder.className = 'notes-placeholder';
      placeholder.style.height = `${Math.round(rect.height)}px`;
      placeholder.style.margin = getComputedStyle(card).margin;
      list.insertBefore(placeholder, card);

      preview = card.cloneNode(true);
      copyFieldValues(card, preview);
      preview.setAttribute('aria-hidden', 'true');
      preview.classList.add('dragging', 'dragging-fixed');
      preview.style.width = `${Math.round(rect.width)}px`;
      preview.style.left = `${Math.round(rect.left)}px`;
      preview.style.top = `${Math.round(rect.top)}px`;
      document.body.appendChild(preview);

      card.classList.add('dragging-source');
      handle.classList.add('dragging');
      card.style.display = 'none';
      dragging = true;
      updateDrag(moveEvent);
    };

    const autoScroll = clientY => {
      const scroller = list.closest('.tab-scroll, .day-scroll, .screen-scroll');
      if (!scroller) return;
      const rect = scroller.getBoundingClientRect();
      if (clientY < rect.top + 52) scroller.scrollTop -= 16;
      if (clientY > rect.bottom - 52) scroller.scrollTop += 16;
    };

    const updateDrag = moveEvent => {
      const clientX = moveEvent.clientX;
      const clientY = moveEvent.clientY;
      if (preview) {
        preview.style.left = `${Math.round(clientX - offsetX)}px`;
        preview.style.top = `${Math.round(clientY - offsetY)}px`;
      }
      placeBlockPlaceholder(list, placeholder, blockId, clientY);
      autoScroll(clientY);
    };

    const cleanup = () => {
      document.removeEventListener(moveEventName, onMove, true);
      document.removeEventListener(upEventName, onUp, true);
      document.removeEventListener(cancelEventName, onCancel, true);
    };

    const restoreCard = () => {
      preview?.remove();
      preview = null;
      card.classList.remove('dragging-source');
      handle.classList.remove('dragging');
      if (previousCardStyle === null) card.removeAttribute('style');
      else card.setAttribute('style', previousCardStyle);
      if (placeholder?.parentNode) placeholder.parentNode.insertBefore(card, placeholder);
      placeholder?.remove();
    };

    const onMove = moveEvent => {
      const distance = Math.abs(moveEvent.clientX - startX) + Math.abs(moveEvent.clientY - startY);
      if (!dragging && distance < 4) return;
      if (!dragging) beginDrag(moveEvent);
      else updateDrag(moveEvent);
      moveEvent.preventDefault();
      moveEvent.stopPropagation();
    };

    const onUp = upEvent => {
      cleanup();
      if (!dragging) return;
      updateDrag(upEvent);
      const beforeId = blockInsertBeforeId(list, blockId, upEvent.clientY);
      const orderedIds = blockOrderFromPlaceholder(list, placeholder, blockId);
      restoreCard();
      if (moveBlockBefore(blocks, blockId, beforeId, categoryId) || reorderBlocksByVisibleOrder(blocks, orderedIds, categoryId)) {
        block.updatedAt = now();
        onReorder();
      }
    };

    const onCancel = () => {
      cleanup();
      if (dragging) restoreCard();
    };

    document.addEventListener(moveEventName, onMove, true);
    document.addEventListener(upEventName, onUp, true);
    document.addEventListener(cancelEventName, onCancel, true);
  };

  if (window.PointerEvent) card.addEventListener('pointerdown', startMove);
  else card.addEventListener('mousedown', startMove);
}

function blockTextForCopy(block) {
  ensureBlockShape(block);
  if (block.type === 'text') return [block.title || 'Text', block.text || ''].filter(Boolean).join('\n');
  const media = getMediaById(block.mediaId);
  return [
    block.title || media?.name || 'Media',
    block.caption || media?.description || '',
  ].filter(Boolean).join('\n');
}

function copyBlocksToClipboard(blocks) {
  const text = (blocks || []).map(blockTextForCopy).filter(Boolean).join('\n\n');
  if (!text.trim()) {
    toast('Nothing to copy');
    return;
  }
  try {
    clipboard.writeText(text);
    toast('Copied');
  } catch (e) {
    toast('Could not copy');
  }
}

function copyBlockContainerToClipboard(container, categoryId = null) {
  ensureBlockContainerShape(container);
  const chunks = [];
  const categories = categoryId
    ? container.categories.filter(category => sameId(category.id, categoryId))
    : container.categories;
  categories.forEach(category => {
    const text = container.blocks
      .filter(block => blockMatchesCategory(block, category.id))
      .map(blockTextForCopy)
      .filter(Boolean)
      .join('\n\n');
    if (text.trim()) chunks.push(`# ${category.title}\n\n${text}`);
  });
  const result = chunks.join('\n\n');
  if (!result.trim()) {
    toast('Nothing to copy');
    return;
  }
  try {
    clipboard.writeText(result);
    toast('Copied');
  } catch (e) {
    toast('Could not copy');
  }
}

function routeSnapshot() {
  return {
    view: S.view,
    activeGameId: S.activeGameId,
    activeTab: S.activeTab,
    activeMediaId: S.activeMediaId,
    activeDailyNoteId: S.activeDailyNoteId,
    activePhotoBoardId: S.activePhotoBoardId,
    activeProjectId: S.activeProjectId,
    activeProjectTab: S.activeProjectTab,
    activeMilestoneId: S.activeMilestoneId,
    activeKanbanBoardId: S.activeKanbanBoardId,
  };
}

function sameRoute(a, b) {
  return JSON.stringify(a) === JSON.stringify(b);
}

function pushRoute() {
  if (restoringRoute) return;
  const route = routeSnapshot();
  if (!navStack.length || !sameRoute(navStack[navStack.length - 1], route)) {
    navStack.push(route);
    if (navStack.length > 80) navStack.shift();
  }
}

function restoreRoute(route) {
  restoringRoute = true;
  Object.assign(S, route);
  renderApp();
  restoringRoute = false;
}

function goBack() {
  const route = navStack.pop();
  if (route) {
    restoreRoute(route);
    return true;
  }
  if (S.activeDailyNoteId) {
    S.activeDailyNoteId = null;
    renderDailyNotes();
    return true;
  }
  if (S.activePhotoBoardId) {
    S.activePhotoBoardId = null;
    renderPhotoBoards();
    return true;
  }
  if (S.activeProjectId) {
    S.activeProjectId = null;
    renderProjects();
    return true;
  }
  if (S.view === 'game' || S.view === 'templates') {
    setView('library', { skipHistory: true });
    return true;
  }
  return false;
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
  ensureMediaCategoryBucket(game, 'photo');
  ensureMediaCategoryBucket(game, 'video');
  ensureMediaCategoryBucket(game, 'sound');
  game.answers ??= {};
  game.notes = ensureBlockContainerShape(game.notes);
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
  scheduleScrollRestore();
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

function setView(view, options = {}) {
  if (S.view !== 'game' || view !== 'game') stopViewer();
  closeAlbumLightbox();
  closeTaskNotebook();
  closeImportanceMenu();
  closeMilestoneMenu();
  closeCategoryMenu();
  if (!options.skipHistory && S.view !== view) pushRoute();
  if (view === 'daily-notes') S.activeDailyNoteId = null;
  if (view === 'photo-boards') S.activePhotoBoardId = null;
  if (view === 'projects') S.activeProjectId = null;
  S.view = view;
  renderApp();
}

function openGame(gameId, tab = 'questions', options = {}) {
  stopViewer();
  if (!options.skipHistory && (S.view !== 'game' || S.activeGameId !== gameId || S.activeTab !== tab)) pushRoute();
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
  else if (S.view === 'daily-notes') renderDailyNotes();
  else if (S.view === 'photo-boards') renderPhotoBoards();
  else if (S.view === 'projects') renderProjects();
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
          <input class="text-input search-input" id="game-search" value="${esc(S.gameSearch || '')}" placeholder="Search">
          <button class="ghost-btn" id="library-templates">Templates</button>
          <button class="inline-btn" id="library-new-game">+ Game</button>
        </div>
      </div>
      <div class="screen-scroll" id="library-body"></div>
    </section>`;

  $('library-new-game').onclick = createGameFlow;
  $('library-templates').onclick = () => setView('templates');
  $('game-search').oninput = e => {
    S.gameSearch = e.target.value;
    scheduleScrollRestore();
    renderLibraryCards();
  };

  renderLibraryCards();
}

function renderLibraryCards() {
  const body = $('library-body');
  if (!body) return;
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

  const games = [...S.games]
    .filter(game => searchMatches([game.title, game.genre, game.status, game.link, formatShortDate(game.updatedAt)], S.gameSearch))
    .sort((a, b) => String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')));

  if (!games.length) {
    body.innerHTML = '<div class="empty-state"><div class="empty-box"><div class="empty-title">No matches</div></div></div>';
    return;
  }

  body.innerHTML = '<div class="games-grid" id="games-grid"></div>';
  const grid = $('games-grid');
  games.forEach(game => grid.appendChild(buildGameCard(game)));
}

function renderDailyNotes() {
  stopViewer();
  hidePlayback();
  S.dailyNotes = S.dailyNotes.map(ensureDailyNoteShape);
  const active = getActiveDailyNote();
  if (active) {
    renderDailyNoteWorkspace(active);
    return;
  }

  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Notes</h1>
        </div>
        <div class="head-actions">
          <input class="text-input search-input" id="daily-search" value="${esc(S.dailySearch || '')}" placeholder="Search">
          <input class="text-input compact-date" id="note-date-picker" type="date" value="${esc(todayISO())}">
          <button class="ghost-btn" id="add-date-note">+ Day</button>
          <button class="inline-btn" id="add-today-note">Today</button>
        </div>
      </div>
      <div class="screen-scroll" id="daily-library-body"></div>
    </section>`;

  $('add-today-note').onclick = () => createDailyNote(todayISO());
  $('add-date-note').onclick = () => createDailyNote($('note-date-picker').value || todayISO());
  $('daily-search').oninput = e => {
    S.dailySearch = e.target.value;
    scheduleScrollRestore();
    renderDailyNoteCards();
  };
  renderDailyNoteCards();
}

function renderDailyNoteCards() {
  const body = $('daily-library-body');
  if (!body) return;
  if (!S.dailyNotes.length) {
    body.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">Empty</div>
          <button class="inline-btn" id="empty-create-day">Today</button>
        </div>
      </div>`;
    $('empty-create-day').onclick = () => createDailyNote(todayISO());
    return;
  }
  const notes = [...S.dailyNotes]
    .filter(note => searchMatches([
      note.title,
      note.date,
      formatDateTitle(note.date),
      ...(note.blocks || []).flatMap(block => [block.title, block.text, block.caption]),
    ], S.dailySearch))
    .sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));

  if (!notes.length) {
    body.innerHTML = '<div class="empty-state"><div class="empty-box"><div class="empty-title">No matches</div></div></div>';
    return;
  }

  body.innerHTML = '<div class="games-grid" id="daily-grid"></div>';
  const grid = $('daily-grid');
  notes.forEach(note => grid.appendChild(buildDailyNoteCard(note)));
}

function buildDailyNoteCard(note) {
  const card = document.createElement('div');
  card.className = `game-card note-grid-card importance-surface-${esc(importanceLevel(note.importance).id)}`;
  const blockCount = (note.blocks || []).length;
  card.innerHTML = `
    <div class="game-card-main">
      <div class="game-cover date-cover">${esc((note.date || '').slice(-2) || 'N')}</div>
      <div class="game-name">${esc(note.title || formatDateTitle(note.date))}</div>
    </div>
    <div class="card-sub">${blockCount} blocks</div>`;
  card.onclick = () => {
    pushRoute();
    S.activeDailyNoteId = note.id;
    renderDailyNotes();
  };
  return card;
}

function renderDailyNoteWorkspace(note) {
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head roomy-head">
        <div class="title-wrap">
          <input id="daily-title" class="section-title-input" value="${esc(note.title || '')}">
        </div>
        <div class="head-actions">
          ${importanceBadgeHTML(note.importance)}
          <button class="ghost-btn" id="daily-add-text">+ Text</button>
          <button class="ghost-btn" id="daily-add-photo">+ Photo</button>
          <button class="ghost-btn" id="daily-back">Notes</button>
          <button class="danger-btn" id="daily-delete">Delete</button>
        </div>
      </div>
      <div class="day-scroll">
        ${blockCategoryControlsHTML(note, 'daily')}
        <div class="notes-list" id="daily-blocks"></div>
      </div>
    </section>`;

  $('daily-title').oninput = e => {
    note.title = e.target.value;
    note.updatedAt = now();
    markDirty();
  };
  bindImportanceTriggers(document.querySelector('.screen-head'), () => note.importance, value => {
    note.importance = value;
    note.updatedAt = now();
    markDirty();
    renderDailyNoteWorkspace(note);
  });
  bindBlockCategoryControls(note, 'daily', shouldRender => {
    note.updatedAt = now();
    markDirty();
    if (shouldRender) renderDailyNoteWorkspace(note);
  });
  $('daily-add-text').onclick = () => {
    const block = createTextBlock();
    block.categoryId = getActiveBlockCategory(note).id;
    note.blocks.push(block);
    note.updatedAt = now();
    markDirty();
    renderDailyNoteWorkspace(note);
  };
  $('daily-add-photo').onclick = () => addDailyNoteMedia(note);
  $('daily-back').onclick = () => {
    if (!goBack()) {
      S.activeDailyNoteId = null;
      renderDailyNotes();
    }
  };
  $('daily-delete').onclick = () => {
    if (!confirm(`Delete notes for ${formatDateTitle(note.date)}?`)) return;
    S.dailyNotes = S.dailyNotes.filter(item => item.id !== note.id);
    S.activeDailyNoteId = null;
    markDirty();
    renderDailyNotes();
  };

  renderEditableBlocks($('daily-blocks'), note.blocks, {
    ownerName: 'note',
    onChange: () => {
      note.updatedAt = now();
      markDirty();
    },
    onDelete: block => {
      note.blocks = note.blocks.filter(item => item.id !== block.id);
      note.updatedAt = now();
      markDirty();
      renderDailyNoteWorkspace(note);
    },
    onReorder: () => {
      note.updatedAt = now();
      markDirty();
      renderDailyNoteWorkspace(note);
    },
  }, { categoryId: getActiveBlockCategory(note).id });
}

function createDailyNote(date) {
  const cleanDate = date || todayISO();
  const existing = S.dailyNotes.find(note => note.date === cleanDate);
  if (existing) {
    S.activeDailyNoteId = existing.id;
    renderDailyNotes();
    return;
  }
  const note = ensureDailyNoteShape({
    id: 'dn_' + uid(),
    date: cleanDate,
    title: formatDateTitle(cleanDate),
    importance: 'noted',
    blocks: [createTextBlock()],
    createdAt: now(),
    updatedAt: now(),
  });
  S.dailyNotes.push(note);
  S.activeDailyNoteId = note.id;
  markDirty();
  renderDailyNotes();
}

function renderDailyNoteList() {
  const list = $('daily-note-list');
  if (!list) return;
  list.innerHTML = '';
  const notes = [...S.dailyNotes].sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
  if (!notes.length) {
    list.innerHTML = '<div class="card-sub">Empty</div>';
    return;
  }
  notes.forEach(note => {
    const row = document.createElement('button');
    row.className = 'date-row' + (note.id === S.activeDailyNoteId ? ' active' : '');
    row.innerHTML = `
      <span>${importanceBadgeHTML(note.importance)}</span>
      <span class="date-row-main">
        <span class="date-row-title">${esc(formatDateTitle(note.date))}</span>
        <span class="date-row-sub">${esc(note.title || '')}</span>
      </span>`;
    row.onclick = () => {
      pushRoute();
      S.activeDailyNoteId = note.id;
      renderDailyNotes();
    };
    list.appendChild(row);
  });
}

function renderDailyNoteDetail(note) {
  const editor = $('day-editor');
  if (!editor) return;
  if (!note) {
    editor.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">Empty</div>
          <button class="inline-btn" id="empty-create-day">Today</button>
        </div>
      </div>`;
    $('empty-create-day').onclick = () => createDailyNote(todayISO());
    return;
  }

  editor.innerHTML = `
    <div class="day-head">
      <div>
        <div class="eyebrow">${esc(formatDateTitle(note.date))}</div>
        <input id="daily-title" class="section-title-input" value="${esc(note.title || '')}">
      </div>
      <div class="head-actions">
        ${importanceBadgeHTML(note.importance)}
        <button class="ghost-btn" id="daily-add-text">+ Text</button>
        <button class="ghost-btn" id="daily-add-photo">+ Photo</button>
        <button class="danger-btn" id="daily-delete">Delete</button>
      </div>
    </div>
    <div class="day-scroll">
      <div class="notes-list" id="daily-blocks"></div>
    </div>`;

  $('daily-title').oninput = e => {
    note.title = e.target.value;
    note.updatedAt = now();
    markDirty();
    renderDailyNoteList();
  };
  bindImportanceTriggers(document.querySelector('.day-head'), () => note.importance, value => {
    note.importance = value;
    note.updatedAt = now();
    markDirty();
    renderDailyNoteDetail(note);
  });
  $('daily-add-text').onclick = () => {
    const block = createTextBlock();
    block.categoryId = getActiveBlockCategory(note).id;
    note.blocks.push(block);
    note.updatedAt = now();
    markDirty();
    renderDailyNoteDetail(note);
  };
  $('daily-add-photo').onclick = () => addDailyNoteMedia(note);
  $('daily-delete').onclick = () => {
    if (!confirm(`Delete notes for ${formatDateTitle(note.date)}?`)) return;
    S.dailyNotes = S.dailyNotes.filter(item => item.id !== note.id);
    S.activeDailyNoteId = null;
    markDirty();
    renderDailyNotes();
  };

  renderEditableBlocks($('daily-blocks'), note.blocks, {
    ownerName: 'note',
    onChange: () => {
      note.updatedAt = now();
      markDirty();
      renderDailyNoteList();
    },
    onDelete: block => {
      note.blocks = note.blocks.filter(item => item.id !== block.id);
      note.updatedAt = now();
      markDirty();
      renderDailyNoteDetail(note);
    },
    onReorder: () => {
      note.updatedAt = now();
      markDirty();
      renderDailyNoteDetail(note);
    },
  });
}

function renderEditableBlocks(list, blocks, callbacks, options = {}) {
  if (!list) return;
  const categoryId = options.categoryId || null;
  const visibleBlocks = visibleBlocksForCategory(blocks, categoryId);
  const handleReorder = () => {
    callbacks.onChange();
    if (callbacks.onReorder) callbacks.onReorder();
    else renderEditableBlocks(list, blocks, callbacks, options);
  };
  list.classList.add('has-spacer');
  list.innerHTML = '';
  const appendSpacer = () => {
    const spacer = document.createElement('div');
    spacer.className = 'notes-spacer';
    list.appendChild(spacer);
  };
  if (!visibleBlocks.length) {
    list.innerHTML = '<div class="block-card"><div class="empty-title">Empty</div></div>';
    appendSpacer();
    return;
  }

  visibleBlocks.forEach((block, visibleIndex) => {
    ensureBlockShape(block);
    const card = document.createElement('div');
    card.className = `note-card block-note importance-surface-${esc(importanceLevel(block.importance).id)}`;
    const moveButtons = `
      <button class="mini-btn block-move-btn" data-block-move="up" ${visibleIndex === 0 ? 'disabled' : ''}>Up</button>
      <button class="mini-btn block-move-btn" data-block-move="down" ${visibleIndex === visibleBlocks.length - 1 ? 'disabled' : ''}>Down</button>`;
    if (block.type === 'text') {
      card.innerHTML = `
        <div class="card-head">
          <div class="block-head-title">
            <span class="drag-handle" title="Move">::</span>
            ${importanceBadgeHTML(block.importance)}
            <input class="block-title-input" value="${esc(block.title || 'Text')}">
          </div>
          <div class="card-actions">
            ${moveButtons}
            <button class="danger-btn delete-block">Delete</button>
          </div>
        </div>
        <div class="card-body">
          <textarea class="text-area block-text" style="height:${esc(block.height)}px" placeholder="Note...">${esc(block.text || '')}</textarea>
        </div>`;
      card.querySelector('.block-title-input').oninput = e => {
        block.title = e.target.value;
        block.updatedAt = now();
        callbacks.onChange();
      };
      bindImportanceTriggers(card, () => block.importance, value => {
        block.importance = value;
        block.updatedAt = now();
        callbacks.onChange();
        renderEditableBlocks(list, blocks, callbacks, options);
      });
      card.querySelector('.block-text').oninput = e => {
        block.text = e.target.value;
        block.updatedAt = now();
        callbacks.onChange();
      };
      persistBlockHeight(card.querySelector('.block-text'), block, callbacks);
    } else {
      const media = getMediaById(block.mediaId);
      card.innerHTML = `
        <div class="card-head">
          <div class="block-head-title">
            <span class="drag-handle" title="Move">::</span>
            ${importanceBadgeHTML(block.importance)}
            <input class="block-title-input" value="${esc(block.title || media?.name || 'Media')}">
            <div class="card-sub">${esc(mediaKindLabel(media?.kind))}</div>
          </div>
          <div class="card-actions">
            ${moveButtons}
            <button class="danger-btn delete-block">Delete</button>
          </div>
        </div>
        <div class="card-body">
          ${noteMediaPreviewHTML(block)}
          <div class="field" style="margin-top:12px">
            <label class="field-label">Caption</label>
            <input class="text-input block-caption" value="${esc(block.caption || '')}">
          </div>
        </div>`;
      card.querySelector('.block-title-input').oninput = e => {
        block.title = e.target.value;
        if (media) {
          media.name = e.target.value;
          media.updatedAt = now();
        }
        block.updatedAt = now();
        callbacks.onChange();
      };
      bindImportanceTriggers(card, () => block.importance, value => {
        block.importance = value;
        block.updatedAt = now();
        callbacks.onChange();
        renderEditableBlocks(list, blocks, callbacks, options);
      });
      const caption = card.querySelector('.block-caption');
      if (caption) caption.oninput = e => {
        block.caption = e.target.value;
        block.updatedAt = now();
        callbacks.onChange();
      };
      const open = card.querySelector('.note-media-open');
      if (open && media) {
        open.onclick = () => openAlbumPhoto(media.id);
        persistBlockHeight(open, block, callbacks);
      }
    }

    card.querySelectorAll('[data-block-move]').forEach(btn => {
      btn.onclick = () => {
        if (btn.disabled) return;
        const offset = btn.dataset.blockMove === 'up' ? -1 : 1;
        if (!moveBlockByOffset(blocks, block.id, offset, categoryId)) return;
        block.updatedAt = now();
        callbacks.onChange();
        if (callbacks.onReorder) callbacks.onReorder();
        else renderEditableBlocks(list, blocks, callbacks, options);
      };
    });
    card.querySelector('.delete-block').onclick = () => callbacks.onDelete(block);
    bindSortableBlock(card, blocks, block, categoryId, handleReorder);
    list.appendChild(card);
  });
  appendSpacer();
}

async function addDailyNoteMedia(note) {
  const files = await pickMediaFiles('photo');
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, note.id, 'photo', 'dailyNote');
    if (media) note.blocks.push({
      id: uid(),
      type: 'media',
      mediaId: media.id,
      title: media.name,
      caption: '',
      importance: note.importance || 'common',
      categoryId: getActiveBlockCategory(note).id,
      height: 270,
      createdAt: now(),
      updatedAt: now(),
    });
  });
  note.updatedAt = now();
  markDirty();
  renderDailyNoteWorkspace(note);
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

function renderPhotoBoards() {
  stopViewer();
  hidePlayback();
  S.photoBoards = S.photoBoards.map(ensurePhotoBoardShape);
  const active = getActivePhotoBoard();
  if (active) {
    renderPhotoBoardWorkspace(active);
    return;
  }

  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Photos</h1>
        </div>
        <div class="head-actions">
          <input class="text-input search-input" id="photo-search" value="${esc(S.photoSearch || '')}" placeholder="Search">
          <button class="inline-btn" id="new-photo-board">+ Board</button>
        </div>
      </div>
      <div class="screen-scroll" id="photo-board-library-body"></div>
    </section>`;

  $('new-photo-board').onclick = createPhotoBoardFlow;
  $('photo-search').oninput = e => {
    S.photoSearch = e.target.value;
    scheduleScrollRestore();
    renderPhotoBoardCards();
  };
  renderPhotoBoardCards();
}

function renderPhotoBoardCards() {
  const body = $('photo-board-library-body');
  if (!body) return;
  if (!S.photoBoards.length) {
    body.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">No Boards</div>
          <button class="inline-btn" id="empty-create-board">+ Board</button>
        </div>
      </div>`;
    $('empty-create-board').onclick = createPhotoBoardFlow;
    return;
  }
  const boards = [...S.photoBoards]
    .filter(board => searchMatches([
      board.title,
      board.description,
      ...getBoardPhotos(board).map(media => media.name),
    ], S.photoSearch))
    .sort((a, b) => String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')));

  if (!boards.length) {
    body.innerHTML = '<div class="empty-state"><div class="empty-box"><div class="empty-title">No matches</div></div></div>';
    return;
  }

  body.innerHTML = '<div class="games-grid" id="photo-board-grid"></div>';
  const grid = $('photo-board-grid');
  boards.forEach(board => grid.appendChild(buildPhotoBoardCard(board)));
}

function buildPhotoBoardCard(board) {
  const card = document.createElement('div');
  card.className = 'game-card album-grid-card';
  const cover = getBoardPhotos(board)[0];
  card.innerHTML = `
    <div class="game-card-main">
      <div class="game-cover">${cover ? mediaPreviewHTML(cover, true) : 'P'}</div>
      <div class="game-name">${esc(board.title)}</div>
    </div>
    <div class="card-sub">${getBoardPhotos(board).length} photos</div>`;
  card.onclick = () => {
    pushRoute();
    S.activePhotoBoardId = board.id;
    renderPhotoBoards();
  };
  return card;
}

function renderPhotoBoardWorkspace(board) {
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head roomy-head">
        <div class="title-wrap">
          <h1 class="screen-title">Photos</h1>
        </div>
        <div class="head-actions">
          <button class="ghost-btn" id="photo-board-back">Boards</button>
          <button class="ghost-btn" id="add-board-photos">+ Photos</button>
          <button class="danger-btn" id="delete-board">Delete</button>
        </div>
      </div>
      <section class="album-main" id="photo-board-detail"></section>
    </section>`;

  $('photo-board-back').onclick = () => {
    if (!goBack()) {
      S.activePhotoBoardId = null;
      renderPhotoBoards();
    }
  };
  renderPhotoBoardDetail(board);
}

function createPhotoBoardFlow() {
  askText('New Photo Board', '', 'Create', title => {
    const board = ensurePhotoBoardShape({
      id: 'pb_' + uid(),
      title,
      description: '',
      photoIds: [],
      createdAt: now(),
      updatedAt: now(),
    });
    S.photoBoards.push(board);
    S.activePhotoBoardId = board.id;
    markDirty();
    renderPhotoBoards();
  });
}

function renderPhotoBoardList() {
  const list = $('photo-board-list');
  if (!list) return;
  list.innerHTML = '';
  const boards = [...S.photoBoards].sort((a, b) => String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')));
  if (!boards.length) {
    list.innerHTML = '<div class="card-sub">Empty</div>';
    return;
  }
  boards.forEach(board => {
    const row = document.createElement('button');
    row.className = 'album-board-row' + (board.id === S.activePhotoBoardId ? ' active' : '');
    row.innerHTML = `
      <span class="album-board-name">${esc(board.title)}</span>
      <span class="album-board-count">${getBoardPhotos(board).length}</span>`;
    row.onclick = () => {
      S.activePhotoBoardId = board.id;
      pushRoute();
      renderPhotoBoards();
    };
    list.appendChild(row);
  });
}

function renderPhotoBoardDetail(board) {
  const detail = $('photo-board-detail');
  if (!detail) return;
  if (!board) {
    detail.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">No Boards</div>
          <button class="inline-btn" id="empty-create-board">+ Board</button>
        </div>
      </div>`;
    $('empty-create-board').onclick = createPhotoBoardFlow;
    return;
  }

  const photos = getBoardPhotos(board);
  detail.innerHTML = `
    <div class="album-head">
      <div>
        <input id="board-title" class="section-title-input" value="${esc(board.title)}">
      </div>
      <div class="head-actions">
        <button class="ghost-btn" id="sort-board-importance">Sort importance</button>
      </div>
    </div>
    <div class="album-scroll">
      <div class="masonry-grid" id="album-grid"></div>
    </div>`;

  $('board-title').oninput = e => {
    board.title = e.target.value;
    board.updatedAt = now();
    markDirty();
  };
  $('sort-board-importance').onclick = () => {
    const sorted = getBoardPhotos(board);
    sortByImportance(sorted);
    board.photoIds = sorted.map(media => media.id);
    board.updatedAt = now();
    markDirty();
    renderPhotoBoardDetail(board);
  };
  $('add-board-photos').onclick = () => addPhotosToBoard(board);
  $('delete-board').onclick = () => {
    if (!confirm(`Delete board "${board.title}"?`)) return;
    S.media = S.media.filter(media => !(board.photoIds || []).includes(media.id));
    S.photoBoards = S.photoBoards.filter(item => item.id !== board.id);
    S.activePhotoBoardId = null;
    markDirty();
    renderPhotoBoards();
  };

  const grid = $('album-grid');
  if (!photos.length) {
    grid.innerHTML = `
      <button class="album-drop-card" id="empty-add-photos">
        <span>+ Photos</span>
      </button>`;
    $('empty-add-photos').onclick = () => addPhotosToBoard(board);
    return;
  }

  photos.forEach(media => {
    const card = document.createElement('div');
    card.className = 'album-photo-card';
    card.innerHTML = `
      <button class="album-photo-open">${mediaPreviewHTML(media, true)}</button>
      <div class="album-photo-foot">
        ${importanceBadgeHTML(media.importance)}
        <input class="album-photo-title" value="${esc(media.name)}">
        <button class="mini-btn remove-board-photo">x</button>
      </div>`;
    card.querySelector('.album-photo-open').onclick = () => openAlbumPhoto(media.id);
    bindImportanceTriggers(card, () => media.importance, value => {
      media.importance = value;
      media.updatedAt = now();
      board.updatedAt = now();
      markDirty();
      renderPhotoBoardDetail(board);
    });
    card.querySelector('.album-photo-title').oninput = e => {
      media.name = e.target.value;
      media.updatedAt = now();
      board.updatedAt = now();
      markDirty();
    };
    card.querySelector('.remove-board-photo').onclick = () => {
      if (!confirm(`Remove "${media.name}" from this board?`)) return;
      board.photoIds = board.photoIds.filter(id => id !== media.id);
      S.media = S.media.filter(item => item.id !== media.id);
      board.updatedAt = now();
      markDirty();
      renderPhotoBoardDetail(board);
    };
    bindSortableIdCard(card, media.id, 'application/x-refboard-photo', (draggedId, beforeId) => {
      if (moveIdBefore(board.photoIds, draggedId, beforeId)) {
        board.updatedAt = now();
        markDirty();
        renderPhotoBoardDetail(board);
      }
    });
    grid.appendChild(card);
  });

  const addCard = document.createElement('button');
  addCard.className = 'album-drop-card';
  addCard.innerHTML = '<span>+ Photos</span>';
  addCard.onclick = () => addPhotosToBoard(board);
  grid.appendChild(addCard);
  const spacer = document.createElement('div');
  spacer.className = 'media-grid-spacer';
  spacer.addEventListener('dragover', e => e.preventDefault());
  spacer.addEventListener('drop', e => {
    e.preventDefault();
    const draggedId = e.dataTransfer.getData('application/x-refboard-photo');
    if (draggedId && moveIdBefore(board.photoIds, draggedId, null)) {
      board.updatedAt = now();
      markDirty();
      renderPhotoBoardDetail(board);
    }
  });
  grid.appendChild(spacer);
}

async function addPhotosToBoard(board) {
  const files = await pickMediaFiles('photo');
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, board.id, 'photo', 'photoBoard');
    if (media) board.photoIds.push(media.id);
  });
  board.updatedAt = now();
  markDirty();
  renderPhotoBoardDetail(board);
  toast(`Added: ${files.length}`);
}

function openAlbumPhoto(mediaId) {
  const media = getMediaById(mediaId);
  const fp = resolveMediaPath(media);
  if (!media || !fp || !fs.existsSync(fp)) {
    toast('File missing');
    return;
  }
  closeAlbumLightbox();
  const url = fileUrl(fp);
  const box = document.createElement('div');
  box.id = 'album-lightbox';
  box.innerHTML = `
    <div class="album-lightbox-top">
      <div class="album-lightbox-title">${esc(media.name)}</div>
      <button class="ghost-btn" id="album-lightbox-close">Close</button>
    </div>
    <div class="album-lightbox-body">
      <div class="album-lightbox-main">
        <div class="album-lightbox-stage" id="album-lightbox-stage">
          ${media.type === 'video'
            ? `<video id="lightbox-video" src="${esc(url)}" autoplay></video>`
            : media.type === 'audio'
              ? `<audio src="${esc(url)}" controls autoplay></audio>`
            : `<img id="lightbox-image" src="${esc(url)}" draggable="false">`}
        </div>
        ${media.type === 'video' ? `
          <div class="lightbox-player bottom-player game-video-player">
            <div class="lightbox-timeline-row">
              <span id="lb-current-time" class="t-time">0:00</span>
              <input id="lb-video-range" class="lightbox-video-range" type="range" min="0" max="1000" value="0">
              <span id="lb-total-time" class="t-time">0:00</span>
            </div>
            <div class="lightbox-controls-row">
              <div class="lightbox-frame-tools">
                <button class="mini-btn" id="lb-prev-frame">-1F</button>
                <button class="mini-btn play-btn" id="lb-play-toggle">Play</button>
                <button class="mini-btn" id="lb-next-frame">+1F</button>
                <span id="lb-frame-display">Frame 0</span>
              </div>
              <div class="lightbox-speed-tools">
                <span class="pb-label">Speed</span>
                <button class="spd lb-spd" data-speed="0.25">0.25x</button>
                <button class="spd lb-spd" data-speed="0.5">0.5x</button>
                <button class="spd lb-spd active" data-speed="1">1x</button>
                <button class="spd lb-spd" data-speed="2">2x</button>
              </div>
            </div>
          </div>` : media.type !== 'audio' ? `
          <div class="lightbox-zoom-tools">
            <button class="mini-btn" id="lb-zoom-out">-</button>
            <span id="lb-zoom-pct">100%</span>
            <button class="mini-btn" id="lb-zoom-in">+</button>
            <button class="mini-btn" id="lb-zoom-fit">Fit</button>
          </div>` : ''}
      </div>
      <aside class="lightbox-notes">
        <div class="field">
          <label class="field-label">Note</label>
          <textarea id="lightbox-note" class="text-area lightbox-note-area" placeholder="Notes...">${esc(media.description || '')}</textarea>
        </div>
      </aside>
    </div>`;
  box.onclick = e => {
    if (e.target === box) closeAlbumLightbox();
  };
  document.body.appendChild(box);
  $('album-lightbox-close').onclick = closeAlbumLightbox;
  $('lightbox-note').oninput = e => {
    media.description = e.target.value;
    media.updatedAt = now();
    markDirty();
  };
  const video = $('lightbox-video');
  if (video) {
    const range = $('lb-video-range');
    const currentTime = $('lb-current-time');
    const totalTime = $('lb-total-time');
    const frameDisplay = $('lb-frame-display');
    const formatVideoTime = seconds => {
      if (!Number.isFinite(seconds)) return '0:00';
      const mins = Math.floor(seconds / 60);
      const secs = Math.floor(seconds % 60).toString().padStart(2, '0');
      return `${mins}:${secs}`;
    };
    const syncVideoUI = () => {
      const duration = Number.isFinite(video.duration) && video.duration > 0 ? video.duration : 0;
      if (range && duration) range.value = Math.round((video.currentTime / duration) * 1000);
      if (currentTime) currentTime.textContent = formatVideoTime(video.currentTime);
      if (totalTime) totalTime.textContent = formatVideoTime(duration);
      if (frameDisplay) frameDisplay.textContent = `Frame ~${Math.floor(video.currentTime * 30)}`;
    };
    const step = dir => {
      video.pause();
      const maxTime = Number.isFinite(video.duration) && video.duration > 0 ? video.duration : video.currentTime + 1;
      video.currentTime = Math.max(0, Math.min(maxTime, video.currentTime + dir / 30));
      syncVideoUI();
    };
    $('lb-prev-frame').onclick = () => step(-1);
    $('lb-next-frame').onclick = () => step(1);
    $('lb-play-toggle').onclick = () => {
      if (video.paused) video.play().catch(() => {});
      else video.pause();
    };
    if (range) {
      range.oninput = e => {
        const duration = Number.isFinite(video.duration) && video.duration > 0 ? video.duration : 0;
        if (!duration) return;
        video.currentTime = (Number(e.target.value) / 1000) * duration;
        syncVideoUI();
      };
    }
    video.addEventListener('play', () => { $('lb-play-toggle').textContent = 'Pause'; });
    video.addEventListener('pause', () => { $('lb-play-toggle').textContent = 'Play'; });
    document.querySelectorAll('.lb-spd').forEach(btn => {
      btn.onclick = () => {
        document.querySelectorAll('.lb-spd').forEach(item => item.classList.remove('active'));
        btn.classList.add('active');
        video.playbackRate = Number(btn.dataset.speed || 1);
      };
    });
    video.addEventListener('loadedmetadata', syncVideoUI);
    video.addEventListener('timeupdate', syncVideoUI);
    syncVideoUI();
  }
  const image = $('lightbox-image');
  const stage = $('album-lightbox-stage');
  if (image && stage) {
    let zoom = 1;
    let panX = 0;
    let panY = 0;
    let panning = false;
    let px = 0;
    let py = 0;
    const apply = () => {
      image.style.transform = `translate(${panX}px, ${panY}px) scale(${zoom})`;
      const pct = $('lb-zoom-pct');
      if (pct) pct.textContent = Math.round(zoom * 100) + '%';
    };
    const fit = () => {
      const w = image.naturalWidth || image.width;
      const h = image.naturalHeight || image.height;
      if (!w || !h) return;
      zoom = Math.min((stage.clientWidth * .92) / w, (stage.clientHeight * .92) / h, 1);
      panX = 0;
      panY = 0;
      apply();
    };
    const change = delta => {
      zoom = Math.max(.1, Math.min(10, zoom + delta));
      apply();
    };
    $('lb-zoom-in').onclick = () => change(.25);
    $('lb-zoom-out').onclick = () => change(-.25);
    $('lb-zoom-fit').onclick = fit;
    stage.addEventListener('wheel', e => {
      e.preventDefault();
      change(e.deltaY < 0 ? .12 : -.12);
    }, { passive: false });
    stage.addEventListener('mousedown', e => {
      if (e.button !== 0) return;
      panning = true;
      px = e.clientX;
      py = e.clientY;
    });
    const onMove = e => {
      if (!panning) return;
      panX += e.clientX - px;
      panY += e.clientY - py;
      px = e.clientX;
      py = e.clientY;
      apply();
    };
    const onUp = () => { panning = false; };
    document.addEventListener('mousemove', onMove);
    document.addEventListener('mouseup', onUp);
    image.onload = fit;
    fit();
  }
}

function closeAlbumLightbox() {
  const old = $('album-lightbox');
  if (old) old.remove();
}

function renderTemplates() {
  stopViewer();
  const main = $('main');
  main.innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Templates</h1>
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
      <input class="text-input tmpl-title" value="${esc(template.title)}" placeholder="Question">
      <textarea class="text-area tmpl-prompt compact-prompt" placeholder="Prompt">${esc(template.prompt)}</textarea>
      <label class="check-wrap compact-check"><input type="checkbox" class="tmpl-enabled" ${template.enabled !== false ? 'checked' : ''}> On</label>
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

function renderProjects() {
  stopViewer();
  hidePlayback();
  S.projects = S.projects.map(ensureProjectShape);
  const project = getActiveProject();
  if (project) renderProjectWorkspace(project);
  else renderProjectLibrary();
}

function renderProjectLibrary() {
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">My Projects</h1>
        </div>
        <div class="head-actions">
          <input class="text-input search-input" id="project-search" value="${esc(S.projectSearch || '')}" placeholder="Search">
          <button class="inline-btn" id="new-project">+ Project</button>
        </div>
      </div>
      <div class="screen-scroll" id="project-library-body"></div>
    </section>`;

  $('new-project').onclick = createProjectFlow;
  $('project-search').oninput = e => {
    S.projectSearch = e.target.value;
    scheduleScrollRestore();
    renderProjectCards();
  };
  renderProjectCards();
}

function renderProjectCards() {
  const body = $('project-library-body');
  if (!body) return;
  if (!S.projects.length) {
    body.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">No Projects</div>
          <button class="inline-btn" id="empty-new-project">+ Project</button>
        </div>
      </div>`;
    $('empty-new-project').onclick = createProjectFlow;
    return;
  }

  const projects = [...S.projects]
    .filter(project => {
      const parts = [
        project.title,
        project.description,
        ...(project.doc?.blocks || []).flatMap(block => [block.title, block.text, block.caption]),
        ...(project.notes?.blocks || []).flatMap(block => [block.title, block.text, block.caption]),
      ];
      (project.milestones || []).forEach(milestone => {
        parts.push(milestone.title);
        (milestone.boards || []).forEach(board => {
          parts.push(board.title);
          KANBAN_COLUMNS.forEach(([key]) => {
            (board.columns?.[key] || []).forEach(task => parts.push(task.title, task.notes));
          });
        });
      });
      return searchMatches(parts, S.projectSearch);
    })
    .sort((a, b) => String(b.updatedAt || '').localeCompare(String(a.updatedAt || '')));

  if (!projects.length) {
    body.innerHTML = '<div class="empty-state"><div class="empty-box"><div class="empty-title">No matches</div></div></div>';
    return;
  }

  body.innerHTML = '<div class="projects-grid" id="projects-grid"></div>';
  const grid = $('projects-grid');
  projects.forEach(project => {
    const stats = project.milestones.reduce((acc, milestone) => {
      const item = milestoneStats(milestone);
      acc.done += item.done;
      acc.total += item.total;
      return acc;
    }, { done: 0, total: 0 });
    const pct = stats.total ? Math.round((stats.done / stats.total) * 100) : 0;
    const card = document.createElement('button');
    card.className = 'project-card';
    card.innerHTML = `
      <span class="project-card-title">${esc(project.title)}</span>
      <span class="progress-track"><span style="width:${pct}%"></span></span>
      <span class="card-sub">${stats.done} / ${stats.total} done</span>`;
    card.onclick = () => openProjectWorkspace(project.id);
    grid.appendChild(card);
  });
}

function createProjectFlow() {
  askText('New Project', '', 'Create', title => {
    const project = ensureProjectShape({
      id: 'pr_' + uid(),
      title,
      description: '',
      doc: { blocks: [createTextBlock('')] },
      notes: { blocks: [] },
      milestones: [createMilestone('Milestone 1')],
      createdAt: now(),
      updatedAt: now(),
    });
    S.projects.push(project);
    openProjectWorkspace(project.id);
    markDirty();
  });
}

function openProjectWorkspace(projectId, tab = S.activeProjectTab || 'doc', options = {}) {
  const project = S.projects.find(item => item.id === projectId);
  if (!project) return;
  ensureProjectShape(project);
  if (!options.skipHistory && (S.view !== 'projects' || S.activeProjectId !== projectId || S.activeProjectTab !== tab)) pushRoute();
  S.view = 'projects';
  S.activeProjectId = project.id;
  S.activeProjectTab = tab;
  S.activeMilestoneId = project.activeMilestoneId || project.milestones[0]?.id || null;
  const milestone = getActiveMilestone(project);
  S.activeKanbanBoardId = milestone?.activeBoardId || milestone?.boards[0]?.id || null;
  renderApp();
}

function renderProjectWorkspace(project) {
  ensureProjectShape(project);
  const tabs = [
    ['doc', 'Design Doc'],
    ['notes', 'Notes'],
    ['images', 'Images'],
    ['videos', 'Video'],
    ['audio', 'Audio'],
    ['kanban', 'Kanban'],
  ];

  $('main').innerHTML = `
    <section class="game-workspace project-workspace">
      <div class="game-header">
        <div class="game-top">
          <div class="game-main-row">
            <input id="project-title" class="game-title-input" value="${esc(project.title)}" spellcheck="false">
          </div>
          <div class="head-actions">
            <button class="ghost-btn" id="project-back">Projects</button>
            <button class="danger-btn" id="delete-project">Delete</button>
          </div>
        </div>
        <div class="tabs">
          ${tabs.map(([id, label]) => `<button class="tab-btn ${S.activeProjectTab === id ? 'active' : ''}" data-project-tab="${id}">${label}</button>`).join('')}
        </div>
      </div>
      <div class="tab-content" id="project-tab-content"></div>
    </section>`;

  $('project-back').onclick = () => {
    if (!goBack()) {
      S.activeProjectId = null;
      renderProjects();
    }
  };
  $('delete-project').onclick = () => {
    if (!confirm(`Delete project "${project.title}"?`)) return;
    S.projects = S.projects.filter(item => item.id !== project.id);
    S.media = S.media.filter(media => media.gameId !== project.id);
    S.activeProjectId = null;
    markDirty();
    renderProjects();
  };
  $('project-title').oninput = e => {
    project.title = e.target.value;
    touchProject(project);
    markDirty();
  };
  document.querySelectorAll('[data-project-tab]').forEach(btn => {
    btn.onclick = () => {
      if (S.activeProjectTab !== btn.dataset.projectTab) pushRoute();
      S.activeProjectTab = btn.dataset.projectTab;
      renderProjectWorkspace(project);
    };
  });

  if (S.activeProjectTab === 'kanban') renderProjectKanban(project);
  else if (S.activeProjectTab === 'notes') renderProjectNotes(project);
  else if (S.activeProjectTab === 'images') renderProjectMediaTab(project, 'photo');
  else if (S.activeProjectTab === 'videos') renderProjectMediaTab(project, 'video');
  else if (S.activeProjectTab === 'audio') renderProjectMediaTab(project, 'sound');
  else renderProjectDoc(project);
}

function renderProjectDoc(project) {
  const content = $('project-tab-content');
  content.innerHTML = `
    <div class="tab-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">Design Doc</div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="project-doc-text">+ Text</button>
          <button class="ghost-btn" id="project-doc-photo">+ Photo</button>
        </div>
      </div>
      ${blockCategoryControlsHTML(project.doc, 'project-doc')}
      <div class="notes-list" id="project-doc-blocks"></div>
    </div>`;

  bindBlockCategoryControls(project.doc, 'project-doc', shouldRender => {
    touchProject(project);
    markDirty();
    if (shouldRender) renderProjectDoc(project);
  });
  $('project-doc-text').onclick = () => {
    const block = createTextBlock();
    block.categoryId = getActiveBlockCategory(project.doc).id;
    project.doc.blocks.push(block);
    touchProject(project);
    markDirty();
    renderProjectDoc(project);
  };
  $('project-doc-photo').onclick = () => addProjectDocMedia(project);
  renderEditableBlocks($('project-doc-blocks'), project.doc.blocks, {
    ownerName: 'doc',
    onChange: () => {
      touchProject(project);
      markDirty();
    },
    onDelete: block => {
      project.doc.blocks = project.doc.blocks.filter(item => item.id !== block.id);
      touchProject(project);
      markDirty();
      renderProjectDoc(project);
    },
    onReorder: () => {
      touchProject(project);
      markDirty();
      renderProjectDoc(project);
    },
  }, { categoryId: getActiveBlockCategory(project.doc).id });
}

async function addProjectDocMedia(project) {
  const files = await pickMediaFiles('photo');
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, project.id, 'photo', 'projectDoc');
    if (media) project.doc.blocks.push({
      id: uid(),
      type: 'media',
      mediaId: media.id,
      title: media.name,
      caption: '',
      importance: 'common',
      categoryId: getActiveBlockCategory(project.doc).id,
      height: 270,
      createdAt: now(),
      updatedAt: now(),
    });
  });
  touchProject(project);
  markDirty();
  renderProjectDoc(project);
}

function renderProjectNotes(project) {
  const content = $('project-tab-content');
  content.innerHTML = `
    <div class="tab-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">Notes</div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="project-note-text">+ Text</button>
          <button class="ghost-btn" id="project-note-photo">+ Photo</button>
        </div>
      </div>
      ${blockCategoryControlsHTML(project.notes, 'project-note')}
      <div class="notes-list" id="project-note-blocks"></div>
    </div>`;

  bindBlockCategoryControls(project.notes, 'project-note', shouldRender => {
    touchProject(project);
    markDirty();
    if (shouldRender) renderProjectNotes(project);
  });
  $('project-note-text').onclick = () => {
    const block = createTextBlock();
    block.categoryId = getActiveBlockCategory(project.notes).id;
    project.notes.blocks.push(block);
    touchProject(project);
    markDirty();
    renderProjectNotes(project);
  };
  $('project-note-photo').onclick = () => addProjectNoteMedia(project);
  renderEditableBlocks($('project-note-blocks'), project.notes.blocks, {
    ownerName: 'project-note',
    onChange: () => {
      touchProject(project);
      markDirty();
    },
    onDelete: block => {
      project.notes.blocks = project.notes.blocks.filter(item => item.id !== block.id);
      touchProject(project);
      markDirty();
      renderProjectNotes(project);
    },
    onReorder: () => {
      touchProject(project);
      markDirty();
      renderProjectNotes(project);
    },
  }, { categoryId: getActiveBlockCategory(project.notes).id });
}

async function addProjectNoteMedia(project) {
  const files = await pickMediaFiles('photo');
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, project.id, 'photo', 'projectNote');
    if (media) project.notes.blocks.push({
      id: uid(),
      type: 'media',
      mediaId: media.id,
      title: media.name,
      caption: '',
      importance: 'common',
      categoryId: getActiveBlockCategory(project.notes).id,
      height: 270,
      createdAt: now(),
      updatedAt: now(),
    });
  });
  touchProject(project);
  markDirty();
  renderProjectNotes(project);
}

function renderProjectMediaTab(project, kind) {
  const label = kind === 'video' ? 'Video' : kind === 'sound' ? 'Audio' : 'Images';
  const content = $('project-tab-content');
  const activeCategory = getActiveMediaCategory(project, kind);
  const items = getProjectMedia(project.id, kind)
    .filter(item => item.categoryId === activeCategory.id);
  content.innerHTML = `
    <div class="tab-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">${label}</div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="project-sort-media">Sort importance</button>
          <button class="ghost-btn" id="project-add-media">+ ${label}</button>
        </div>
      </div>
      ${mediaCategoryControlsHTML(project, kind, 'project-media', 'projectMedia')}
      <div class="project-media-grid" id="project-media-grid"></div>
    </div>`;

  $('project-add-media').onclick = () => addProjectMedia(project, kind);
  $('project-sort-media').onclick = () => {
    const sortable = getProjectMedia(project.id, kind).filter(item => item.categoryId === activeCategory.id);
    sortMediaByImportance(sortable);
    touchProject(project);
    markDirty();
    renderProjectMediaTab(project, kind);
  };
  bindMediaCategoryControls(project, kind, 'project-media', 'projectMedia', () => {
    S.activeMediaId = null;
    touchProject(project);
    markDirty();
    renderProjectMediaTab(project, kind);
  });
  const grid = $('project-media-grid');
  if (!items.length) {
    grid.innerHTML = `<button class="album-drop-card fixed-drop" id="project-empty-media">+ ${esc(label)}</button>`;
    $('project-empty-media').onclick = () => addProjectMedia(project, kind);
    return;
  }
  items.forEach(item => {
    const card = document.createElement('div');
    card.className = 'album-photo-card fixed-media-card';
    card.innerHTML = `
      <button class="album-photo-open">${mediaPreviewHTML(item, true)}</button>
      <div class="album-photo-foot">
        ${importanceBadgeHTML(item.importance)}
        <input class="album-photo-title" value="${esc(item.name)}">
        <button class="mini-btn remove-project-media">x</button>
      </div>`;
    card.querySelector('.album-photo-open').onclick = () => openAlbumPhoto(item.id);
    bindImportanceTriggers(card, () => item.importance, value => {
      item.importance = value;
      item.updatedAt = now();
      touchProject(project);
      markDirty();
      renderProjectMediaTab(project, kind);
    });
    card.querySelector('.album-photo-title').oninput = e => {
      item.name = e.target.value;
      item.updatedAt = now();
      touchProject(project);
      markDirty();
    };
    card.querySelector('.remove-project-media').onclick = () => {
      if (!confirm(`Remove "${item.name}"?`)) return;
      S.media = S.media.filter(media => media.id !== item.id);
      touchProject(project);
      markDirty();
      renderProjectMediaTab(project, kind);
    };
    bindSortableIdCard(card, item.id, 'application/x-refboard-project-media', (draggedId, beforeId) => {
      if (reorderMediaBefore(project.id, 'projectMedia', kind, activeCategory.id, draggedId, beforeId)) {
        touchProject(project);
        markDirty();
        renderProjectMediaTab(project, kind);
      }
    });
    grid.appendChild(card);
  });
  const add = document.createElement('button');
  add.className = 'album-drop-card fixed-drop';
  add.textContent = `+ ${label}`;
  add.onclick = () => addProjectMedia(project, kind);
  grid.appendChild(add);
  const spacer = document.createElement('div');
  spacer.className = 'media-grid-spacer';
  spacer.addEventListener('dragover', e => {
    e.preventDefault();
    if (hasMoveDragType(e, 'application/x-refboard-project-media')) spacer.classList.add('drag-over');
  });
  spacer.addEventListener('dragleave', () => spacer.classList.remove('drag-over'));
  spacer.addEventListener('drop', e => {
    e.preventDefault();
    spacer.classList.remove('drag-over');
    const draggedId = getDraggedId(e, 'application/x-refboard-project-media');
    if (draggedId && reorderMediaBefore(project.id, 'projectMedia', kind, activeCategory.id, draggedId, null)) {
      touchProject(project);
      markDirty();
      renderProjectMediaTab(project, kind);
    }
  });
  grid.appendChild(spacer);
}

async function addProjectMedia(project, kind) {
  const files = await pickMediaFiles(kind);
  if (!files.length) return;
  files.forEach(fp => registerMediaFile(fp, project.id, kind, 'projectMedia'));
  touchProject(project);
  markDirty();
  renderProjectMediaTab(project, kind);
  toast(`Added: ${files.length}`);
}

function renderProjectKanban(project) {
  const content = $('project-tab-content');
  let milestone = getActiveMilestone(project);
  if (!milestone) {
    milestone = createMilestone('Milestone 1');
    project.milestones.push(milestone);
  }
  ensureMilestoneShape(milestone);
  project.activeMilestoneId = milestone.id;
  S.activeMilestoneId = milestone.id;
  if (!getActiveKanbanBoard(milestone)) {
    S.activeKanbanBoardId = milestone.boards[0]?.id || null;
  }

  const stats = milestoneStats(milestone);
  content.innerHTML = `
    <div class="kanban-workarea">
      <div class="kanban-control-row">
        <button class="milestone-select" id="milestone-select">
          <span>${esc(milestone.title)}</span>
          <span class="select-caret">v</span>
        </button>
        <button class="inline-btn" id="new-milestone">+ Milestone</button>
      </div>
      <div class="boss-progress" title="${esc(milestone.title)}">
        <div class="boss-track">
          <span style="width:${stats.pct}%"></span>
          <strong>${stats.done} / ${stats.total}</strong>
        </div>
      </div>
      <section class="kanban-main" id="kanban-main"></section>
    </div>`;

  $('milestone-select').onclick = e => openMilestoneMenu(e.currentTarget, project);
  $('new-milestone').onclick = () => createMilestoneFlow(project);
  renderMilestoneDetail(project, milestone);
  maybeCelebrateMilestone(project, milestone, stats);
}

function maybeCelebrateMilestone(project, milestone, stats = milestoneStats(milestone)) {
  if (!stats.total || stats.pct < 100 || milestone.celebratedAt) return;
  milestone.celebratedAt = now();
  milestone.updatedAt = now();
  touchProject(project);
  markDirty();
  showMilestoneCompleteEffect(milestone);
}

function showMilestoneCompleteEffect(milestone) {
  const old = $('milestone-complete-effect');
  if (old) old.remove();
  const effect = document.createElement('div');
  effect.id = 'milestone-complete-effect';
  effect.innerHTML = `
    <div class="complete-burst">
      <div class="complete-title">Milestone Complete</div>
      <div class="complete-name">${esc(milestone.title)}</div>
    </div>`;
  document.body.appendChild(effect);
  setTimeout(() => effect.classList.add('show'), 20);
  setTimeout(() => effect.remove(), 1900);
}

function renderMilestoneList(project) {
  const list = $('milestone-list');
  list.innerHTML = '';
  project.milestones.forEach(milestone => {
    const stats = milestoneStats(milestone);
    const row = document.createElement('button');
    row.className = 'milestone-card' + (milestone.id === S.activeMilestoneId ? ' active' : '');
    row.innerHTML = `
      <span class="milestone-row-title">${esc(milestone.title)}</span>
      <span class="progress-track"><span style="width:${stats.pct}%"></span></span>
      <span class="milestone-row-meta">${stats.done} / ${stats.total} ${stats.closed ? 'closed' : 'open'}</span>`;
    row.onclick = () => {
      S.activeMilestoneId = milestone.id;
      project.activeMilestoneId = milestone.id;
      S.activeKanbanBoardId = milestone.activeBoardId || milestone.boards[0]?.id || null;
      touchProject(project);
      markDirty();
      renderProjectWorkspace(project);
    };
    list.appendChild(row);
  });
}

function createMilestoneFlow(project) {
  askText('New Milestone', '', 'Create', title => {
    const milestone = createMilestone(title);
    project.milestones.push(milestone);
    project.activeMilestoneId = milestone.id;
    S.activeMilestoneId = milestone.id;
    S.activeKanbanBoardId = milestone.boards[0].id;
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  });
}

function renderMilestoneDetail(project, milestone) {
  const main = $('kanban-main');
  const board = getActiveKanbanBoard(milestone);
  main.innerHTML = `
    <div class="kanban-board-bar">
      <div class="kanban-board-tabs" id="kanban-board-tabs"></div>
      <div class="kanban-board-tools">
        <button class="mini-btn" id="new-kanban-board">+ Board</button>
        <button class="mini-btn danger-lite" id="delete-milestone">Delete</button>
      </div>
    </div>
    <div id="kanban-board-detail"></div>`;

  $('new-kanban-board').onclick = () => createKanbanBoardFlow(project, milestone);
  $('delete-milestone').onclick = () => {
    if (project.milestones.length <= 1) {
      toast('Keep one milestone');
      return;
    }
    if (!confirm(`Delete milestone "${milestone.title}"?`)) return;
    project.milestones = project.milestones.filter(item => item.id !== milestone.id);
    project.activeMilestoneId = project.milestones[0]?.id || null;
    S.activeMilestoneId = project.activeMilestoneId;
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  };

  renderKanbanBoardTabs(project, milestone);
  if (board) renderKanbanBoard(project, milestone, board);
}

function renderKanbanBoardTabs(project, milestone) {
  const tabs = $('kanban-board-tabs');
  tabs.innerHTML = '';
  milestone.boards.forEach(board => {
    const btn = document.createElement('button');
    btn.className = 'chip-btn' + (board.id === S.activeKanbanBoardId ? ' active' : '');
    btn.textContent = board.title;
    btn.onclick = () => {
      S.activeKanbanBoardId = board.id;
      milestone.activeBoardId = board.id;
      milestone.updatedAt = now();
      touchProject(project);
      markDirty();
      renderProjectWorkspace(project);
    };
    tabs.appendChild(btn);
  });
}

function createKanbanBoardFlow(project, milestone) {
  askText('New Board', '', 'Create', title => {
    const board = createKanbanBoard(title);
    milestone.boards.push(board);
    milestone.activeBoardId = board.id;
    S.activeKanbanBoardId = board.id;
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  });
}

function renderKanbanBoard(project, milestone, board) {
  const wrap = $('kanban-board-detail');
  wrap.innerHTML = `
    <div class="kanban-board-head compact-board-head">
      <input id="kanban-board-title" class="text-input kanban-board-title" value="${esc(board.title)}">
      <button class="mini-btn danger-lite" id="delete-kanban-board">Delete Board</button>
    </div>
    <div class="kanban-columns" id="kanban-columns"></div>`;

  $('kanban-board-title').oninput = e => {
    board.title = e.target.value;
    board.updatedAt = now();
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    renderKanbanBoardTabs(project, milestone);
  };
  $('delete-kanban-board').onclick = () => {
    if (milestone.boards.length <= 1) {
      toast('Keep one board');
      return;
    }
    if (!confirm(`Delete board "${board.title}"?`)) return;
    milestone.boards = milestone.boards.filter(item => item.id !== board.id);
    milestone.activeBoardId = milestone.boards[0]?.id || null;
    S.activeKanbanBoardId = milestone.activeBoardId;
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  };

  const columns = $('kanban-columns');
  KANBAN_COLUMNS.forEach(([key, label]) => {
    const col = document.createElement('section');
    col.className = 'kanban-column';
    const tasks = board.columns[key] || [];
    col.innerHTML = `
      <div class="kanban-column-head">
        <span>${esc(label)}</span>
        <span class="kanban-column-tools">
          <button class="column-sort-btn" data-sort-column="${esc(key)}">Sort</button>
          <span class="column-count">${tasks.length}</span>
        </span>
      </div>
      <button class="mini-add-task" data-add-task="${esc(key)}">+ Task</button>
      <div class="task-list" data-column="${esc(key)}"></div>`;
    col.querySelector('[data-add-task]').onclick = () => addTaskFlow(project, milestone, board, key);
    col.querySelector('[data-sort-column]').onclick = e => {
      e.stopPropagation();
      sortByImportance(board.columns[key]);
      board.updatedAt = now();
      milestone.updatedAt = now();
      touchProject(project);
      markDirty();
      renderProjectWorkspace(project);
    };
    const taskList = col.querySelector('.task-list');
    taskList.addEventListener('dragover', e => {
      e.preventDefault();
      col.classList.add('drag-over');
    });
    taskList.addEventListener('dragleave', () => col.classList.remove('drag-over'));
    taskList.addEventListener('drop', e => {
      e.preventDefault();
      col.classList.remove('drag-over');
      const payload = JSON.parse(e.dataTransfer.getData('application/x-refboard-task') || '{}');
      if (!payload.taskId || payload.boardId !== board.id) return;
      moveTask(project, milestone, board, payload.columnKey, payload.taskId, key);
    });
    tasks.forEach(task => taskList.appendChild(buildTaskCard(project, milestone, board, key, task)));
    columns.appendChild(col);
  });
}

function buildTaskCard(project, milestone, board, columnKey, task) {
  ensureTaskShape(task);
  const card = document.createElement('div');
  card.className = `task-card task-importance-${esc(importanceLevel(task.importance).id)}`;
  let dragging = false;
  card.draggable = true;
  card.addEventListener('dragstart', e => {
    dragging = true;
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('application/x-refboard-task', JSON.stringify({
      boardId: board.id,
      columnKey,
      taskId: task.id,
    }));
    card.classList.add('dragging');
  });
  card.addEventListener('dragend', () => {
    card.classList.remove('dragging');
    setTimeout(() => { dragging = false; }, 0);
  });
  const meta = [
    (task.notes || '').trim().slice(0, 96),
    (task.mediaIds || []).length ? `${(task.mediaIds || []).length} media` : '',
  ].filter(Boolean).join(' - ');
  card.innerHTML = `
    <div class="task-card-top">
      ${importanceBadgeHTML(task.importance)}
      <span class="task-title-btn">${esc(task.title || 'Untitled')}</span>
    </div>
    ${meta ? `<div class="task-card-meta">${esc(meta)}</div>` : ''}`;
  card.addEventListener('click', e => {
    if (dragging || e.target.closest('.rarity-badge')) return;
    openTaskNotebook(project.id, milestone.id, board.id, columnKey, task.id);
  });
  bindImportanceTriggers(card, () => task.importance, value => {
    task.importance = value;
    task.updatedAt = now();
    board.updatedAt = now();
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  });
  return card;
}

function addTaskFlow(project, milestone, board, columnKey) {
  askText('New Task', '', 'Create', title => {
    board.columns[columnKey].push(ensureTaskShape({
      id: 'task_' + uid(),
      title,
      notes: '',
      importance: columnKey === 'ideas' ? 'noted' : 'common',
      mediaIds: [],
      createdAt: now(),
      updatedAt: now(),
    }));
    board.updatedAt = now();
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  });
}

function moveTask(project, milestone, board, fromColumn, taskId, toColumn) {
  const list = board.columns[fromColumn] || [];
  const task = list.find(item => item.id === taskId);
  if (!task || !board.columns[toColumn]) return;
  board.columns[fromColumn] = list.filter(item => item.id !== taskId);
  board.columns[toColumn].push(task);
  task.updatedAt = now();
  board.updatedAt = now();
  milestone.updatedAt = now();
  touchProject(project);
  markDirty();

  const stats = milestoneStats(milestone);
  maybeCelebrateMilestone(project, milestone, stats);
  if (stats.closed) {
    const index = project.milestones.findIndex(item => item.id === milestone.id);
    const next = project.milestones.slice(index + 1).find(item => !milestoneStats(item).closed);
    if (next) {
      project.activeMilestoneId = next.id;
      S.activeMilestoneId = next.id;
      S.activeKanbanBoardId = next.activeBoardId || next.boards[0]?.id || null;
      toast('Next milestone opened');
      renderProjectWorkspace(project);
      return;
    }
  }
  renderProjectWorkspace(project);
}

function findTaskRef(projectId, milestoneId, boardId, columnKey, taskId) {
  const project = S.projects.find(item => item.id === projectId);
  const milestone = project?.milestones.find(item => item.id === milestoneId);
  const board = milestone?.boards.find(item => item.id === boardId);
  const task = board?.columns[columnKey]?.find(item => item.id === taskId);
  if (!project || !milestone || !board || !task) return null;
  return { project, milestone, board, task };
}

function openTaskNotebook(projectId, milestoneId, boardId, columnKey, taskId) {
  const ref = findTaskRef(projectId, milestoneId, boardId, columnKey, taskId);
  if (!ref) return;
  closeTaskNotebook();
  const { project, milestone, board, task } = ref;
  const modal = document.createElement('div');
  modal.id = 'task-notebook';
  modal.innerHTML = `
    <div class="task-notebook-box">
      <div class="task-notebook-head">
        <input id="task-modal-title" class="section-title-input" value="${esc(task.title)}">
        <div class="head-actions">
          ${importanceBadgeHTML(task.importance)}
          <button class="ghost-btn" id="task-modal-photo">+ Photo</button>
          <button class="danger-btn" id="task-modal-delete">Delete</button>
          <button class="ghost-btn" id="task-modal-close">Close</button>
        </div>
      </div>
      <textarea id="task-modal-notes" class="text-area task-modal-notes" placeholder="Task notes...">${esc(task.notes || '')}</textarea>
      <div class="task-media-grid" id="task-media-grid">
        ${(task.mediaIds || []).map(id => mediaChipHTML(id, id, false)).join('')}
      </div>
    </div>`;
  document.body.appendChild(modal);

  $('task-modal-close').onclick = closeTaskNotebook;
  modal.onclick = e => {
    if (e.target === modal) closeTaskNotebook();
  };
  $('task-modal-title').oninput = e => {
    task.title = e.target.value;
    task.updatedAt = now();
    board.updatedAt = now();
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    renderProjectWorkspace(project);
  };
  bindImportanceTriggers(modal, () => task.importance, value => {
    task.importance = value;
    task.updatedAt = now();
    touchProject(project);
    markDirty();
    closeTaskNotebook();
    renderProjectWorkspace(project);
    openTaskNotebook(project.id, milestone.id, board.id, columnKey, task.id);
  });
  $('task-modal-notes').oninput = e => {
    task.notes = e.target.value;
    task.updatedAt = now();
    touchProject(project);
    markDirty();
  };
  $('task-modal-photo').onclick = () => addTaskPhoto(project.id, milestone.id, board.id, columnKey, task.id);
  $('task-modal-delete').onclick = () => {
    if (!confirm(`Delete task "${task.title}"?`)) return;
    board.columns[columnKey] = board.columns[columnKey].filter(item => item.id !== task.id);
    board.updatedAt = now();
    milestone.updatedAt = now();
    touchProject(project);
    markDirty();
    closeTaskNotebook();
    renderProjectWorkspace(project);
  };
}

function closeTaskNotebook() {
  closeImportanceMenu();
  const modal = $('task-notebook');
  if (modal) modal.remove();
}

async function addTaskPhoto(projectId, milestoneId, boardId, columnKey, taskId) {
  const ref = findTaskRef(projectId, milestoneId, boardId, columnKey, taskId);
  if (!ref) return;
  const files = await pickMediaFiles('photo');
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, ref.project.id, 'photo', 'projectTask');
    if (media) ref.task.mediaIds.push(media.id);
  });
  ref.task.updatedAt = now();
  ref.board.updatedAt = now();
  ref.milestone.updatedAt = now();
  touchProject(ref.project);
  markDirty();
  openTaskNotebook(projectId, milestoneId, boardId, columnKey, taskId);
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
    ['photos', 'Images'],
    ['videos', 'Video'],
    ['sound', 'Audio'],
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

  $('game-back').onclick = () => {
    if (!goBack()) setView('library', { skipHistory: true });
  };
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
      if (S.activeTab !== btn.dataset.tab) pushRoute();
      S.activeTab = btn.dataset.tab;
      S.activeMediaId = null;
      renderGameWorkspace();
    };
  });

  if (S.activeTab === 'notes') renderNotesTab(game);
  else if (S.activeTab === 'photos') renderGameMediaGridTab(game, 'photo');
  else if (S.activeTab === 'videos') renderGameMediaGridTab(game, 'video');
  else if (S.activeTab === 'sound') renderMediaTab(game, 'sound');
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
  game.notes = ensureBlockContainerShape(game.notes);
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
          <button class="ghost-btn" id="add-note-sound">+ Sound</button>
          <button class="ghost-btn" id="add-note-video">+ Video</button>
        </div>
      </div>
      ${blockCategoryControlsHTML(game.notes, 'game-note')}
      <div class="notes-list" id="notes-list"></div>
    </div>`;

  bindBlockCategoryControls(game.notes, 'game-note', shouldRender => {
    touchGame(game.id);
    markDirty();
    if (shouldRender) renderNotesTab(game);
  });
  $('add-note-text').onclick = () => {
    game.notes = ensureBlockContainerShape(game.notes);
    const block = createTextBlock();
    block.categoryId = getActiveBlockCategory(game.notes).id;
    game.notes.blocks.push(block);
    touchGame(game.id);
    markDirty();
    renderNotesTab(game);
  };
  $('add-note-image').onclick = () => addNoteMedia(game, 'photo');
  $('add-note-sound').onclick = () => addNoteMedia(game, 'sound');
  $('add-note-video').onclick = () => addNoteMedia(game, 'video');

  renderEditableBlocks($('notes-list'), game.notes.blocks, {
    ownerName: 'game-note',
    onChange: () => {
      touchGame(game.id);
      markDirty();
    },
    onDelete: block => {
      game.notes.blocks = game.notes.blocks.filter(item => item.id !== block.id);
      touchGame(game.id);
      markDirty();
      renderNotesTab(game);
    },
    onReorder: () => {
      touchGame(game.id);
      markDirty();
      renderNotesTab(game);
    },
  }, { categoryId: getActiveBlockCategory(game.notes).id });
}

function renderMediaTab(game, kind) {
  const label = kind === 'video' ? 'Video' : kind === 'sound' ? 'Audio' : 'Images';
  const activeCategory = getActiveMediaCategory(game, kind);

  $('tab-content').innerHTML = `
    <div class="media-workspace">
      <aside class="media-panel">
        <div class="media-panel-head">
          <div>
            <div class="pane-label">${label}</div>
          </div>
          <div class="panel-mini-actions">
            <button class="mini-btn" id="sort-media-btn">Sort</button>
            <button class="mini-btn" id="add-media-btn">+</button>
          </div>
        </div>
        <div class="media-panel-category">
          ${mediaCategoryControlsHTML(game, kind, 'media-panel', 'game')}
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
          <audio id="audio-viewer" class="hidden" controls></audio>
        </div>
        <div id="zoom-hud" class="${kind === 'sound' ? 'hidden' : ''}">
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

  bindMediaCategoryControls(game, kind, 'media-panel', 'game', () => {
    S.activeMediaId = null;
    touchGame(game.id);
    markDirty();
    renderMediaTab(game, kind);
  });
  $('add-media-btn').onclick = () => addMediaToActiveGame(kind);
  $('sort-media-btn').onclick = () => {
    const sortable = getGameMedia(game.id, kind).filter(item => item.categoryId === activeCategory.id);
    sortMediaByImportance(sortable);
    touchGame(game.id);
    markDirty();
    renderMediaList(game, kind);
  };
  bindViewerEvents(kind);
  renderMediaList(game, kind);

  const selected = getMediaById(S.activeMediaId);
  if (selected && selected.gameId === game.id && selected.kind === kind) loadMedia(selected);
  else {
    clearViewer();
    hidePlayback();
  }
}

function renderGameMediaGridTab(game, kind) {
  hidePlayback();
  const label = kind === 'video' ? 'Video' : 'Images';
  const activeCategory = getActiveMediaCategory(game, kind);
  const items = getGameMedia(game.id, kind)
    .filter(item => item.categoryId === activeCategory.id);

  $('tab-content').innerHTML = `
    <div class="tab-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">${label}</div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="game-sort-media">Sort importance</button>
          <button class="ghost-btn" id="game-add-media">+ ${label}</button>
        </div>
      </div>
      ${mediaCategoryControlsHTML(game, kind, 'game-media', 'game')}
      <div class="project-media-grid" id="game-media-grid"></div>
    </div>`;

  bindMediaCategoryControls(game, kind, 'game-media', 'game', () => {
    S.activeMediaId = null;
    touchGame(game.id);
    markDirty();
    renderGameMediaGridTab(game, kind);
  });
  $('game-add-media').onclick = () => addMediaToActiveGame(kind);
  $('game-sort-media').onclick = () => {
    const sortable = getGameMedia(game.id, kind).filter(item => item.categoryId === activeCategory.id);
    sortMediaByImportance(sortable);
    touchGame(game.id);
    markDirty();
    renderGameMediaGridTab(game, kind);
  };

  const grid = $('game-media-grid');
  if (!items.length) {
    grid.innerHTML = `<button class="album-drop-card fixed-drop" id="game-empty-media">+ ${esc(label)}</button>`;
    $('game-empty-media').onclick = () => addMediaToActiveGame(kind);
    return;
  }

  items.forEach(item => {
    const card = document.createElement('div');
    card.className = 'album-photo-card fixed-media-card';
    card.innerHTML = `
      <button class="album-photo-open">${mediaPreviewHTML(item, true)}</button>
      <div class="album-photo-foot">
        ${importanceBadgeHTML(item.importance)}
        <input class="album-photo-title" value="${esc(item.name)}">
        <button class="mini-btn remove-game-media">x</button>
      </div>`;
    card.querySelector('.album-photo-open').onclick = () => openAlbumPhoto(item.id);
    bindImportanceTriggers(card, () => item.importance, value => {
      item.importance = value;
      item.updatedAt = now();
      touchGame(game.id);
      markDirty();
      renderGameMediaGridTab(game, kind);
    });
    card.querySelector('.album-photo-title').oninput = e => {
      item.name = e.target.value;
      item.updatedAt = now();
      touchGame(game.id);
      markDirty();
    };
    card.querySelector('.remove-game-media').onclick = () => removeGameMediaFromGrid(game, item.id, kind);
    bindSortableIdCard(card, item.id, 'application/x-refboard-game-grid-media', (draggedId, beforeId) => {
      if (reorderMediaBefore(game.id, 'game', kind, activeCategory.id, draggedId, beforeId)) {
        touchGame(game.id);
        markDirty();
        renderGameMediaGridTab(game, kind);
      }
    });
    grid.appendChild(card);
  });

  const add = document.createElement('button');
  add.className = 'album-drop-card fixed-drop';
  add.textContent = `+ ${label}`;
  add.onclick = () => addMediaToActiveGame(kind);
  grid.appendChild(add);
  const spacer = document.createElement('div');
  spacer.className = 'media-grid-spacer';
  spacer.addEventListener('dragover', e => {
    e.preventDefault();
    if (hasMoveDragType(e, 'application/x-refboard-game-grid-media')) spacer.classList.add('drag-over');
  });
  spacer.addEventListener('dragleave', () => spacer.classList.remove('drag-over'));
  spacer.addEventListener('drop', e => {
    e.preventDefault();
    spacer.classList.remove('drag-over');
    const draggedId = getDraggedId(e, 'application/x-refboard-game-grid-media');
    if (draggedId && reorderMediaBefore(game.id, 'game', kind, activeCategory.id, draggedId, null)) {
      touchGame(game.id);
      markDirty();
      renderGameMediaGridTab(game, kind);
    }
  });
  grid.appendChild(spacer);
}

function removeGameMediaFromGrid(game, mediaId, kind) {
  const media = getMediaById(mediaId);
  if (!media) return;
  if (!confirm(`Remove "${media.name}"?`)) return;
  S.media = S.media.filter(item => item.id !== mediaId);
  if (game.coverMediaId === mediaId) game.coverMediaId = null;
  if (game.iconMediaId === mediaId) game.iconMediaId = null;
  touchGame(game.id);
  markDirty();
  renderGameMediaGridTab(game, kind);
}

function renderMediaList(game, kind) {
  const list = $('media-list');
  const activeCategory = getActiveMediaCategory(game, kind);
  const items = getGameMedia(game.id, kind)
    .filter(item => item.categoryId === activeCategory.id);
  list.innerHTML = '';

  items.forEach(item => {
    const thumb = document.createElement('div');
    thumb.className = 'media-thumb' + (S.activeMediaId === item.id ? ' active' : '');
    thumb.innerHTML = `
      ${mediaPreviewHTML(item, true)}
      <span class="media-badge">${esc(item.type.toUpperCase())}</span>
      ${importanceBadgeHTML(item.importance)}
      <div class="media-thumb-title">${esc(item.name)}</div>`;
    bindImportanceTriggers(thumb, () => item.importance, value => {
      item.importance = value;
      item.updatedAt = now();
      touchGame(game.id);
      markDirty();
      renderMediaList(game, kind);
    });
    thumb.onclick = () => {
      S.activeMediaId = item.id;
      renderMediaList(game, kind);
      loadMedia(item);
    };
    bindSortableIdCard(thumb, item.id, 'application/x-refboard-game-media', (draggedId, beforeId) => {
      if (reorderMediaBefore(game.id, 'game', kind, activeCategory.id, draggedId, beforeId)) {
        touchGame(game.id);
        markDirty();
        renderMediaList(game, kind);
      }
    });
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
  const spacer = document.createElement('div');
  spacer.className = 'media-grid-spacer';
  spacer.addEventListener('dragover', e => {
    e.preventDefault();
    if (hasMoveDragType(e, 'application/x-refboard-game-media')) spacer.classList.add('drag-over');
  });
  spacer.addEventListener('dragleave', () => spacer.classList.remove('drag-over'));
  spacer.addEventListener('drop', e => {
    e.preventDefault();
    spacer.classList.remove('drag-over');
    const draggedId = getDraggedId(e, 'application/x-refboard-game-media');
    if (draggedId && reorderMediaBefore(game.id, 'game', kind, activeCategory.id, draggedId, null)) {
      touchGame(game.id);
      markDirty();
      renderMediaList(game, kind);
    }
  });
  list.appendChild(spacer);
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

function noteMediaPreviewHTML(block) {
  const media = getMediaById(block.mediaId);
  if (!media) return '<div class="note-media-preview missing">Missing</div>';
  return `<button class="note-media-open" style="height:${esc(block.height || 270)}px">${mediaPreviewHTML(media, true)}</button>`;
}

function mediaPreviewHTML(media, compact = false) {
  const fp = resolveMediaPath(media);
  const url = fileUrl(fp);
  if (!fp || !fs.existsSync(fp)) return '<span>Missing</span>';
  if (media.type === 'video') return `<video src="${esc(url)}" muted preload="metadata"></video>`;
  if (media.type === 'audio') return '<span class="audio-preview">Sound</span>';
  if (media.type === 'gif' || media.type === 'image') return `<img src="${esc(url)}" draggable="false">`;
  return compact ? '<span>Media</span>' : `<span>${esc(media.type)}</span>`;
}

function mediaKindLabel(kind) {
  if (kind === 'photo') return 'photo';
  if (kind === 'video') return 'video';
  if (kind === 'sound') return 'sound';
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
    if (media) answer.blocks.push({ id: uid(), type: 'media', mediaId: media.id, title: media.name, caption: '', importance: 'common' });
  });
  answer.updatedAt = now();
  touchGame(game.id);
  markDirty();
  renderQuestionsTab(game);
}

async function addNoteMedia(game, kind) {
  game.notes = ensureBlockContainerShape(game.notes);
  const files = await pickMediaFiles(kind);
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, game.id, kind);
    if (media) game.notes.blocks.push({
      id: uid(),
      type: 'media',
      mediaId: media.id,
      title: media.name,
      caption: '',
      importance: 'common',
      categoryId: getActiveBlockCategory(game.notes).id,
      height: 270,
    });
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
  if (kind === 'photo' || kind === 'video') renderGameMediaGridTab(game, kind);
  else renderMediaTab(game, kind);
  toast(`Added: ${files.length}`);
}

function addDroppedFiles(fileList, kind) {
  const game = getActiveGame();
  if (!game) return;
  const files = Array.from(fileList || []).map(f => f.path).filter(Boolean);
  const valid = files.filter(fp => kindAllowsFile(kind, fp));
  if (!valid.length) {
    toast(kind === 'video' ? 'Use video or GIF' : kind === 'sound' ? 'Use audio' : 'Use image or GIF');
    return;
  }
  valid.forEach(fp => registerMediaFile(fp, game.id, kind));
  touchGame(game.id);
  markDirty();
  if (kind === 'photo' || kind === 'video') renderGameMediaGridTab(game, kind);
  else renderMediaTab(game, kind);
  toast(`Added: ${valid.length}`);
}

async function pickMediaFiles(kind) {
  const extensions = kind === 'photo'
    ? ['png', 'jpg', 'jpeg', 'webp', 'bmp', 'svg', 'gif']
    : kind === 'video'
      ? ['mp4', 'webm', 'mov', 'mkv', 'gif']
      : kind === 'sound'
        ? ['mp3', 'wav', 'ogg', 'flac', 'm4a', 'aac']
        : ['png', 'jpg', 'jpeg', 'webp', 'bmp', 'svg', 'gif', 'mp4', 'webm', 'mov', 'mkv', 'mp3', 'wav', 'ogg', 'flac', 'm4a', 'aac'];
  const result = await ipcRenderer.invoke('dialog:open', {
    title: 'Add media',
    filters: [{ name: 'Media', extensions }],
    properties: ['openFile', 'multiSelections'],
  });
  if (result.canceled || !result.filePaths?.length) return [];
  return result.filePaths.filter(fp => kind === 'mixed' || kindAllowsFile(kind, fp));
}

function registerMediaFile(fp, gameId, kind, scope = 'game') {
  if (!fp || !fs.existsSync(fp)) return null;
  if (!kindAllowsFile(kind, fp)) return null;
  const id = 'm_' + uid();
  const type = inferMediaType(fp);
  const game = S.games.find(item => item.id === gameId);
  const project = S.projects.find(item => item.id === gameId);
  const projectMediaOrder = S.media.filter(item => item.gameId === gameId && item.scope === scope && item.kind === kind).length;
  const item = {
    id,
    gameId,
    scope,
    kind,
    type,
    name: nodePath.basename(fp, nodePath.extname(fp)),
    path: fp,
    originalPath: fp,
    description: '',
    tags: [],
    importance: 'common',
    order: projectMediaOrder,
    categoryId: scope === 'game' && game
      ? getActiveMediaCategory(game, kind).id
      : scope === 'projectMedia' && project
        ? getActiveMediaCategory(project, kind).id
        : 'imgcat_default',
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
  S.dailyNotes.forEach(note => {
    note.blocks = (note.blocks || []).filter(block => block.mediaId !== mediaId);
  });
  S.photoBoards.forEach(board => {
    board.photoIds = (board.photoIds || []).filter(id => id !== mediaId);
  });
  S.projects.forEach(project => {
    if (project.doc?.blocks) project.doc.blocks = project.doc.blocks.filter(block => block.mediaId !== mediaId);
    if (project.notes?.blocks) project.notes.blocks = project.notes.blocks.filter(block => block.mediaId !== mediaId);
    (project.milestones || []).forEach(milestone => {
      (milestone.boards || []).forEach(board => {
        Object.values(board.columns || {}).forEach(tasks => {
          (tasks || []).forEach(task => {
            task.mediaIds = (task.mediaIds || []).filter(id => id !== mediaId);
          });
        });
      });
    });
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
  if (['.mp3', '.wav', '.ogg', '.flac', '.m4a', '.aac'].includes(ext)) return 'audio';
  return 'image';
}

function kindAllowsFile(kind, fp) {
  const type = inferMediaType(fp);
  if (kind === 'mixed') return true;
  if (kind === 'icon') return type === 'image' || type === 'gif';
  if (kind === 'photo') return type === 'image' || type === 'gif';
  if (kind === 'video') return type === 'video' || type === 'gif';
  if (kind === 'sound') return type === 'audio';
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
    dailyNotes: S.dailyNotes,
    photoBoards: S.photoBoards,
    projects: S.projects,
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
  navStack = [];
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

  if (data.type === APP_TYPE && Number(data.version || 0) >= 2) {
    next.questionTemplates = Array.isArray(data.questionTemplates) && data.questionTemplates.length
      ? data.questionTemplates
      : defaultQuestionTemplates();
    next.games = Array.isArray(data.games) ? data.games.map(ensureGameShape) : [];
    next.dailyNotes = Array.isArray(data.dailyNotes) ? data.dailyNotes.map(ensureDailyNoteShape) : [];
    next.photoBoards = Array.isArray(data.photoBoards) ? data.photoBoards.map(ensurePhotoBoardShape) : [];
    next.projects = Array.isArray(data.projects) ? data.projects.map(ensureProjectShape) : [];
    next.media = Array.isArray(data.media) ? data.media.map(ensureMediaShape) : [];
  } else {
    const migrated = migrateV1ToV2(data, next.projectName);
    next.questionTemplates = migrated.questionTemplates;
    next.games = migrated.games.map(ensureGameShape);
    next.media = migrated.media.map(ensureMediaShape);
    next.dailyNotes = [];
    next.photoBoards = [];
    next.projects = [];
  }

  next.view = 'library';
  next.activeGameId = null;
  next.activeTab = 'questions';
  next.activeMediaId = null;
  next.activeDailyNoteId = null;
  next.activePhotoBoardId = null;
  next.activeProjectId = null;
  next.activeProjectTab = 'doc';
  next.activeMilestoneId = null;
  next.activeKanbanBoardId = null;
  S = next;
  navStack = [];
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
  const aud = $('audio-viewer');
  if (vid) {
    vid.pause();
    vid.removeAttribute('src');
    try { vid.load(); } catch (e) {}
  }
  if (aud) {
    aud.pause();
    aud.removeAttribute('src');
    try { aud.load(); } catch (e) {}
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
  const aud = $('audio-viewer');
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
  if (aud) {
    aud.pause();
    aud.classList.add('hidden');
    aud.removeAttribute('src');
    try { aud.load(); } catch (e) {}
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
  $('audio-viewer')?.classList.add('hidden');

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
  } else if (item.type === 'audio') {
    const aud = $('audio-viewer');
    aud.classList.remove('hidden');
    aud.src = url;
    aud.volume = Number($('vol-slider').value || 100) / 100;
    aud.play().catch(() => {});
    hidePlayback();
    setFrameDisplay('Sound');
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
  const aud = $('audio-viewer');
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
  if (aud) {
    aud.addEventListener('loadedmetadata', fitToScreen);
  }
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
  if (vid && vid.classList.contains('hidden')) return null;
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
  $('pb-prev').textContent = V.frameMode === 'framebyframe' ? '-1F' : '-1s';
  $('pb-next').textContent = V.frameMode === 'framebyframe' ? '+1F' : '+1s';
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
  document.addEventListener('pointerdown', rememberScrollState, true);
  document.addEventListener('keydown', rememberScrollState, true);
  document.addEventListener('dragstart', rememberScrollState, true);
  document.addEventListener('drop', rememberScrollState, true);

  document.querySelectorAll('.nav-btn').forEach(btn => {
    btn.onclick = () => setView(btn.dataset.view);
  });
  if ($('quick-new-game')) $('quick-new-game').onclick = createGameFlow;

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
    if (e.key === 'Escape') {
      if (!$('modal-bg').classList.contains('hidden')) {
        closeModal();
        return;
      }
      if ($('importance-menu') || $('milestone-menu') || $('category-menu') || $('album-lightbox') || $('task-notebook')) {
        closeImportanceMenu();
        closeMilestoneMenu();
        closeCategoryMenu();
        closeAlbumLightbox();
        closeTaskNotebook();
        return;
      }
      e.preventDefault();
      goBack();
      return;
    }
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
