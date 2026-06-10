'use strict';

const { ipcRenderer, clipboard, webUtils } = require('electron');
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

const APP_VERSION = 8;
const APP_TYPE = 'game-analysis-library';
const DAILIES_EPOCH = '2026-06-07';
const MOODBOARD_WORLD_MARGIN = 90000;
const MOODBOARD_WORLD_MIN_WIDTH = 240000;
const MOODBOARD_WORLD_MIN_HEIGHT = 180000;

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
  return [];
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

const DAILY_COLUMNS = [
  ['todo', 'Todo'],
  ['done', 'Done'],
];

const DAILY_TABS = ['today', 'defaults', 'calendar'];

const GAME_TABS = ['notes', 'photos', 'videos', 'sound', 'board'];

const PAINT_TOOLS = [['select', 'Select']];

const PAINT_BACKGROUND = '#111315';
const PAINT_GRID_SIZE = 40;

function normalizeGameTab(tab) {
  return GAME_TABS.includes(tab) ? tab : 'notes';
}

function gameWithoutQuestions(game) {
  const clean = { ...game };
  delete clean.answers;
  delete clean.collapsedQuestions;
  return clean;
}

function freshState() {
  return {
    createdAt: now(),
    projectPath: null,
    projectName: 'Untitled',
    modified: false,
    view: 'library',
    activeGameId: null,
    activeTab: 'notes',
    activeMediaId: null,
    activeDailyNoteId: null,
    activePhotoBoardId: null,
    activeProjectId: null,
    activeProjectTab: 'doc',
    activeMilestoneId: null,
    activeKanbanBoardId: null,
    activeDailyDate: null,
    dailyCalendarMonth: null,
    activeMoodboardId: null,
    gameSearch: '',
    dailySearch: '',
    photoSearch: '',
    projectSearch: '',
    noteSearch: '',
    notes: null,
    dailies: null,
    moodboard: null,
    drawing: null,
    dailyNotes: [],
    photoBoards: [],
    projects: [],
    questionTemplates: [],
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
  moodboardHistory: [],
  moodboardSelection: [],
  moodboardViewportReady: {},
  paintHistory: {},
  paintViewportReady: {},
  paintSelection: null,
  paintConnectorFrom: null,
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

function dateToISO(value) {
  const date = value instanceof Date ? new Date(value) : new Date(value || Date.now());
  if (Number.isNaN(date.getTime())) return todayISO();
  date.setMinutes(date.getMinutes() - date.getTimezoneOffset());
  return date.toISOString().slice(0, 10);
}

function todayISO() {
  return dateToISO(new Date());
}

function addDaysISO(value, amount) {
  const date = new Date(String(value || todayISO()) + 'T00:00:00');
  date.setDate(date.getDate() + amount);
  return dateToISO(date);
}

function daysBetweenISO(from, to) {
  const start = new Date(String(from || todayISO()) + 'T00:00:00');
  const end = new Date(String(to || todayISO()) + 'T00:00:00');
  return Math.round((end - start) / 86400000);
}

function monthISO(value = todayISO()) {
  return String(value || todayISO()).slice(0, 7);
}

function maxISODate(a, b) {
  return String(a || '') > String(b || '') ? a : b;
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
  '.moodboard-viewport',
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

function defaultPaintCategory() {
  return { id: 'paintcat_default', title: 'Main', createdAt: now(), updatedAt: now() };
}

function ensurePaintCategoryShape(category, fallback = 'Main') {
  if (!category || typeof category !== 'object') category = {};
  category.id ??= 'paintcat_' + uid();
  category.title ??= fallback;
  category.createdAt ??= now();
  category.updatedAt ??= now();
  return category;
}

function createPaintBoard(title = 'Board', categoryId = 'paintcat_default') {
  return ensurePaintBoardShape({
    id: 'pboard_' + uid(),
    title,
    categoryId,
    elements: [],
    zoom: 1,
    panX: 0,
    panY: 0,
    tool: 'select',
    color: '#5d6674',
    fillColor: '#181b20',
    lineWidth: 4,
    fontSize: 28,
    fillShapes: false,
    background: PAINT_BACKGROUND,
    createdAt: now(),
    updatedAt: now(),
  });
}

function ensurePaintWorkspaceShape(workspace) {
  if (!workspace || typeof workspace !== 'object') workspace = {};
  workspace.categories = Array.isArray(workspace.categories) && workspace.categories.length
    ? workspace.categories.map((category, index) => ensurePaintCategoryShape(category, index ? 'Category' : 'Main'))
    : [defaultPaintCategory()];
  workspace.activeCategoryId ??= workspace.categories[0]?.id || null;
  if (!workspace.categories.some(category => sameId(category.id, workspace.activeCategoryId))) {
    workspace.activeCategoryId = workspace.categories[0]?.id || null;
  }
  workspace.boards = Array.isArray(workspace.boards) && workspace.boards.length
    ? workspace.boards.map(board => ensurePaintBoardShape(board, workspace.activeCategoryId || workspace.categories[0]?.id))
    : [createPaintBoard('Board 1', workspace.activeCategoryId || workspace.categories[0]?.id)];
  workspace.activeBoardId ??= workspace.boards[0]?.id || null;
  if (!workspace.boards.some(board => sameId(board.id, workspace.activeBoardId))) {
    workspace.activeBoardId = workspace.boards[0]?.id || null;
  }
  workspace.boardOpen = workspace.boardOpen === true;
  workspace.createdAt ??= now();
  workspace.updatedAt ??= now();
  return workspace;
}

function ensurePaintBoardShape(board, fallbackCategoryId = 'paintcat_default') {
  if (!board || typeof board !== 'object') board = {};
  board.id ??= 'pboard_' + uid();
  board.title ??= 'Board';
  board.categoryId ??= fallbackCategoryId || 'paintcat_default';
  board.elements = Array.isArray(board.elements) ? board.elements.map(ensurePaintElementShape).filter(Boolean) : [];
  board.zoom = clampNumber(board.zoom, 1, 0.05, 20);
  board.panX = paintNumber(board.panX, 0);
  board.panY = paintNumber(board.panY, 0);
  board.tool = 'select';
  board.color = paintColor(board.color, '#5d6674');
  board.fillColor = paintColor(board.fillColor, '#181b20');
  board.lineWidth = clampNumber(board.lineWidth, 4, 1, 72);
  board.fontSize = clampNumber(board.fontSize, 28, 10, 96);
  board.fillShapes = board.fillShapes === true;
  board.background = paintColor(board.background, PAINT_BACKGROUND);
  if (board.background === '#f4f1e8') board.background = PAINT_BACKGROUND;
  board.createdAt ??= now();
  board.updatedAt ??= now();
  return board;
}

function ensurePaintElementShape(element) {
  if (!element || typeof element !== 'object') return null;
  element.id ??= 'pel_' + uid();
  element.type ??= 'path';
  element.color = paintColor(element.color, '#d7dce3');
  element.fill = element.fill === 'transparent' ? 'transparent' : paintColor(element.fill, 'transparent');
  element.width = clampNumber(element.width, 4, 1, 96);
  element.z = clampNumber(element.z, 1, 1, 1000000);
  element.createdAt ??= now();
  element.updatedAt ??= now();

  if (element.type === 'path') {
    element.tool = element.tool === 'eraser' ? 'eraser' : element.tool === 'brush' ? 'brush' : 'pencil';
    element.points = Array.isArray(element.points)
      ? element.points.map(paintPoint).filter(Boolean)
      : [];
    return element.points.length ? element : null;
  }
  if (element.type === 'line' || element.type === 'arrow') {
    element.x1 = paintNumber(element.x1, 0);
    element.y1 = paintNumber(element.y1, 0);
    element.x2 = paintNumber(element.x2, element.x1 + 1);
    element.y2 = paintNumber(element.y2, element.y1 + 1);
    return element;
  }
  if (element.type === 'connector') {
    element.fromId ??= null;
    element.toId ??= null;
    element.fromSide = ['n', 'e', 's', 'w'].includes(element.fromSide) ? element.fromSide : 's';
    element.toSide = ['n', 'e', 's', 'w'].includes(element.toSide) ? element.toSide : 'n';
    element.x1 = paintNumber(element.x1, 0);
    element.y1 = paintNumber(element.y1, 0);
    element.x2 = paintNumber(element.x2, element.x1 + PAINT_GRID_SIZE);
    element.y2 = paintNumber(element.y2, element.y1 + PAINT_GRID_SIZE);
    return element;
  }
  if (element.type === 'rect' || element.type === 'ellipse' || element.type === 'image' || element.type === 'note' || element.type === 'block') {
    element.x = paintNumber(element.x, 0);
    element.y = paintNumber(element.y, 0);
    element.w = clampNumber(element.w, element.type === 'note' || element.type === 'block' ? 260 : 160, 24, 5000);
    element.h = clampNumber(element.h, element.type === 'note' || element.type === 'block' ? 150 : 120, 24, 5000);
    element.text ??= '';
    element.fontSize = clampNumber(element.fontSize, element.type === 'block' ? 14 : 18, 10, 120);
    return element;
  }
  if (element.type === 'text') {
    element.x = paintNumber(element.x, 0);
    element.y = paintNumber(element.y, 0);
    element.w = clampNumber(element.w, 260, 40, 5000);
    element.h = clampNumber(element.h, 60, 20, 2000);
    element.fontSize = clampNumber(element.fontSize, 28, 10, 120);
    element.text ??= 'Text';
    return element;
  }
  return null;
}

function paintNumber(value, fallback = 0) {
  const next = Number(value);
  return Number.isFinite(next) ? next : fallback;
}

function paintPoint(point) {
  if (!point || typeof point !== 'object') return null;
  return { x: paintNumber(point.x, 0), y: paintNumber(point.y, 0) };
}

function paintColor(value, fallback) {
  if (value === 'transparent') return value;
  const text = String(value || '');
  return /^#[0-9a-f]{6}$/i.test(text) ? text : fallback;
}

function paintToolButtonHTML(id, label, activeId) {
  return `
    <button class="paint-tool-btn ${activeId === id ? 'active' : ''}" data-paint-tool="${esc(id)}" title="${esc(label)}" aria-label="${esc(label)}">
      ${paintToolIconHTML(id)}
      <span>${esc(label)}</span>
    </button>`;
}

function paintToolIconHTML(id) {
  const icons = {
    select: '<path d="M5 4l8 8-4 1-2 5-2-1.5 2-4-4-2z"/>',
    block: '<rect x="3" y="5" width="18" height="14" rx="2"/><path d="M7 10h10M7 14h7"/>',
    connector: '<path d="M6 7c7 0 5 10 12 10"/><path d="M15 14l3 3-4 2"/>',
    pencil: '<path d="M4 17l1 3 3-1L18 9l-4-4z"/><path d="M13 6l4 4"/>',
    brush: '<path d="M14 4l6 6-7 7-6-6z"/><path d="M4 14c2 1 3 3 1 6 3 0 5-2 6-5"/>',
    eraser: '<path d="M4 14l8-8 8 8-5 5H9z"/><path d="M9 19h11"/>',
    fill: '<path d="M5 12l7-7 7 7-7 7z"/><path d="M15 15h6v5h-6z"/>',
    picker: '<path d="M14 4l6 6-3 3-6-6z"/><path d="M13 8l-8 8v4h4l8-8"/>',
    line: '<path d="M5 19L19 5"/>',
    arrow: '<path d="M5 19L19 5"/><path d="M12 5h7v7"/>',
    rect: '<rect x="5" y="6" width="14" height="12" rx="1"/>',
    ellipse: '<ellipse cx="12" cy="12" rx="8" ry="6"/>',
    text: '<path d="M5 6h14M12 6v13M9 19h6"/>',
    note: '<path d="M6 4h9l3 3v13H6z"/><path d="M15 4v4h4M9 12h6M9 16h5"/>',
    pan: '<path d="M7 12V8a2 2 0 0 1 4 0v3"/><path d="M11 11V7a2 2 0 0 1 4 0v5"/><path d="M15 12V9a2 2 0 0 1 4 0v5c0 4-2 7-6 7h-1c-3 0-5-2-7-6"/>',
  };
  return `<svg class="paint-tool-icon" viewBox="0 0 24 24" aria-hidden="true">${icons[id] || icons.select}</svg>`;
}

function paintSnap(value) {
  return Math.round(Number(value || 0) / PAINT_GRID_SIZE) * PAINT_GRID_SIZE;
}

function paintSnapPoint(point) {
  return { x: paintSnap(point.x), y: paintSnap(point.y) };
}

function paintIsTileElement(element) {
  return ['block', 'note', 'text', 'image', 'rect', 'ellipse'].includes(element?.type);
}

function paintElementHasInlineText(element) {
  return ['block', 'note', 'text'].includes(element?.type);
}

function paintIsTextTopElement(element) {
  return ['text', 'note', 'block'].includes(element?.type);
}

function paintVisualZ(element) {
  if (element?.type === 'connector') return Number(element.z || 1);
  if (paintIsTextTopElement(element)) return 200000 + Number(element.z || 1);
  return 50000 + Number(element?.z || 1);
}

function paintElementCenter(element, board = null) {
  if (!element) return null;
  if (paintIsTileElement(element)) {
    return {
      x: Number(element.x || 0) + Number(element.w || 0) / 2,
      y: Number(element.y || 0) + Number(element.h || 0) / 2,
    };
  }
  const bounds = paintElementBounds(element, board);
  return bounds ? { x: bounds.x + bounds.w / 2, y: bounds.y + bounds.h / 2 } : null;
}

function paintAnchorForElement(element, side = 's') {
  if (!element) return { x: 0, y: 0 };
  const x = Number(element.x || 0);
  const y = Number(element.y || 0);
  const w = Number(element.w || 0);
  const h = Number(element.h || 0);
  if (side === 'n') return { x: x + w / 2, y };
  if (side === 'e') return { x: x + w, y: y + h / 2 };
  if (side === 'w') return { x, y: y + h / 2 };
  return { x: x + w / 2, y: y + h };
}

function getPaintWorkspaceForOwner(owner) {
  owner.paintBoards = ensurePaintWorkspaceShape(owner.paintBoards);
  return owner.paintBoards;
}

function getPaintCategories(workspace) {
  ensurePaintWorkspaceShape(workspace);
  return workspace.categories;
}

function getActivePaintCategory(workspace) {
  ensurePaintWorkspaceShape(workspace);
  let category = workspace.categories.find(item => sameId(item.id, workspace.activeCategoryId));
  if (!category) {
    category = workspace.categories[0];
    workspace.activeCategoryId = category?.id || null;
  }
  return category;
}

function setActivePaintCategory(workspace, categoryId) {
  ensurePaintWorkspaceShape(workspace);
  const category = workspace.categories.find(item => sameId(item.id, categoryId)) || workspace.categories[0];
  workspace.activeCategoryId = category?.id || null;
  return category;
}

function getActivePaintBoard(workspace) {
  ensurePaintWorkspaceShape(workspace);
  let board = workspace.boards.find(item => sameId(item.id, workspace.activeBoardId));
  if (!board) {
    const category = getActivePaintCategory(workspace);
    board = workspace.boards.find(item => sameId(item.categoryId, category?.id)) || workspace.boards[0] || null;
    workspace.activeBoardId = board?.id || null;
  }
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
  task.completedAt ??= null;
  task.createdAt ??= now();
  task.updatedAt ??= now();
  return task;
}

function ensureKanbanBoardShape(board) {
  board.id ??= 'kb_' + uid();
  board.title ??= 'Board';
  board.columns ??= {};
  KANBAN_COLUMNS.forEach(([key]) => {
    board.columns[key] = Array.isArray(board.columns[key]) ? board.columns[key].map(task => {
      const next = ensureTaskShape(task);
      if (key === 'done' && !next.completedAt) next.completedAt = next.updatedAt || next.createdAt || now();
      return next;
    }) : [];
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
  project.paintBoards = ensurePaintWorkspaceShape(project.paintBoards);
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

function ensureNotesShape(notes) {
  notes = ensureBlockContainerShape(notes || { blocks: [] });
  notes.id ??= 'notes';
  notes.title ??= 'Notes';
  notes.categoryOpen = notes.categoryOpen === true;
  notes.createdAt ??= now();
  notes.updatedAt ??= now();
  return notes;
}

function notesFromLegacyDailyNotes(dailyNotes) {
  const notes = ensureNotesShape({ blocks: [] });
  const source = Array.isArray(dailyNotes) ? dailyNotes : [];
  if (!source.length) return notes;
  notes.categories = [];
  source
    .map(ensureDailyNoteShape)
    .sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')))
    .forEach(note => {
      const category = ensureBlockCategoryShape({
        id: 'blockcat_' + uid(),
        title: note.title || formatDateTitle(note.date),
        createdAt: note.createdAt || now(),
        updatedAt: note.updatedAt || now(),
      });
      notes.categories.push(category);
      (note.blocks || []).forEach(block => {
        const next = ensureBlockShape({ ...block });
        next.id = 'legacy_' + uid();
        next.categoryId = category.id;
        notes.blocks.push(next);
      });
    });
  if (!notes.categories.length) notes.categories = [defaultBlockCategory()];
  notes.activeCategoryId = notes.categories[0].id;
  return ensureNotesShape(notes);
}

function createDailyTemplate(title = 'Daily quest') {
  return ensureDailyTemplateShape({
    id: 'dt_' + uid(),
    title,
    notes: '',
    importance: 'common',
    categoryId: S.dailies?.activeTemplateCategoryId || 'dtcat_default',
    enabled: true,
    order: dailyTemplatesForCategory(S.dailies?.activeTemplateCategoryId).length,
    createdAt: now(),
    updatedAt: now(),
  });
}

function ensureDailyTemplateShape(template, index = 0) {
  template.id ??= 'dt_' + uid();
  template.title ??= 'Daily quest';
  template.notes ??= '';
  template.categoryId ??= 'dtcat_default';
  template.importance = importanceLevel(template.importance).id;
  template.enabled = template.enabled !== false;
  template.order = Number.isFinite(Number(template.order)) ? Number(template.order) : index;
  template.createdAt ??= now();
  template.updatedAt ??= now();
  return template;
}

function defaultDailyTemplateCategory() {
  return { id: 'dtcat_default', title: 'Default', createdAt: now(), updatedAt: now() };
}

function ensureDailyTemplateCategoryShape(category, index = 0) {
  if (!category || typeof category !== 'object') category = {};
  category.id ??= 'dtcat_' + uid();
  category.title ??= index ? 'Preset' : 'Default';
  category.createdAt ??= now();
  category.updatedAt ??= now();
  return category;
}

function getActiveDailyTemplateCategory() {
  ensureDailiesShape(S.dailies);
  return S.dailies.templateCategories.find(category => sameId(category.id, S.dailies.activeTemplateCategoryId))
    || S.dailies.templateCategories[0];
}

function dailyTemplatesForCategory(categoryId = getActiveDailyTemplateCategory()?.id) {
  return (S.dailies?.templates || [])
    .map(ensureDailyTemplateShape)
    .filter(template => sameId(template.categoryId, categoryId))
    .sort((a, b) => (a.order ?? 0) - (b.order ?? 0));
}

function createDailyQuest(title = 'Daily quest', source = 'manual') {
  return ensureDailyQuestShape({
    id: 'dq_' + uid(),
    title,
    notes: '',
    importance: 'common',
    source,
    sourceTemplateId: null,
    completedAt: null,
    createdAt: now(),
    updatedAt: now(),
  });
}

function createDailyQuestFromTemplate(template) {
  ensureDailyTemplateShape(template);
  return ensureDailyQuestShape({
    id: 'dq_' + uid(),
    title: template.title,
    notes: template.notes || '',
    importance: template.importance || 'common',
    source: 'default',
    sourceTemplateId: template.id,
    completedAt: null,
    createdAt: now(),
    updatedAt: now(),
  });
}

function ensureDailyQuestShape(quest) {
  quest.id ??= 'dq_' + uid();
  quest.title ??= 'Daily quest';
  quest.notes ??= '';
  quest.importance = importanceLevel(quest.importance).id;
  quest.source ??= 'manual';
  quest.sourceTemplateId ??= null;
  quest.completedAt ??= null;
  quest.createdAt ??= now();
  quest.updatedAt ??= now();
  return quest;
}

function createDailyDay(date = todayISO()) {
  const day = ensureDailyDayShape({
    id: 'dd_' + date,
    date,
    title: formatDateTitle(date),
    journal: '',
    status: 'open',
    columns: { todo: [], done: [], extra: [] },
    celebratedAt: null,
    createdAt: now(),
    updatedAt: now(),
  });
  const templates = dailyTemplatesForCategory(S.dailies?.activeTemplateCategoryId)
    .filter(template => template.enabled !== false);
  day.columns.todo = templates.map(createDailyQuestFromTemplate);
  return day;
}

function ensureDailyDayShape(day) {
  day.id ??= 'dd_' + (day.date || todayISO());
  day.date ??= todayISO();
  day.title ??= formatDateTitle(day.date);
  day.journal ??= '';
  day.status ??= 'open';
  day.celebratedAt ??= null;
  day.columns ??= {};
  if (Array.isArray(day.columns.need) && day.columns.need.length) {
    day.columns.todo = [...day.columns.need, ...(Array.isArray(day.columns.todo) ? day.columns.todo : [])];
    delete day.columns.need;
  }
  day.columns.extra = Array.isArray(day.columns.extra) ? day.columns.extra.map(ensureDailyQuestShape) : [];
  DAILY_COLUMNS.forEach(([key]) => {
    day.columns[key] = Array.isArray(day.columns[key]) ? day.columns[key].map(ensureDailyQuestShape) : [];
    const extras = day.columns[key].filter(quest => quest.source === 'extra');
    if (extras.length) {
      day.columns.extra.push(...extras);
      day.columns[key] = day.columns[key].filter(quest => quest.source !== 'extra');
    }
  });
  day.createdAt ??= now();
  day.updatedAt ??= now();
  return day;
}

function ensureDailiesShape(dailies) {
  if (!dailies || typeof dailies !== 'object') dailies = {};
  dailies.enabled = dailies.enabled !== false;
  dailies.disabledAt ??= null;
  dailies.pausedRanges = Array.isArray(dailies.pausedRanges)
    ? dailies.pausedRanges
      .map(range => ({
        from: dateToISO(range.from || todayISO()),
        to: dateToISO(range.to || range.from || todayISO()),
      }))
      .filter(range => String(range.from) <= String(range.to))
    : [];
  dailies.activeTab = DAILY_TABS.includes(dailies.activeTab) ? dailies.activeTab : 'today';
  dailies.templateCategories = Array.isArray(dailies.templateCategories) && dailies.templateCategories.length
    ? dailies.templateCategories.map(ensureDailyTemplateCategoryShape)
    : [defaultDailyTemplateCategory()];
  dailies.activeTemplateCategoryId ??= dailies.templateCategories[0]?.id || 'dtcat_default';
  if (!dailies.templateCategories.some(category => sameId(category.id, dailies.activeTemplateCategoryId))) {
    dailies.activeTemplateCategoryId = dailies.templateCategories[0]?.id || 'dtcat_default';
  }
  dailies.templates = Array.isArray(dailies.templates)
    ? dailies.templates.map(ensureDailyTemplateShape).sort((a, b) => (a.order ?? 0) - (b.order ?? 0))
    : [];
  const categoryIds = new Set(dailies.templateCategories.map(category => category.id));
  dailies.templates.forEach(template => {
    if (!categoryIds.has(template.categoryId)) template.categoryId = dailies.templateCategories[0].id;
  });
  dailies.days = Array.isArray(dailies.days)
    ? dailies.days.map(ensureDailyDayShape)
    : [];
  dailies.createdAt ??= S.createdAt || now();
  dailies.lastEnsuredDate ??= null;
  dailies.updatedAt ??= now();
  return dailies;
}

function ensureMoodboardShape(board) {
  if (!board || typeof board !== 'object') board = {};
  board.id ??= 'moodboard';
  if (!Array.isArray(board.boards) || !board.boards.length) {
    board.boards = [ensureMoodboardBoardShape({
      id: 'mb_' + uid(),
      title: 'Board 1',
      items: Array.isArray(board.items) ? board.items : [],
      zoom: board.zoom || 1,
      createdAt: board.createdAt || now(),
      updatedAt: board.updatedAt || now(),
    })];
  } else {
    board.boards = board.boards.map((item, index) => ensureMoodboardBoardShape(item, index));
  }
  delete board.items;
  board.activeBoardId ??= board.boards[0]?.id || null;
  if (!board.boards.some(item => sameId(item.id, board.activeBoardId))) board.activeBoardId = board.boards[0]?.id || null;
  board.boardOpen = board.boardOpen === true;
  board.createdAt ??= now();
  board.updatedAt ??= now();
  return board;
}

function ensureMoodboardBoardShape(board, index = 0) {
  if (!board || typeof board !== 'object') board = {};
  board.id ??= 'mb_' + uid();
  board.title ??= index ? 'Moodboard' : 'Board 1';
  board.items = Array.isArray(board.items) ? board.items.map(ensureMoodboardItemShape) : [];
  board.zoom = clampNumber(board.zoom, 1, .1, 8);
  board.originX = clampNumber(board.originX, MOODBOARD_WORLD_MARGIN, 1000, 10000000);
  board.originY = clampNumber(board.originY, MOODBOARD_WORLD_MARGIN, 1000, 10000000);
  board.createdAt ??= now();
  board.updatedAt ??= now();
  return board;
}

function ensureMoodboardItemShape(item) {
  item.id ??= 'mbi_' + uid();
  item.mediaId ??= null;
  item.x = clampNumber(item.x, 80, -50000, 500000);
  item.y = clampNumber(item.y, 80, -50000, 500000);
  item.w = clampNumber(item.w, 260, 80, 20000);
  item.h = clampNumber(item.h, 190, 80, 20000);
  item.z = clampNumber(item.z, 1, 1, 999999);
  item.createdAt ??= now();
  item.updatedAt ??= now();
  return item;
}

function getActiveMoodboard() {
  S.moodboard = ensureMoodboardShape(S.moodboard);
  const activeId = S.activeMoodboardId || S.moodboard.activeBoardId;
  let board = S.moodboard.boards.find(item => sameId(item.id, activeId));
  if (!board) board = S.moodboard.boards[0] || null;
  if (board) {
    S.moodboard.activeBoardId = board.id;
    S.activeMoodboardId = board.id;
  }
  return board;
}

function ensureDrawingShape(drawing) {
  if (!drawing || typeof drawing !== 'object') drawing = {};
  drawing.id ??= 'drawing';
  drawing.title ??= 'Drawing';
  drawing.categoryOpen = drawing.categoryOpen === true;
  ensureMediaCategoryBucket(drawing, 'photo');
  drawing.createdAt ??= now();
  drawing.updatedAt ??= now();
  return drawing;
}

function clampNumber(value, fallback, min, max) {
  const number = Number(value);
  if (!Number.isFinite(number)) return fallback;
  return Math.max(min, Math.min(max, number));
}

function ensureWorkspaceShape() {
  S.notes = ensureNotesShape(S.notes);
  S.dailies = ensureDailiesShape(S.dailies);
  S.moodboard = ensureMoodboardShape(S.moodboard);
  S.drawing = ensureDrawingShape(S.drawing);
  S.activeDailyDate ??= todayISO();
  S.dailyCalendarMonth ??= monthISO(S.activeDailyDate || todayISO());
}

function getDailiesStartDate() {
  const raw = S.createdAt || S.dailies?.createdAt || now();
  const created = dateToISO(raw);
  return maxISODate(created, DAILIES_EPOCH);
}

function isDailiesPausedDate(date) {
  if (S.dailies?.enabled === false && S.dailies.disabledAt && String(date) >= String(S.dailies.disabledAt) && String(date) <= String(todayISO())) {
    return true;
  }
  return (S.dailies?.pausedRanges || []).some(range => (
    String(date) >= String(range.from) && String(date) <= String(range.to)
  ));
}

function countDailiesTrackDays(start, end) {
  let count = 0;
  let date = start;
  let guard = 0;
  while (String(date) <= String(end) && guard < 5000) {
    if (!isDailiesPausedDate(date)) count += 1;
    date = addDaysISO(date, 1);
    guard += 1;
  }
  return count;
}

function setDailiesEnabled(enabled) {
  ensureWorkspaceShape();
  const today = todayISO();
  if (!enabled && S.dailies.enabled) {
    S.dailies.enabled = false;
    S.dailies.disabledAt = today;
  } else if (enabled && !S.dailies.enabled) {
    const from = S.dailies.disabledAt;
    const to = addDaysISO(today, -1);
    if (from && String(from) <= String(to)) {
      S.dailies.pausedRanges.push({ from, to });
    }
    S.dailies.disabledAt = null;
    S.dailies.enabled = true;
    ensureDailiesReady();
  }
  S.dailies.updatedAt = now();
  markDirty();
}

function dailyStats(day) {
  ensureDailyDayShape(day);
  const externalDone = collectExternalDailyTasks(day.date).length;
  const extraTotal = (day.columns.extra || []).length;
  const extraDone = (day.columns.extra || []).filter(quest => quest.completedAt).length;
  const routineTotal = DAILY_COLUMNS.reduce((sum, [key]) => sum + (day.columns[key] || []).length, 0);
  const routineDone = (day.columns.done || []).length;
  const dailyTotal = routineTotal + extraTotal;
  const dailyDone = routineDone + extraDone;
  const total = dailyTotal + externalDone;
  const done = dailyDone + externalDone;
  const pct = total ? Math.round((done / total) * 100) : 0;
  return {
    total,
    done,
    dailyTotal,
    dailyDone,
    routineTotal,
    routineDone,
    extraTotal,
    extraDone,
    externalDone,
    todo: (day.columns.todo || []).length,
    extraTodo: Math.max(0, extraTotal - extraDone),
    pct,
    complete: total > 0 && done >= total,
  };
}

function syncDailyDayStatus(day, today = todayISO()) {
  ensureDailyDayShape(day);
  const before = day.status;
  const stats = dailyStats(day);
  if (stats.complete) day.status = 'complete';
  else if (String(day.date) < String(today)) day.status = 'failed';
  else day.status = 'open';
  if (before !== day.status) {
    day.updatedAt = now();
    return true;
  }
  return false;
}

function ensureDailiesReady(options = {}) {
  ensureWorkspaceShape();
  if (!S.dailies.enabled) return false;
  const today = todayISO();
  const start = getDailiesStartDate();
  let date = start;
  let changed = false;
  let guard = 0;
  while (String(date) <= String(today) && guard < 5000) {
    if (isDailiesPausedDate(date)) {
      date = addDaysISO(date, 1);
      guard += 1;
      continue;
    }
    let day = S.dailies.days.find(item => item.date === date);
    if (!day) {
      day = createDailyDay(date);
      S.dailies.days.push(day);
      changed = true;
    }
    if (syncDailyDayStatus(day, today)) changed = true;
    date = addDaysISO(date, 1);
    guard += 1;
  }
  S.dailies.days.sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
  if (S.dailies.lastEnsuredDate !== today) {
    S.dailies.lastEnsuredDate = today;
    changed = true;
  }
  if (changed) {
    S.dailies.updatedAt = now();
    if (options.dirty !== false) markDirty();
  }
  return changed;
}

function getDailyDay(date) {
  ensureWorkspaceShape();
  return S.dailies.days.find(day => day.date === date) || null;
}

function getOrCreateDailyDay(date) {
  ensureWorkspaceShape();
  const cleanDate = date || todayISO();
  let day = getDailyDay(cleanDate);
  if (!day) {
    day = createDailyDay(cleanDate);
    S.dailies.days.push(day);
    syncDailyDayStatus(day);
    S.dailies.updatedAt = now();
    markDirty();
  }
  return day;
}

function taskCompletedISO(task) {
  if (!task?.completedAt) return null;
  return dateToISO(task.completedAt);
}

function collectExternalDailyTasks(date = todayISO()) {
  const targetDate = dateToISO(date);
  const tasks = [];
  (S.projects || []).forEach(project => {
    (project.milestones || []).forEach(milestone => {
      (milestone.boards || []).forEach(board => {
        (board.columns?.done || []).forEach(task => {
          if (taskCompletedISO(task) !== targetDate) return;
          tasks.push({
            id: `${project.id}:${milestone.id}:${board.id}:${task.id}`,
            title: task.title || 'Task',
            importance: importanceLevel(task.importance).id,
            projectTitle: project.title || 'Project',
            milestoneTitle: milestone.title || 'Milestone',
            boardTitle: board.title || 'Board',
            completedAt: task.completedAt,
          });
        });
      });
    });
  });
  return tasks.sort((a, b) => String(b.completedAt || '').localeCompare(String(a.completedAt || '')));
}

function dailiesProgressStats() {
  ensureWorkspaceShape();
  const today = todayISO();
  const start = getDailiesStartDate();
  const days = S.dailies.days
    .map(ensureDailyDayShape)
    .filter(day => String(day.date) >= String(start) && String(day.date) <= String(today) && !isDailiesPausedDate(day.date));
  days.forEach(day => syncDailyDayStatus(day, today));
  const complete = days.filter(day => day.status === 'complete').length;
  const failed = days.filter(day => day.status === 'failed').length;
  const open = days.filter(day => day.status === 'open').length;
  const counted = complete + failed;
  const successRate = counted ? Math.round((complete / counted) * 100) : 0;
  let currentStreak = 0;
  let cursor = today;
  const todayDay = days.find(day => day.date === today);
  if (!todayDay || todayDay.status !== 'complete') cursor = addDaysISO(cursor, -1);
  while (String(cursor) >= String(start)) {
    const day = days.find(item => item.date === cursor);
    if (!day || day.status !== 'complete') break;
    currentStreak += 1;
    cursor = addDaysISO(cursor, -1);
  }
  let bestStreak = 0;
  let run = 0;
  [...days].sort((a, b) => String(a.date).localeCompare(String(b.date))).forEach(day => {
    if (day.status === 'complete') {
      run += 1;
      bestStreak = Math.max(bestStreak, run);
    } else if (day.status === 'failed') {
      run = 0;
    }
  });
  return {
    start,
    today,
    total: countDailiesTrackDays(start, today),
    complete,
    failed,
    open,
    successRate,
    currentStreak,
    bestStreak,
  };
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
    activeDailyDate: S.activeDailyDate,
    dailyCalendarMonth: S.dailyCalendarMonth,
    activeMoodboardId: S.activeMoodboardId,
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
  game.paintBoards = ensurePaintWorkspaceShape(game.paintBoards);
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

function returnToViewRoot(view) {
  ensureWorkspaceShape();
  if (view === 'daily-notes' && S.notes?.categoryOpen) {
    S.notes.categoryOpen = false;
    S.notes.updatedAt = now();
    markDirty();
    renderApp();
    return true;
  }
  if (view === 'drawing' && S.drawing?.categoryOpen) {
    S.drawing.categoryOpen = false;
    S.drawing.updatedAt = now();
    markDirty();
    renderApp();
    return true;
  }
  if (view === 'moodboard' && S.moodboard?.boardOpen) {
    S.moodboard.boardOpen = false;
    S.moodboard.updatedAt = now();
    clearMoodboardSelection();
    markDirty();
    renderApp();
    return true;
  }
  if (view === 'photo-boards' && S.activePhotoBoardId) {
    S.activePhotoBoardId = null;
    renderApp();
    return true;
  }
  if (view === 'projects' && S.activeProjectId) {
    S.activeProjectId = null;
    renderApp();
    return true;
  }
  return false;
}

function handleMainNavClick(view) {
  if (S.view === view && returnToViewRoot(view)) return;
  setView(view);
}

function setView(view, options = {}) {
  if (view === 'templates') view = 'library';
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
  if (view === 'dailies') {
    S.activeDailyDate ??= todayISO();
    S.dailyCalendarMonth ??= monthISO(S.activeDailyDate);
  }
  if (view === 'drawing') S.activeMediaId = null;
  S.view = view;
  renderApp();
}

function openGame(gameId, tab = 'notes', options = {}) {
  tab = normalizeGameTab(tab);
  stopViewer();
  if (!options.skipHistory && (S.view !== 'game' || S.activeGameId !== gameId || S.activeTab !== tab)) pushRoute();
  S.view = 'game';
  S.activeGameId = gameId;
  S.activeTab = tab;
  S.activeMediaId = null;
  renderApp();
}

function renderApp() {
  if (S.view === 'templates') S.view = 'library';
  S.activeTab = normalizeGameTab(S.activeTab);
  ensureWorkspaceShape();
  ensureDailiesReady();
  updateChrome();
  renderMiniGames();
  if (S.view === 'game') renderGameWorkspace();
  else if (S.view === 'daily-notes') renderNotes();
  else if (S.view === 'dailies') renderDailies();
  else if (S.view === 'moodboard') renderMoodboard();
  else if (S.view === 'drawing') renderDrawing();
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
    row.onclick = () => openGame(game.id, S.activeTab || 'notes');
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
          <button class="inline-btn" id="library-new-game">+ Game</button>
        </div>
      </div>
      <div class="screen-scroll" id="library-body"></div>
    </section>`;

  $('library-new-game').onclick = createGameFlow;
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

function renderNotes() {
  stopViewer();
  hidePlayback();
  S.notes = ensureNotesShape(S.notes);
  if (!S.notes.categoryOpen) {
    renderNotesCategoryLibrary();
    return;
  }
  renderNotesCategoryDetail();
}

function renderNotesCategoryLibrary() {
  S.notes = ensureNotesShape(S.notes);
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Notes</h1>
        </div>
        <div class="head-actions">
          <button class="inline-btn" id="notes-new-category">+ Category</button>
        </div>
      </div>
      <div class="screen-scroll" id="notes-category-body"></div>
    </section>`;

  $('notes-new-category').onclick = () => addBlockCategory(S.notes, () => {
    S.notes.categoryOpen = true;
    S.notes.updatedAt = now();
    markDirty();
    renderNotes();
  });

  const body = $('notes-category-body');
  if (!S.notes.categories.length) {
    body.innerHTML = `
      <div class="empty-state">
        <div class="empty-box">
          <div class="empty-title">Empty</div>
          <button class="inline-btn" id="notes-empty-category">+ Category</button>
        </div>
      </div>`;
    $('notes-empty-category').onclick = $('notes-new-category').onclick;
    return;
  }
  body.innerHTML = '<div class="category-card-grid" id="notes-category-grid"></div>';
  const grid = $('notes-category-grid');
  S.notes.categories.forEach(category => {
    const count = S.notes.blocks.filter(block => blockMatchesCategory(block, category.id)).length;
    const card = document.createElement('button');
    card.className = 'category-card';
    card.innerHTML = `
      <div class="category-card-mark">N</div>
      <div class="category-card-main">
        <div class="category-card-title">${esc(category.title)}</div>
        <div class="card-sub">${count} notes</div>
      </div>`;
    card.onclick = () => {
      S.notes.activeCategoryId = category.id;
      S.notes.categoryOpen = true;
      S.notes.updatedAt = now();
      markDirty();
      renderNotes();
    };
    grid.appendChild(card);
  });
}

function renderNotesCategoryDetail() {
  S.notes = ensureNotesShape(S.notes);
  const category = getActiveBlockCategory(S.notes);
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head roomy-head">
        <div class="title-wrap">
          <input id="notes-category-title" class="section-title-input" value="${esc(category.title)}">
        </div>
        <div class="head-actions">
          <button class="ghost-btn" id="notes-back-categories">Categories</button>
          <button class="ghost-btn" id="global-note-text">+ Text</button>
          <button class="ghost-btn" id="global-note-photo">+ Photo</button>
          <button class="ghost-btn" id="global-note-sound">+ Sound</button>
          <button class="ghost-btn" id="global-note-video">+ Video</button>
          <button class="danger-btn" id="notes-delete-category">Delete Category</button>
        </div>
      </div>
      <div class="tab-scroll">
        <div class="category-action-row">
          <button class="ghost-btn" id="global-note-sort-importance">Sort importance</button>
          <button class="ghost-btn" id="global-note-copy-category">Copy category</button>
          <button class="ghost-btn" id="global-note-copy-all">Copy all</button>
        </div>
        <div class="notes-list" id="global-notes-list"></div>
      </div>
    </section>`;

  $('notes-back-categories').onclick = () => {
    S.notes.categoryOpen = false;
    S.notes.updatedAt = now();
    markDirty();
    renderNotes();
  };
  $('notes-category-title').oninput = e => {
    category.title = e.target.value;
    category.updatedAt = now();
    S.notes.updatedAt = now();
    markDirty();
  };
  $('notes-delete-category').onclick = () => deleteNotesCategory(category);
  $('global-note-sort-importance').onclick = () => {
    sortBlocksByImportance(S.notes, category.id);
    S.notes.updatedAt = now();
    markDirty();
    renderNotes();
  };
  $('global-note-copy-category').onclick = () => copyBlockContainerToClipboard(S.notes, category.id);
  $('global-note-copy-all').onclick = () => copyBlockContainerToClipboard(S.notes);
  $('global-note-text').onclick = () => {
    const block = createTextBlock();
    block.categoryId = category.id;
    S.notes.blocks.push(block);
    S.notes.updatedAt = now();
    markDirty();
    renderNotes();
  };
  $('global-note-photo').onclick = () => addGlobalNoteMedia('photo');
  $('global-note-sound').onclick = () => addGlobalNoteMedia('sound');
  $('global-note-video').onclick = () => addGlobalNoteMedia('video');

  renderEditableBlocks($('global-notes-list'), S.notes.blocks, {
    ownerName: 'notes',
    onChange: () => {
      S.notes.updatedAt = now();
      markDirty();
    },
    onDelete: block => {
      S.notes.blocks = S.notes.blocks.filter(item => item.id !== block.id);
      S.notes.updatedAt = now();
      markDirty();
      renderNotes();
    },
    onReorder: () => {
      S.notes.updatedAt = now();
      markDirty();
      renderNotes();
    },
  }, { categoryId: getActiveBlockCategory(S.notes).id });
}

function deleteNotesCategory(category) {
  if (S.notes.categories.length <= 1) {
    toast('Keep one category');
    return;
  }
  if (!confirm(`Delete category "${category.title}"?`)) return;
  S.notes.blocks = S.notes.blocks.filter(block => !blockMatchesCategory(block, category.id));
  S.notes.categories = S.notes.categories.filter(item => !sameId(item.id, category.id));
  S.notes.activeCategoryId = S.notes.categories[0]?.id || null;
  S.notes.categoryOpen = false;
  S.notes.updatedAt = now();
  markDirty();
  renderNotes();
}

async function addGlobalNoteMedia(kind) {
  S.notes = ensureNotesShape(S.notes);
  const files = await pickMediaFiles(kind);
  if (!files.length) return;
  files.forEach(fp => {
    const media = registerMediaFile(fp, S.notes.id, kind, 'notes');
    if (media) S.notes.blocks.push({
      id: uid(),
      type: 'media',
      mediaId: media.id,
      title: media.name,
      caption: '',
      importance: 'common',
      categoryId: getActiveBlockCategory(S.notes).id,
      height: 270,
      createdAt: now(),
      updatedAt: now(),
    });
  });
  S.notes.updatedAt = now();
  markDirty();
  renderNotes();
  toast(`Added: ${files.length}`);
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

function renderDailies() {
  stopViewer();
  hidePlayback();
  ensureWorkspaceShape();
  ensureDailiesReady();
  const stats = dailiesProgressStats();
  const activeTab = S.dailies.activeTab || 'today';
  $('main').innerHTML = `
    <section class="screen dailies-screen simple-dailies-screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Dailies</h1>
        </div>
        <div class="head-actions">
          <span class="daily-compact-stat">${stats.currentStreak} streak</span>
          <span class="daily-compact-stat">${stats.bestStreak} best</span>
          <span class="daily-compact-stat">${stats.complete}/${stats.total} days</span>
          <span class="daily-compact-stat">${stats.successRate}% success</span>
          <button class="${S.dailies.enabled ? 'inline-btn' : 'danger-btn'}" id="toggle-dailies">
            ${S.dailies.enabled ? 'On' : 'Off'}
          </button>
        </div>
      </div>
      <div class="dailies-shell">
        <div class="tabs dailies-tabs">
          ${[
            ['today', 'Today'],
            ['defaults', 'Defaults'],
            ['calendar', 'Calendar'],
          ].map(([id, label]) => `<button class="tab-btn ${activeTab === id ? 'active' : ''}" data-daily-tab="${id}">${label}</button>`).join('')}
        </div>
        <div class="dailies-content" id="dailies-content"></div>
      </div>
    </section>`;

  $('toggle-dailies').onclick = () => {
    setDailiesEnabled(!S.dailies.enabled);
    renderDailies();
  };
  document.querySelectorAll('[data-daily-tab]').forEach(btn => {
    btn.onclick = () => {
      S.dailies.activeTab = btn.dataset.dailyTab;
      S.dailies.updatedAt = now();
      markDirty();
      renderDailies();
    };
  });

  const content = $('dailies-content');
  if (!S.dailies.enabled) renderDailiesDisabled(content);
  else if (activeTab === 'defaults') renderDailyDefaults(content);
  else if (activeTab === 'calendar') renderDailyCalendar(content);
  else renderDailyToday(content);
}

function renderDailiesDisabled(content) {
  content.innerHTML = `
    <div class="empty-state compact-empty">
      <div class="empty-box">
        <div class="empty-title">Dailies are off</div>
        <div class="empty-text">No new daily days will be created while this is disabled.</div>
        <button class="inline-btn" id="enable-dailies">Enable</button>
      </div>
    </div>`;
  $('enable-dailies').onclick = () => {
    setDailiesEnabled(true);
    renderDailies();
  };
}

function renderDailyToday(content) {
  const day = getOrCreateDailyDay(todayISO());
  S.activeDailyDate = day.date;
  S.dailyCalendarMonth = monthISO(day.date);
  renderDailyDayPanel(content, day, 'today');
}

function dailyExternalWorkHTML(date) {
  const items = collectExternalDailyTasks(date);
  if (!items.length) {
    return `
      <div class="daily-external-work empty">
        <div class="daily-side-title">Done elsewhere</div>
        <div class="daily-side-empty">Tasks moved to Done on this day will appear here.</div>
      </div>`;
  }
  return `
    <div class="daily-external-work">
      <div class="daily-side-title">Done elsewhere <span>${items.length}</span></div>
      <div class="daily-external-list">
        ${items.slice(0, 8).map(item => `
          <div class="daily-external-item task-importance-${esc(item.importance)}">
            <strong>${esc(item.title)}</strong>
            <small>${esc(item.projectTitle)} / ${esc(item.boardTitle)}</small>
          </div>`).join('')}
      </div>
    </div>`;
}

function renderDailyExtraList(day, host, rerender) {
  if (!host) return;
  ensureDailyDayShape(day);
  const extras = day.columns.extra || [];
  host.innerHTML = '';
  if (!extras.length) {
    host.innerHTML = '<div class="daily-side-empty">No extra tasks for this day.</div>';
    return;
  }
  extras.forEach(quest => host.appendChild(buildDailyExtraCard(day, quest, rerender)));
}

function buildDailyExtraCard(day, quest, rerender) {
  ensureDailyQuestShape(quest);
  const done = !!quest.completedAt;
  const card = document.createElement('div');
  card.className = `task-card daily-task-card daily-extra-card task-importance-${esc(importanceLevel(quest.importance).id)}${done ? ' done task-done' : ''}`;
  card.draggable = true;
  card.addEventListener('dragstart', e => {
    if (e.target.closest('input, textarea, button, .rarity-badge')) { e.preventDefault(); return; }
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('application/x-refboard-daily-task', JSON.stringify({
      date: day.date,
      columnKey: 'extra',
      taskId: quest.id,
    }));
    card.classList.add('dragging');
  });
  card.addEventListener('dragend', () => card.classList.remove('dragging'));
  card.innerHTML = `
    <div class="task-card-top daily-task-top">
      ${importanceBadgeHTML(quest.importance)}
      <input class="daily-task-title-input daily-extra-title" value="${esc(quest.title || '')}">
      ${done ? '<span class="task-done-mark">Done</span>' : ''}
      <button class="mini-btn daily-extra-toggle">${done ? 'Return' : 'Done'}</button>
    </div>
    <textarea class="daily-task-notes daily-extra-notes" placeholder="Extra note...">${esc(quest.notes || '')}</textarea>
    <div class="daily-task-foot">
      <span>${done ? `done${quest.completedAt ? ` ${formatShortDate(quest.completedAt)}` : ''}` : 'extra'}</span>
      <button class="mini-btn danger-lite daily-extra-delete">Delete</button>
    </div>`;
  bindImportanceTriggers(card, () => quest.importance, value => {
    quest.importance = value;
    touchDailyDay(day);
    markDirty();
    rerender();
  });
  card.querySelector('.daily-extra-title').oninput = e => {
    quest.title = e.target.value;
    quest.updatedAt = now();
    touchDailyDay(day);
    markDirty();
  };
  card.querySelector('.daily-extra-notes').oninput = e => {
    quest.notes = e.target.value;
    quest.updatedAt = now();
    touchDailyDay(day);
    markDirty();
  };
  card.querySelector('.daily-extra-toggle').onclick = () => toggleDailyExtraQuest(day, quest.id, rerender);
  card.querySelector('.daily-extra-delete').onclick = () => {
    if (!confirm(`Delete "${quest.title}"?`)) return;
    day.columns.extra = (day.columns.extra || []).filter(item => item.id !== quest.id);
    updateDailyCompletion(day);
    touchDailyDay(day);
    markDirty();
    rerender();
    // Re-render kanban if open so button reactivates
    if (S.view === 'projects' && S.activeProjectId) {
      const project = S.projects.find(p => p.id === S.activeProjectId);
      if (project) renderProjectWorkspace(project);
    }
  };
  return card;
}


function isKanbanTaskLinkedToExtras(taskId) {
  return (S.dailies?.days || []).some(day =>
    (day.columns?.extra || []).some(q => q.sourceRef === taskId)
  );
}

function addKanbanTaskToTodayExtras(task) {
  // Prevent duplicate across all days
  if (isKanbanTaskLinkedToExtras(task.id)) {
    toast('Already in Today extras');
    return;
  }
  const day = getOrCreateDailyDay(todayISO());
  ensureDailyDayShape(day);
  const quest = createDailyQuest(task.title || 'Task', 'extra');
  quest.importance = task.importance || 'common';
  quest.notes = task.notes || '';
  quest.sourceRef = task.id;
  day.columns.extra.push(quest);
  updateDailyCompletion(day);
  touchDailyDay(day);
  markDirty();
  // Re-render kanban card to show disabled state
  if (S.view === 'projects') {
    const btn = document.querySelector(`.task-to-today-btn[data-task-id="${task.id}"]`);
    if (btn) { btn.textContent = '✓ Added'; btn.disabled = true; btn.classList.add('added'); }
  }
  toast('Added to Today ✓');
}
function addDailyExtraQuestFlow(day, rerender) {
  askText('Extra Daily Task', '', 'Create', title => {
    const quest = createDailyQuest(title, 'extra');
    quest.importance = 'common';
    ensureDailyDayShape(day);
    day.columns.extra.push(quest);
    updateDailyCompletion(day);
    touchDailyDay(day);
    markDirty();
    rerender();
  });
}

function toggleDailyExtraQuest(day, questId, rerender) {
  ensureDailyDayShape(day);
  const quest = (day.columns.extra || []).find(item => item.id === questId);
  if (!quest) return;
  const beforeStats = dailyStats(day);
  const willDone = !quest.completedAt;
  quest.completedAt = willDone ? now() : null;
  quest.updatedAt = now();
  touchDailyDay(day);
  updateDailyCompletion(day, beforeStats, quest, willDone ? 'done' : 'extra');
  // Sync with linked kanban task
  if (quest.sourceRef && willDone) syncKanbanTaskDone(quest.sourceRef);
  markDirty();
  rerender();
}

function syncExtraQuestDone(taskId) {
  if (!S.dailies?.days) return;
  ensureDailiesReady({ dirty: false });
  for (const day of (S.dailies.days || [])) {
    ensureDailyDayShape(day);
    const quest = (day.columns.extra || []).find(q => q.sourceRef === taskId && !q.completedAt);
    if (quest) {
      const beforeStats = dailyStats(day);
      quest.completedAt = now();
      quest.updatedAt = now();
      touchDailyDay(day);
      updateDailyCompletion(day, beforeStats, quest, 'done');
      markDirty();
      return;
    }
  }
}

function syncKanbanTaskDone(taskId) {
  const nonDoneCols = KANBAN_COLUMNS.map(([k]) => k).filter(k => k !== 'done');
  for (const project of (S.projects || [])) {
    for (const milestone of (project.milestones || [])) {
      for (const board of (milestone.boards || [])) {
        // ensure board has columns
        if (!board.columns) continue;
        for (const col of nonDoneCols) {
          const tasks = board.columns[col] || [];
          const task = tasks.find(t => t.id === taskId);
          if (task) {
            // move without triggering daily XP again (pass silent flag)
            board.columns[col] = tasks.filter(t => t.id !== taskId);
            if (!Array.isArray(board.columns.done)) board.columns.done = [];
            board.columns.done.push(task);
            task.completedAt = now();
            task.updatedAt = now();
            board.updatedAt = now();
            milestone.updatedAt = now();
            touchProject(project);
            markDirty();
            // re-render if project is currently open
            if (S.view === 'projects' && S.activeProjectId === project.id) {
              renderProjectWorkspace(project);
            }
            return;
          }
        }
      }
    }
  }
}

function renderDailyExtras(content) {
  const days = [...S.dailies.days]
    .map(ensureDailyDayShape)
    .filter(day => (day.columns.extra || []).length)
    .sort((a, b) => String(b.date || '').localeCompare(String(a.date || '')));
  content.innerHTML = `
    <div class="daily-extras-page">
      <div class="toolbar daily-extras-toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">Extra tasks</div>
        </div>
        <div class="toolbar-right">
          <button class="inline-btn" id="daily-extras-add">+ Today extra</button>
        </div>
      </div>
      <div class="daily-extras-list" id="daily-extras-list"></div>
    </div>`;
  $('daily-extras-add').onclick = () => addDailyExtraQuestFlow(getOrCreateDailyDay(todayISO()), () => renderDailies());
  const list = $('daily-extras-list');
  if (!days.length) {
    list.innerHTML = `
      <div class="empty-state compact-empty">
        <div class="empty-box">
          <div class="empty-title">No extra tasks</div>
          <button class="inline-btn" id="daily-extras-empty-add">+ Today extra</button>
        </div>
      </div>`;
    $('daily-extras-empty-add').onclick = $('daily-extras-add').onclick;
    return;
  }
  days.forEach(day => {
    const stats = dailyStats(day);
    const section = document.createElement('section');
    section.className = 'daily-extra-day';
    section.innerHTML = `
      <div class="daily-extra-day-head">
        <div>
          <div class="eyebrow">${esc(day.date)}</div>
          <h3>${esc(formatDateTitle(day.date))}</h3>
        </div>
        <span>${stats.extraDone}/${stats.extraTotal}</span>
      </div>
      <div class="daily-extra-day-list"></div>`;
    renderDailyExtraList(day, section.querySelector('.daily-extra-day-list'), () => renderDailies());
    list.appendChild(section);
  });
}

function renderDailyDayPanel(content, day, prefix) {
  ensureDailyDayShape(day);
  syncDailyDayStatus(day);
  const stats = dailyStats(day);
  content.innerHTML = `
    <div class="daily-day-layout daily-day-layout-wide">
      <section class="daily-board-panel daily-board-full">
        <div class="daily-day-head">
          <div>
            <div class="eyebrow">${esc(formatDateTitle(day.date))}</div>
            <h2 class="daily-day-title">${esc(day.title || formatDateTitle(day.date))}</h2>
          </div>
          <div class="daily-head-actions">
            <div class="daily-status daily-status-${esc(day.status)}">${esc(day.status)}</div>
            <span class="daily-mini-summary">
              <span>${stats.todo} todo</span>
              <span>${stats.dailyDone} done</span>
              <span>${stats.extraDone}/${stats.extraTotal} extra</span>
            </span>
          </div>
        </div>
        <div class="daily-simple-progress"><span style="width:${stats.pct}%"></span><strong>${stats.done} / ${stats.total}</strong></div>
        <div class="daily-kanban-wrap" id="${esc(prefix)}-daily-board"></div>
      </section>
      <aside class="daily-journal-panel daily-journal-compact">
        ${dailyExternalWorkHTML(day.date)}
        <div class="field">
          <label class="field-label">Day comment</label>
          <textarea class="text-area daily-journal" id="${esc(prefix)}-daily-journal" placeholder="How did this day go?">${esc(day.journal || '')}</textarea>
        </div>
      </aside>
    </div>`;
  $(`${prefix}-daily-journal`).oninput = e => {
    day.journal = e.target.value;
    day.updatedAt = now();
    S.dailies.updatedAt = now();
    markDirty();
  };
  renderDailyKanban(day, $(`${prefix}-daily-board`), () => renderDailies());
}

function renderDailyKanban(day, host, rerender) {
  if (!host) return;
  ensureDailyDayShape(day);
  host.innerHTML = '<div class="kanban-columns daily-columns"></div>';
  const columns = host.querySelector('.daily-columns');

  // All columns: extras first, then todo, done
  const allColumns = [
    ['extra', 'Extra'],
    ...DAILY_COLUMNS,
  ];

  allColumns.forEach(([key, label]) => {
    const col = document.createElement('section');
    const isExtra = key === 'extra';
    col.className = `kanban-column daily-column daily-column-${key}${isExtra ? ' daily-column-extra-kanban' : ''}`;
    const quests = day.columns[key] || [];
    col.innerHTML = `
      <div class="kanban-column-head">
        <span>${esc(label)}</span>
        <span class="kanban-column-tools">
          <button class="column-sort-btn" data-sort-daily="${esc(key)}">Sort</button>
          <span class="column-count">${quests.length}</span>
        </span>
      </div>
      <button class="mini-add-task" data-add-daily="${esc(key)}">+ ${isExtra ? 'Extra' : 'Quest'}</button>
      <div class="task-list" data-daily-column="${esc(key)}"></div>`;

    col.querySelector('[data-add-daily]').onclick = () => {
      if (isExtra) addDailyExtraQuestFlow(day, rerender);
      else addDailyQuestFlow(day, key, rerender);
    };
    col.querySelector('[data-sort-daily]').onclick = () => {
      sortByImportance(day.columns[key]);
      touchDailyDay(day);
      markDirty();
      rerender();
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
      const payload = JSON.parse(e.dataTransfer.getData('application/x-refboard-daily-task') || '{}');
      if (!payload.taskId || payload.date !== day.date) return;
      if (isExtra) {
        // Move to extra column
        moveDailyQuestToExtra(day, payload.columnKey, payload.taskId, rerender);
      } else if (payload.columnKey === 'extra') {
        // Move from extra to regular column
        moveDailyQuestFromExtra(day, payload.taskId, key, rerender);
      } else {
        moveDailyQuest(day, payload.columnKey, payload.taskId, key, rerender);
      }
    });

    if (isExtra) {
      quests.forEach(quest => taskList.appendChild(buildDailyExtraCard(day, quest, rerender)));
    } else {
      quests.forEach(quest => taskList.appendChild(buildDailyQuestCard(day, key, quest, rerender)));
    }
    columns.appendChild(col);
  });
}

function moveDailyQuestToExtra(day, fromColumn, taskId, rerender) {
  if (fromColumn === 'extra') return;
  const list = day.columns[fromColumn] || [];
  const quest = list.find(item => item.id === taskId);
  if (!quest) return;
  day.columns[fromColumn] = list.filter(item => item.id !== taskId);
  quest.source = 'extra';
  quest.completedAt = null;
  quest.updatedAt = now();
  day.columns.extra = day.columns.extra || [];
  day.columns.extra.push(quest);
  touchDailyDay(day);
  markDirty();
  rerender();
}

function moveDailyQuestFromExtra(day, taskId, toColumn, rerender) {
  const list = day.columns.extra || [];
  const quest = list.find(item => item.id === taskId);
  if (!quest) return;
  day.columns.extra = list.filter(item => item.id !== taskId);
  quest.source = 'manual';
  if (toColumn === 'done') quest.completedAt = now();
  else quest.completedAt = null;
  quest.updatedAt = now();
  day.columns[toColumn] = day.columns[toColumn] || [];
  day.columns[toColumn].push(quest);
  touchDailyDay(day);
  markDirty();
  rerender();
}

function buildDailyQuestCard(day, columnKey, quest, rerender) {
  ensureDailyQuestShape(quest);
  const card = document.createElement('div');
  const done = columnKey === 'done' || !!quest.completedAt;
  card.className = `task-card daily-task-card task-importance-${esc(importanceLevel(quest.importance).id)}${done ? ' task-done' : ''}`;
  card.draggable = true;
  card.addEventListener('dragstart', e => {
    if (e.target.closest('input, textarea, button, .rarity-badge')) {
      e.preventDefault();
      return;
    }
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('application/x-refboard-daily-task', JSON.stringify({
      date: day.date,
      columnKey,
      taskId: quest.id,
    }));
    card.classList.add('dragging');
  });
  card.addEventListener('dragend', () => card.classList.remove('dragging'));
  const nextColumn = columnKey === 'done' ? 'todo' : 'done';
  const actionLabel = columnKey === 'done' ? 'Return' : 'Done';
  card.innerHTML = `
    <div class="task-card-top daily-task-top">
      ${importanceBadgeHTML(quest.importance)}
      <input class="daily-task-title-input" value="${esc(quest.title || '')}">
      ${done ? '<span class="task-done-mark">Done</span>' : ''}
      <button class="mini-btn daily-complete-btn">${esc(actionLabel)}</button>
    </div>
    <textarea class="daily-task-notes" placeholder="Quest note...">${esc(quest.notes || '')}</textarea>
    <div class="daily-task-foot">
      <span>${done ? `done${quest.completedAt ? ` ${formatShortDate(quest.completedAt)}` : ''}` : quest.source === 'default' ? 'default' : 'manual'}</span>
      <button class="mini-btn danger-lite daily-delete-quest">Delete</button>
    </div>`;
  bindImportanceTriggers(card, () => quest.importance, value => {
    quest.importance = value;
    touchDailyDay(day);
    markDirty();
    rerender();
  });
  card.querySelector('.daily-task-title-input').oninput = e => {
    quest.title = e.target.value;
    quest.updatedAt = now();
    touchDailyDay(day);
    markDirty();
  };
  card.querySelector('.daily-task-notes').oninput = e => {
    quest.notes = e.target.value;
    quest.updatedAt = now();
    touchDailyDay(day);
    markDirty();
  };
  card.querySelector('.daily-complete-btn').onclick = () => moveDailyQuest(day, columnKey, quest.id, nextColumn, rerender);
  card.querySelector('.daily-delete-quest').onclick = () => {
    if (!confirm(`Delete "${quest.title}"?`)) return;
    day.columns[columnKey] = (day.columns[columnKey] || []).filter(item => item.id !== quest.id);
    updateDailyCompletion(day);
    touchDailyDay(day);
    markDirty();
    rerender();
  };
  return card;
}

function addDailyQuestFlow(day, columnKey, rerender) {
  askText('New Daily Quest', '', 'Create', title => {
    const quest = createDailyQuest(title, 'manual');
    quest.importance = 'common';
    if (columnKey === 'done') quest.completedAt = now();
    day.columns[columnKey].push(quest);
    updateDailyCompletion(day);
    touchDailyDay(day);
    markDirty();
    rerender();
  });
}

function moveDailyQuest(day, fromColumn, taskId, toColumn, rerender) {
  if (fromColumn === toColumn) return;
  const list = day.columns[fromColumn] || [];
  const quest = list.find(item => item.id === taskId);
  if (!quest || !day.columns[toColumn]) return;
  const beforeStats = dailyStats(day);
  day.columns[fromColumn] = list.filter(item => item.id !== taskId);
  day.columns[toColumn].push(quest);
  quest.completedAt = toColumn === 'done' ? now() : null;
  quest.updatedAt = now();
  touchDailyDay(day);
  updateDailyCompletion(day, beforeStats, quest, toColumn);
  markDirty();
  rerender();
}

function touchDailyDay(day) {
  day.updatedAt = now();
  S.dailies.updatedAt = now();
  syncDailyDayStatus(day);
}

function updateDailyCompletion(day, beforeStats = dailyStats(day), quest = null, toColumn = null) {
  const beforeComplete = beforeStats.complete;
  syncDailyDayStatus(day);
  const stats = dailyStats(day);
  if (quest && toColumn === 'done') showDailyQuestDoneEffect(quest);
  if (stats.total && stats.complete && !beforeComplete && !day.celebratedAt) {
    day.celebratedAt = now();
    showDailyAllDoneEffect(day);
  }
}

function refreshDailyStatusForDate(date) {
  if (!date || !S.dailies) return;
  const day = getDailyDay(date);
  if (!day) return;
  syncDailyDayStatus(day);
  day.updatedAt = now();
  S.dailies.updatedAt = now();
}

function renderDailyDefaults(content) {
  const activeCategory = getActiveDailyTemplateCategory();
  const templates = dailyTemplatesForCategory(activeCategory.id);
  content.innerHTML = `
    <div class="daily-defaults">
      <div class="toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">Default quests / ${esc(activeCategory.title)}</div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="apply-defaults-today">Apply to today</button>
          <button class="ghost-btn" id="add-daily-template-category">+ Category</button>
          <button class="ghost-btn" id="rename-daily-template-category">Rename</button>
          <button class="mini-btn danger-lite" id="delete-daily-template-category">Delete Category</button>
          <button class="inline-btn" id="add-daily-template">+ Quest</button>
        </div>
      </div>
      <div class="daily-template-categories" id="daily-template-categories"></div>
      <div class="daily-template-list" id="daily-template-list"></div>
    </div>`;
  $('add-daily-template').onclick = () => addDailyTemplateFlow();
  $('add-daily-template-category').onclick = addDailyTemplateCategoryFlow;
  $('rename-daily-template-category').onclick = renameDailyTemplateCategory;
  $('delete-daily-template-category').onclick = deleteDailyTemplateCategory;
  $('apply-defaults-today').onclick = () => {
    const added = applyDefaultTemplatesToDay(getOrCreateDailyDay(todayISO()), activeCategory.id);
    markDirty();
    renderDailies();
    toast(added ? `Added: ${added}` : 'Already added');
  };
  renderDailyTemplateCategoryTabs();
  const list = $('daily-template-list');
  if (!templates.length) {
    list.innerHTML = `
      <div class="empty-state compact-empty">
        <div class="empty-box">
          <div class="empty-title">No defaults</div>
          <button class="inline-btn" id="empty-add-daily-template">+ Quest</button>
        </div>
      </div>`;
    $('empty-add-daily-template').onclick = () => addDailyTemplateFlow();
    return;
  }
  templates.forEach((template, index) => {
    const card = document.createElement('div');
    card.className = `daily-template-card task-importance-${esc(importanceLevel(template.importance).id)}`;
    card.innerHTML = `
      <label class="check-wrap compact-check">
        <input type="checkbox" class="daily-template-enabled" ${template.enabled !== false ? 'checked' : ''}>
        Enabled
      </label>
      ${importanceBadgeHTML(template.importance)}
      <input class="text-input daily-template-title" value="${esc(template.title || '')}">
      <textarea class="text-area compact-prompt daily-template-notes" placeholder="Optional note...">${esc(template.notes || '')}</textarea>
      <div class="card-actions">
        <button class="mini-btn daily-template-up" ${index === 0 ? 'disabled' : ''}>Up</button>
        <button class="mini-btn daily-template-down" ${index === templates.length - 1 ? 'disabled' : ''}>Down</button>
        <button class="mini-btn danger-lite daily-template-delete">Delete</button>
      </div>`;
    bindImportanceTriggers(card, () => template.importance, value => {
      template.importance = value;
      template.updatedAt = now();
      S.dailies.updatedAt = now();
      markDirty();
      renderDailies();
    });
    card.querySelector('.daily-template-enabled').onchange = e => {
      template.enabled = e.target.checked;
      template.updatedAt = now();
      S.dailies.updatedAt = now();
      markDirty();
    };
    card.querySelector('.daily-template-title').oninput = e => {
      template.title = e.target.value;
      template.updatedAt = now();
      S.dailies.updatedAt = now();
      markDirty();
    };
    card.querySelector('.daily-template-notes').oninput = e => {
      template.notes = e.target.value;
      template.updatedAt = now();
      S.dailies.updatedAt = now();
      markDirty();
    };
    card.querySelector('.daily-template-up').onclick = () => moveDailyTemplate(template.id, -1);
    card.querySelector('.daily-template-down').onclick = () => moveDailyTemplate(template.id, 1);
    card.querySelector('.daily-template-delete').onclick = () => {
      if (!confirm(`Delete "${template.title}"?`)) return;
      S.dailies.templates = S.dailies.templates.filter(item => item.id !== template.id);
      normalizeDailyTemplateOrder(template.categoryId);
      S.dailies.updatedAt = now();
      markDirty();
      renderDailies();
    };
    list.appendChild(card);
  });
}

function renderDailyTemplateCategoryTabs() {
  const wrap = $('daily-template-categories');
  if (!wrap) return;
  wrap.innerHTML = '';
  S.dailies.templateCategories.forEach(category => {
    const btn = document.createElement('button');
    btn.className = 'chip-btn' + (sameId(category.id, S.dailies.activeTemplateCategoryId) ? ' active' : '');
    btn.textContent = `${category.title} (${dailyTemplatesForCategory(category.id).length})`;
    btn.onclick = () => {
      S.dailies.activeTemplateCategoryId = category.id;
      S.dailies.updatedAt = now();
      markDirty();
      renderDailies();
    };
    wrap.appendChild(btn);
  });
}

function addDailyTemplateCategoryFlow() {
  askText('New Daily Template Category', '', 'Create', title => {
    const category = ensureDailyTemplateCategoryShape({ id: 'dtcat_' + uid(), title, createdAt: now(), updatedAt: now() }, S.dailies.templateCategories.length);
    S.dailies.templateCategories.push(category);
    S.dailies.activeTemplateCategoryId = category.id;
    S.dailies.updatedAt = now();
    markDirty();
    renderDailies();
  });
}

function renameDailyTemplateCategory() {
  const category = getActiveDailyTemplateCategory();
  if (!category) return;
  askText('Rename Template Category', category.title || '', 'Save', title => {
    category.title = title;
    category.updatedAt = now();
    S.dailies.updatedAt = now();
    markDirty();
    renderDailies();
  });
}

function deleteDailyTemplateCategory() {
  const category = getActiveDailyTemplateCategory();
  if (!category) return;
  if (S.dailies.templateCategories.length <= 1) {
    toast('Keep one category');
    return;
  }
  if (!confirm(`Delete category "${category.title}"? Its quests move to the first category.`)) return;
  const next = S.dailies.templateCategories.find(item => !sameId(item.id, category.id));
  S.dailies.templates.forEach(template => {
    if (sameId(template.categoryId, category.id)) template.categoryId = next.id;
  });
  S.dailies.templateCategories = S.dailies.templateCategories.filter(item => !sameId(item.id, category.id));
  S.dailies.activeTemplateCategoryId = next.id;
  normalizeDailyTemplateOrder(next.id);
  S.dailies.updatedAt = now();
  markDirty();
  renderDailies();
}

function addDailyTemplateFlow() {
  askText('New Default Quest', '', 'Create', title => {
    S.dailies.templates.push(createDailyTemplate(title));
    normalizeDailyTemplateOrder(S.dailies.activeTemplateCategoryId);
    S.dailies.updatedAt = now();
    markDirty();
    renderDailies();
  });
}

function normalizeDailyTemplateOrder(categoryId = null) {
  const categoryIds = categoryId
    ? [categoryId]
    : (S.dailies.templateCategories || []).map(category => category.id);
  categoryIds.forEach(id => {
    dailyTemplatesForCategory(id).forEach((template, index) => {
      template.order = index;
      template.updatedAt = now();
    });
  });
}

function moveDailyTemplate(templateId, offset) {
  const template = S.dailies.templates.find(item => sameId(item.id, templateId));
  if (!template) return;
  const list = dailyTemplatesForCategory(template.categoryId);
  const index = list.findIndex(item => sameId(item.id, template.id));
  const to = index + offset;
  if (index < 0 || to < 0 || to >= list.length) return;
  const [moved] = list.splice(index, 1);
  list.splice(to, 0, moved);
  list.forEach((item, nextIndex) => {
    item.order = nextIndex;
    item.updatedAt = now();
  });
  S.dailies.updatedAt = now();
  markDirty();
  renderDailies();
}

function applyDefaultTemplatesToDay(day, categoryId = getActiveDailyTemplateCategory()?.id) {
  const existing = new Set(DAILY_COLUMNS.flatMap(([key]) => (day.columns[key] || []).map(quest => quest.sourceTemplateId)).filter(Boolean));
  let added = 0;
  dailyTemplatesForCategory(categoryId)
    .filter(template => template.enabled !== false)
    .forEach(template => {
      if (existing.has(template.id)) return;
      day.columns.todo.push(createDailyQuestFromTemplate(template));
      existing.add(template.id);
      added += 1;
    });
  if (added) {
    touchDailyDay(day);
    S.dailies.updatedAt = now();
  }
  return added;
}

function renderDailyCalendar(content) {
  const today = todayISO();
  const start = getDailiesStartDate();
  const month = S.dailyCalendarMonth || monthISO(today);
  S.dailyCalendarMonth = month;
  if (!S.activeDailyDate || String(S.activeDailyDate) < String(start) || String(S.activeDailyDate) > String(today)) {
    S.activeDailyDate = today;
  }
  content.innerHTML = `
    <div class="daily-calendar-layout">
      <section class="daily-calendar-panel">
        <div class="daily-calendar-head">
          <button class="mini-btn" id="daily-month-prev">&lt;</button>
          <div class="daily-calendar-title">${esc(formatCalendarMonth(month))}</div>
          <button class="mini-btn" id="daily-month-next">&gt;</button>
          <button class="ghost-btn" id="daily-month-today">Today</button>
        </div>
        <div class="daily-calendar-grid" id="daily-calendar-grid"></div>
      </section>
      <section class="daily-calendar-detail" id="daily-calendar-detail"></section>
    </div>`;
  $('daily-month-prev').onclick = () => {
    S.dailyCalendarMonth = shiftMonthISO(month, -1);
    renderDailies();
  };
  $('daily-month-next').onclick = () => {
    S.dailyCalendarMonth = shiftMonthISO(month, 1);
    renderDailies();
  };
  $('daily-month-today').onclick = () => {
    S.activeDailyDate = today;
    S.dailyCalendarMonth = monthISO(today);
    renderDailies();
  };
  renderCalendarCells(month, start, today);
  const selected = getOrCreateDailyDay(S.activeDailyDate);
  renderDailyDayPanel($('daily-calendar-detail'), selected, 'calendar');
}

function renderCalendarCells(month, start, today) {
  const grid = $('daily-calendar-grid');
  const [year, monthIndex] = month.split('-').map(Number);
  const first = new Date(year, monthIndex - 1, 1);
  const daysInMonth = new Date(year, monthIndex, 0).getDate();
  const offset = first.getDay();
  grid.innerHTML = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat']
    .map(label => `<div class="calendar-weekday">${label}</div>`)
    .join('');
  for (let i = 0; i < offset; i++) {
    const blank = document.createElement('div');
    blank.className = 'calendar-day blank';
    grid.appendChild(blank);
  }
  for (let dayNum = 1; dayNum <= daysInMonth; dayNum++) {
    const date = `${year}-${String(monthIndex).padStart(2, '0')}-${String(dayNum).padStart(2, '0')}`;
    const day = getDailyDay(date);
    const stats = day ? dailyStats(day) : { total: 0, done: 0, pct: 0 };
    const paused = isDailiesPausedDate(date);
    const status = paused ? 'paused' : day ? day.status : String(date) < String(today) && String(date) >= String(start) ? 'failed' : 'empty';
    const locked = paused || String(date) < String(start) || String(date) > String(today);
    const cell = document.createElement('button');
    cell.className = `calendar-day status-${status}${date === S.activeDailyDate ? ' active' : ''}${locked ? ' locked' : ''}`;
    cell.disabled = locked;
    cell.innerHTML = `
      <span class="calendar-day-num">${dayNum}</span>
      <span class="calendar-day-pct">${paused ? 'pause' : stats.total ? `${stats.done}/${stats.total}` : '-'}</span>`;
    cell.onclick = () => {
      S.activeDailyDate = date;
      S.dailyCalendarMonth = monthISO(date);
      getOrCreateDailyDay(date);
      renderDailies();
    };
    grid.appendChild(cell);
  }
}

function formatCalendarMonth(month) {
  try {
    return new Intl.DateTimeFormat('en-US', { month: 'long', year: 'numeric' }).format(new Date(month + '-01T00:00:00'));
  } catch (e) {
    return month;
  }
}

function shiftMonthISO(month, offset) {
  const [year, monthIndex] = String(month || monthISO()).split('-').map(Number);
  const date = new Date(year, monthIndex - 1 + offset, 1);
  return monthISO(dateToISO(date));
}

function showDailyQuestDoneEffect(quest) {
  const effect = document.createElement('div');
  effect.className = 'daily-quest-effect';
  effect.innerHTML = `
    <span class="daily-effect-xp">+1 done</span>
    <span class="daily-effect-title">${esc(quest.title || 'Done')}</span>`;
  document.body.appendChild(effect);
  setTimeout(() => effect.classList.add('show'), 20);
  setTimeout(() => effect.remove(), 1200);
}

function showDailyAllDoneEffect(day) {
  const old = $('daily-complete-effect');
  if (old) old.remove();
  const effect = document.createElement('div');
  effect.id = 'daily-complete-effect';
  effect.innerHTML = `
    <div class="complete-burst daily-complete-burst">
      <div class="complete-title">All Dailies Done</div>
      <div class="complete-name">${esc(formatDateTitle(day.date))}</div>
    </div>`;
  document.body.appendChild(effect);
  setTimeout(() => effect.classList.add('show'), 20);
  setTimeout(() => effect.remove(), 1900);
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

function getDrawingMedia() {
  S.drawing = ensureDrawingShape(S.drawing);
  return S.media
    .map(ensureMediaShape)
    .filter(media => media.gameId === S.drawing.id && media.scope === 'drawing' && media.kind === 'photo')
    .sort((a, b) => (a.order ?? 0) - (b.order ?? 0) || String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
}

function renderDrawing() {
  stopViewer();
  hidePlayback();
  S.drawing = ensureDrawingShape(S.drawing);
  if (!S.drawing.categoryOpen) {
    renderDrawingCategoryLibrary();
    return;
  }
  renderDrawingCategoryDetail();
}

function renderDrawingCategoryLibrary() {
  S.drawing = ensureDrawingShape(S.drawing);
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Drawing</h1>
        </div>
        <div class="head-actions">
          <button class="inline-btn" id="drawing-new-category">+ Category</button>
        </div>
      </div>
      <div class="screen-scroll" id="drawing-category-body"></div>
    </section>`;
  $('drawing-new-category').onclick = () => createMediaCategoryFlow(S.drawing, 'photo', () => {
    S.drawing.categoryOpen = true;
    S.drawing.updatedAt = now();
    markDirty();
    renderDrawing();
  });

  const body = $('drawing-category-body');
  const categories = getMediaCategories(S.drawing, 'photo');
  body.innerHTML = '<div class="category-card-grid" id="drawing-category-grid"></div>';
  const grid = $('drawing-category-grid');
  categories.forEach(category => {
    const items = getDrawingMedia().filter(item => item.categoryId === category.id);
    const cover = items[0];
    const card = document.createElement('button');
    card.className = 'category-card media-category-card';
    card.innerHTML = `
      <div class="category-card-cover">${cover ? mediaPreviewHTML(cover, true) : 'R'}</div>
      <div class="category-card-main">
        <div class="category-card-title">${esc(category.title)}</div>
        <div class="card-sub">${items.length} images</div>
      </div>`;
    card.onclick = () => {
      setActiveMediaCategory(S.drawing, 'photo', category.id);
      S.drawing.categoryOpen = true;
      S.drawing.updatedAt = now();
      markDirty();
      renderDrawing();
    };
    grid.appendChild(card);
  });
}

function renderDrawingCategoryDetail() {
  S.drawing = ensureDrawingShape(S.drawing);
  const activeCategory = getActiveMediaCategory(S.drawing, 'photo');
  const items = getDrawingMedia().filter(item => item.categoryId === activeCategory.id);
  $('main').innerHTML = `
    <section class="screen">
      <div class="screen-head roomy-head">
        <div class="title-wrap">
          <input id="drawing-category-title" class="section-title-input" value="${esc(activeCategory.title)}">
        </div>
        <div class="head-actions">
          <button class="ghost-btn" id="drawing-back-categories">Categories</button>
          <button class="ghost-btn" id="drawing-sort-media">Sort importance</button>
          <button class="inline-btn" id="drawing-add-media">+ Images</button>
          <button class="danger-btn" id="drawing-delete-category">Delete Category</button>
        </div>
      </div>
      <div class="tab-scroll">
        <div class="project-media-grid" id="drawing-media-grid"></div>
      </div>
    </section>`;

  $('drawing-back-categories').onclick = () => {
    S.drawing.categoryOpen = false;
    S.drawing.updatedAt = now();
    markDirty();
    renderDrawing();
  };
  $('drawing-category-title').oninput = e => {
    activeCategory.title = e.target.value;
    activeCategory.updatedAt = now();
    S.drawing.updatedAt = now();
    markDirty();
  };
  $('drawing-delete-category').onclick = () => deleteDrawingCategory(activeCategory);
  $('drawing-add-media').onclick = addDrawingMedia;
  $('drawing-sort-media').onclick = () => {
    const sortable = getDrawingMedia().filter(item => item.categoryId === activeCategory.id);
    sortMediaByImportance(sortable);
    S.drawing.updatedAt = now();
    markDirty();
    renderDrawing();
  };

  const grid = $('drawing-media-grid');
  if (!items.length) {
    grid.innerHTML = `<button class="album-drop-card fixed-drop" id="drawing-empty-media">+ Images</button>`;
    $('drawing-empty-media').onclick = addDrawingMedia;
    bindDrawingDrop(grid);
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
        <button class="mini-btn remove-drawing-media">x</button>
      </div>`;
    card.querySelector('.album-photo-open').onclick = () => openAlbumPhoto(item.id);
    bindImportanceTriggers(card, () => item.importance, value => {
      item.importance = value;
      item.updatedAt = now();
      S.drawing.updatedAt = now();
      markDirty();
      renderDrawing();
    });
    card.querySelector('.album-photo-title').oninput = e => {
      item.name = e.target.value;
      item.updatedAt = now();
      S.drawing.updatedAt = now();
      markDirty();
    };
    card.querySelector('.remove-drawing-media').onclick = () => removeDrawingMedia(item.id);
    bindSortableIdCard(card, item.id, 'application/x-refboard-drawing-media', (draggedId, beforeId) => {
      if (reorderMediaBefore(S.drawing.id, 'drawing', 'photo', activeCategory.id, draggedId, beforeId)) {
        S.drawing.updatedAt = now();
        markDirty();
        renderDrawing();
      }
    });
    grid.appendChild(card);
  });

  const add = document.createElement('button');
  add.className = 'album-drop-card fixed-drop';
  add.textContent = '+ Images';
  add.onclick = addDrawingMedia;
  grid.appendChild(add);
  const spacer = document.createElement('div');
  spacer.className = 'media-grid-spacer';
  spacer.addEventListener('dragover', e => {
    e.preventDefault();
    if (hasMoveDragType(e, 'application/x-refboard-drawing-media')) spacer.classList.add('drag-over');
  });
  spacer.addEventListener('dragleave', () => spacer.classList.remove('drag-over'));
  spacer.addEventListener('drop', e => {
    e.preventDefault();
    spacer.classList.remove('drag-over');
    const draggedId = getDraggedId(e, 'application/x-refboard-drawing-media');
    if (draggedId && reorderMediaBefore(S.drawing.id, 'drawing', 'photo', activeCategory.id, draggedId, null)) {
      S.drawing.updatedAt = now();
      markDirty();
      renderDrawing();
    }
  });
  grid.appendChild(spacer);
  bindDrawingDrop(grid);
}

function deleteDrawingCategory(category) {
  const categories = getMediaCategories(S.drawing, 'photo');
  if (categories.length <= 1) {
    toast('Keep one category');
    return;
  }
  if (!confirm(`Delete category "${category.title}"?`)) return;
  const mediaIds = new Set(getDrawingMedia().filter(item => item.categoryId === category.id).map(item => item.id));
  S.media = S.media.filter(item => !mediaIds.has(item.id));
  const [listKey, activeKey] = mediaCategoryConfig('photo');
  S.drawing[listKey] = categories.filter(item => !sameId(item.id, category.id));
  S.drawing[activeKey] = S.drawing[listKey][0]?.id || null;
  S.drawing.categoryOpen = false;
  S.drawing.updatedAt = now();
  markDirty();
  renderDrawing();
}

function bindDrawingDrop(target) {
  target.addEventListener('dragover', e => {
    if (Array.from(e.dataTransfer?.files || []).length) e.preventDefault();
  });
  target.addEventListener('drop', e => {
    const files = Array.from(e.dataTransfer?.files || []).map(file => file.path).filter(Boolean);
    if (!files.length) return;
    e.preventDefault();
    addDrawingFiles(files);
  });
}

async function addDrawingMedia() {
  const files = await pickMediaFiles('photo');
  addDrawingFiles(files);
}

function addDrawingFiles(files) {
  const valid = (files || []).filter(fp => kindAllowsFile('photo', fp));
  if (!valid.length) return;
  valid.forEach(fp => registerMediaFile(fp, S.drawing.id, 'photo', 'drawing'));
  S.drawing.updatedAt = now();
  markDirty();
  renderDrawing();
  toast(`Added: ${valid.length}`);
}

function removeDrawingMedia(mediaId) {
  const media = getMediaById(mediaId);
  if (!media) return;
  if (!confirm(`Remove "${media.name}"?`)) return;
  S.media = S.media.filter(item => item.id !== mediaId);
  S.drawing.updatedAt = now();
  markDirty();
  renderDrawing();
}

function renderMoodboard() {
  stopViewer();
  hidePlayback();
  S.moodboard = ensureMoodboardShape(S.moodboard);
  if (!S.moodboard.boardOpen) {
    renderMoodboardBoardLibrary();
    return;
  }
  renderMoodboardCanvas();
}

function renderMoodboardBoardLibrary() {
  S.moodboard = ensureMoodboardShape(S.moodboard);
  $('main').innerHTML = `
    <section class="screen moodboard-screen">
      <div class="screen-head">
        <div class="title-wrap">
          <h1 class="screen-title">Moodboard</h1>
        </div>
        <div class="head-actions">
          <button class="inline-btn" id="moodboard-new">+ Board</button>
        </div>
      </div>
      <div class="screen-scroll" id="moodboard-board-body"></div>
    </section>`;
  $('moodboard-new').onclick = createMoodboardBoardFlow;
  const body = $('moodboard-board-body');
  body.innerHTML = '<div class="category-card-grid" id="moodboard-board-grid"></div>';
  const grid = $('moodboard-board-grid');
  S.moodboard.boards.forEach(board => {
    const cover = (board.items || []).map(item => getMediaById(item.mediaId)).filter(Boolean)[0];
    const card = document.createElement('button');
    card.className = 'category-card media-category-card';
    card.innerHTML = `
      <div class="category-card-cover">${cover ? mediaPreviewHTML(cover, true) : 'B'}</div>
      <div class="category-card-main">
        <div class="category-card-title">${esc(board.title)}</div>
        <div class="card-sub">${(board.items || []).length} images</div>
      </div>`;
    card.onclick = () => {
      S.moodboard.activeBoardId = board.id;
      S.activeMoodboardId = board.id;
      S.moodboard.boardOpen = true;
      V.moodboardHistory = [];
      clearMoodboardSelection();
      S.moodboard.updatedAt = now();
      markDirty();
      renderMoodboard();
    };
    grid.appendChild(card);
  });
}

function saveMoodboardViewState(board) {
  if (!board) return;
  board.panX = V.mbPanX || 0;
  board.panY = V.mbPanY || 0;
}

function applyMoodboardTransform(canvas, board) {
  if (!canvas || !board) return;
  const zoom = board.zoom || 1;
  const px = V.mbPanX || 0;
  const py = V.mbPanY || 0;
  canvas.style.transform = `translate(${px}px, ${py}px) scale(${zoom})`;
  const label = $('moodboard-zoom-label');
  if (label) label.textContent = Math.round(zoom * 100) + '%';
}

function centerMoodboardView(board) {
  if (!board) return;
  const viewport = $('moodboard-viewport');
  if (!viewport) return;
  const vw = viewport.clientWidth;
  const vh = viewport.clientHeight;
  const zoom = board.zoom || 1;
  if (!board.items || !board.items.length) {
    V.mbPanX = vw / 2;
    V.mbPanY = vh / 2;
  } else {
    const bounds = moodboardBoundsForItems(board.items);
    if (!bounds) { V.mbPanX = vw / 2; V.mbPanY = vh / 2; }
    else {
      const cx = bounds.x + bounds.w / 2;
      const cy = bounds.y + bounds.h / 2;
      V.mbPanX = vw / 2 - cx * zoom;
      V.mbPanY = vh / 2 - cy * zoom;
    }
  }
  const canvas = $('moodboard-canvas');
  if (canvas) applyMoodboardTransform(canvas, board);
}

function renderMoodboardCanvas() {
  S.moodboard = ensureMoodboardShape(S.moodboard);
  const board = getActiveMoodboard();
  const zoom = board?.zoom || 1;

  // Restore pan state
  V.mbPanX = board?.panX ?? (V.mbPanX || 0);
  V.mbPanY = board?.panY ?? (V.mbPanY || 0);

  $('main').innerHTML = `
    <section class="screen moodboard-screen">
      <div class="screen-head roomy-head moodboard-toolbar">
        <div class="title-wrap">
          <span class="moodboard-board-name">${esc(board?.title || 'Board')}</span>
          <span class="moodboard-zoom-label" id="moodboard-zoom-label">${Math.round(zoom * 100)}%</span>
        </div>
        <div class="head-actions">
          <button class="ghost-btn" id="moodboard-add-media">+ Photos</button>
          <button class="ghost-btn" id="moodboard-undo">Undo</button>
          <button class="ghost-btn" id="moodboard-back-boards">Boards</button>
          <button class="ghost-btn" id="moodboard-new">+ Board</button>
          <button class="ghost-btn" id="moodboard-rename">Rename</button>
          <button class="danger-btn" id="moodboard-delete-board">Delete</button>
          <button class="danger-btn" id="moodboard-clear">Clear all</button>
        </div>
      </div>
      <div class="moodboard-viewport" id="moodboard-viewport">
        <div class="moodboard-canvas" id="moodboard-canvas"></div>
        ${!board?.items.length ? `
        <div class="moodboard-empty-overlay" id="moodboard-empty-overlay">
          <div class="moodboard-empty-box">
            <div class="moodboard-empty-icon">+</div>
            <div class="moodboard-empty-title">Drop images here</div>
            <div class="moodboard-empty-sub">or click to add photos to your board</div>
            <button class="inline-btn moodboard-empty-btn" id="moodboard-empty-add">+ Add Photos</button>
          </div>
        </div>` : ''}
      </div>
    </section>`;

  $('moodboard-back-boards').onclick = () => {
    saveMoodboardViewState(board);
    S.moodboard.boardOpen = false;
    clearMoodboardSelection();
    V.mbPanX = 0; V.mbPanY = 0;
    S.moodboard.updatedAt = now();
    markDirty();
    renderMoodboard();
  };
  $('moodboard-undo').onclick = undoMoodboard;
  $('moodboard-clear').onclick = clearMoodboard;
  $('moodboard-new').onclick = createMoodboardBoardFlow;
  $('moodboard-rename').onclick = () => renameMoodboardBoard(board);
  $('moodboard-delete-board').onclick = () => deleteMoodboardBoard(board);
  $('moodboard-add-media').onclick = addMoodboardMedia;
  if ($('moodboard-empty-add')) $('moodboard-empty-add').onclick = addMoodboardMedia;

  const viewport = $('moodboard-viewport');
  const canvas = $('moodboard-canvas');

  applyMoodboardTransform(canvas, board);
  renderMoodboardItems(board);
  bindMoodboardViewport(viewport, canvas, board);
  bindMoodboardMarquee(viewport, canvas, board);
  bindMoodboardDrop(viewport, canvas, board);

  if (!V.moodboardViewportReady) V.moodboardViewportReady = {};
  if (!V.moodboardViewportReady[board?.id]) {
    V.moodboardViewportReady[board?.id] = true;
    requestAnimationFrame(() => centerMoodboardView(board));
  }
}

function renderMoodboardTabs() {
  const tabs = $('moodboard-tabs');
  if (!tabs) return;
  tabs.innerHTML = '';
  S.moodboard.boards.forEach(board => {
    const btn = document.createElement('button');
    btn.className = 'chip-btn' + (sameId(board.id, S.moodboard.activeBoardId) ? ' active' : '');
    btn.textContent = board.title;
    btn.onclick = () => {
      S.moodboard.activeBoardId = board.id;
      S.activeMoodboardId = board.id;
      V.moodboardHistory = [];
      clearMoodboardSelection();
      S.moodboard.updatedAt = now();
      markDirty();
      renderMoodboard();
    };
    tabs.appendChild(btn);
  });
}

function createMoodboardBoardFlow() {
  askText('New Moodboard', '', 'Create', title => {
    const board = ensureMoodboardBoardShape({
      id: 'mb_' + uid(),
      title,
      items: [],
      zoom: 1,
      createdAt: now(),
      updatedAt: now(),
    }, S.moodboard.boards.length);
    S.moodboard.boards.push(board);
    S.moodboard.activeBoardId = board.id;
    S.activeMoodboardId = board.id;
    S.moodboard.boardOpen = true;
    V.moodboardHistory = [];
    clearMoodboardSelection();
    S.moodboard.updatedAt = now();
    markDirty();
    renderMoodboard();
  });
}

function renameMoodboardBoard(board) {
  if (!board) return;
  askText('Rename Moodboard', board.title || '', 'Save', title => {
    board.title = title;
    board.updatedAt = now();
    S.moodboard.updatedAt = now();
    markDirty();
    renderMoodboard();
  });
}

function deleteMoodboardBoard(board) {
  if (!board) return;
  if (S.moodboard.boards.length <= 1) {
    toast('Keep one board');
    return;
  }
  if (!confirm(`Delete moodboard "${board.title}"?`)) return;
  const mediaIds = new Set((board.items || []).map(item => item.mediaId).filter(Boolean));
  S.media = S.media.filter(media => !mediaIds.has(media.id));
  S.moodboard.boards = S.moodboard.boards.filter(item => !sameId(item.id, board.id));
  S.moodboard.activeBoardId = S.moodboard.boards[0]?.id || null;
  S.activeMoodboardId = S.moodboard.activeBoardId;
  S.moodboard.boardOpen = false;
  V.moodboardHistory = [];
  clearMoodboardSelection();
  S.moodboard.updatedAt = now();
  markDirty();
  renderMoodboard();
}

function moodboardDimensions(board = getActiveMoodboard()) {
  const items = board?.items || [];
  const minX = Math.min(0, ...items.map(item => Number(item.x || 0)));
  const minY = Math.min(0, ...items.map(item => Number(item.y || 0)));
  const maxX = Math.max(0, ...items.map(item => Number(item.x || 0) + Number(item.w || 0)));
  const maxY = Math.max(0, ...items.map(item => Number(item.y || 0) + Number(item.h || 0)));
  if (board) {
    board.originX = Math.max(Number(board.originX || MOODBOARD_WORLD_MARGIN), Math.ceil(MOODBOARD_WORLD_MARGIN - minX));
    board.originY = Math.max(Number(board.originY || MOODBOARD_WORLD_MARGIN), Math.ceil(MOODBOARD_WORLD_MARGIN - minY));
  }
  const originX = Number(board?.originX || MOODBOARD_WORLD_MARGIN);
  const originY = Number(board?.originY || MOODBOARD_WORLD_MARGIN);
  const width = Math.max(MOODBOARD_WORLD_MIN_WIDTH, Math.ceil(originX + maxX + MOODBOARD_WORLD_MARGIN));
  const height = Math.max(MOODBOARD_WORLD_MIN_HEIGHT, Math.ceil(originY + maxY + MOODBOARD_WORLD_MARGIN));
  return { width, height, originX, originY };
}

function updateMoodboardSpaceSize(board = getActiveMoodboard()) {
  const canvas = $('moodboard-canvas');
  if (!canvas) return;
  applyMoodboardTransform(canvas, board);
  syncMoodboardRenderedPositions(board);
}

function syncMoodboardRenderedPositions(board = getActiveMoodboard()) {
  const canvas = $('moodboard-canvas');
  if (!canvas || !board) return;
  canvas.querySelectorAll('.moodboard-item').forEach(el => {
    const item = (board.items || []).find(next => sameId(next.id, el.dataset.itemId));
    if (item) setMoodboardItemStyle(el, item);
  });
  syncMoodboardSelectionBox(board);
}

function centerMoodboardViewportIfNeeded(scroll, board, dims = moodboardDimensions(board), zoom = board?.zoom || 1) {
  if (!scroll || !board) return;
  if (!V.moodboardViewportReady || typeof V.moodboardViewportReady !== 'object') V.moodboardViewportReady = {};
  if (V.moodboardViewportReady[board.id]) return;
  V.moodboardViewportReady[board.id] = true;
  requestAnimationFrame(() => {
    const bounds = moodboardBoundsForItems(board.items || []) || { x: 0, y: 0, w: 1, h: 1 };
    const targetX = dims.originX + bounds.x + bounds.w / 2;
    const targetY = dims.originY + bounds.y + bounds.h / 2;
    scroll.scrollLeft = Math.max(0, targetX * zoom - scroll.clientWidth / 2);
    scroll.scrollTop = Math.max(0, targetY * zoom - scroll.clientHeight / 2);
  });
}

function renderMoodboardItems(board = getActiveMoodboard()) {
  const space = $('moodboard-canvas');
  if (!space) return;
  const selectedIds = new Set(moodboardSelectionIds(board));
  (board?.items || [])
    .map(ensureMoodboardItemShape)
    .sort((a, b) => (a.z ?? 0) - (b.z ?? 0))
    .forEach(item => {
      const media = getMediaById(item.mediaId);
      const el = document.createElement('div');
      el.className = 'moodboard-item' + (selectedIds.has(item.id) ? ' selected' : '');
      el.dataset.itemId = item.id;
      setMoodboardItemStyle(el, item);
      el.innerHTML = `
        <div class="moodboard-image">${media ? mediaPreviewHTML(media, true) : '<span>Missing</span>'}</div>
        <button class="moodboard-delete" title="Delete">x</button>
        <span class="moodboard-resize" title="Resize"></span>`;
      el.ondblclick = e => {
        if (e.target.closest('button, .moodboard-resize')) return;
        if (media) openAlbumPhoto(media.id);
      };
      el.querySelector('.moodboard-delete').onclick = e => {
        e.stopPropagation();
        removeMoodboardItem(board, item.id);
      };
      el.addEventListener('pointerdown', e => {
        if (e.button !== 0) return;
        if (e.target.closest('button, .moodboard-resize')) return;
        if (e.ctrlKey || e.metaKey || e.shiftKey) {
          e.preventDefault();
          e.stopPropagation();
          toggleMoodboardSelection(item.id, board);
          renderMoodboard();
          return;
        }
        // If clicking a different item without modifier, select only it
        const sel = moodboardSelectionIds(board);
        if (!sel.includes(item.id) || sel.length > 1) {
          setMoodboardSelection([item.id], board);
          syncMoodboardSelectionClasses(board);
          renderMoodboardSelectionBox(board);
        }
        startMoodboardInteraction(e, board, item, el, 'move');
      });
      el.querySelector('.moodboard-resize').addEventListener('pointerdown', e => {
        if (!moodboardSelectionIds(board).includes(item.id)) setMoodboardSelection([item.id], board);
        startMoodboardInteraction(e, board, item, el, 'resize');
      });
      space.appendChild(el);
    });
  renderMoodboardSelectionBox(board);
}

function setMoodboardItemStyle(el, item) {
  el.style.left = `${Math.round(Number(item.x || 0))}px`;
  el.style.top = `${Math.round(Number(item.y || 0))}px`;
  el.style.width = `${Math.round(item.w)}px`;
  el.style.height = `${Math.round(item.h)}px`;
  el.style.zIndex = String(item.z || 1);
}

function moodboardSelectionIds(board = getActiveMoodboard()) {
  const valid = new Set((board?.items || []).map(item => item.id));
  V.moodboardSelection = (Array.isArray(V.moodboardSelection) ? V.moodboardSelection : [])
    .filter(id => valid.has(id));
  return V.moodboardSelection;
}

function setMoodboardSelection(ids = [], board = getActiveMoodboard()) {
  const valid = new Set((board?.items || []).map(item => item.id));
  V.moodboardSelection = [...new Set(ids)].filter(id => valid.has(id));
}

function toggleMoodboardSelection(itemId, board = getActiveMoodboard()) {
  const selected = new Set(moodboardSelectionIds(board));
  if (selected.has(itemId)) selected.delete(itemId);
  else selected.add(itemId);
  setMoodboardSelection([...selected], board);
}

function clearMoodboardSelection() {
  V.moodboardSelection = [];
}

function selectedMoodboardItems(board = getActiveMoodboard()) {
  const ids = new Set(moodboardSelectionIds(board));
  return (board?.items || []).filter(item => ids.has(item.id));
}

function getMoodboardItemElement(itemId) {
  const space = $('moodboard-canvas');
  if (!space) return null;
  return Array.from(space.querySelectorAll('.moodboard-item'))
    .find(el => el.dataset.itemId === String(itemId)) || null;
}

function syncMoodboardSelectionClasses(board = getActiveMoodboard()) {
  const space = $('moodboard-canvas');
  if (!space) return;
  const ids = new Set(moodboardSelectionIds(board));
  space.querySelectorAll('.moodboard-item').forEach(el => {
    el.classList.toggle('selected', ids.has(el.dataset.itemId));
  });
}

function moodboardClientPoint(e, canvas = $('moodboard-canvas'), board = getActiveMoodboard()) {
  // Convert screen coords to world coords
  const zoom = board?.zoom || 1;
  const px = V.mbPanX || 0;
  const py = V.mbPanY || 0;
  const viewport = $('moodboard-viewport');
  if (!viewport) return { x: 0, y: 0 };
  const rect = viewport.getBoundingClientRect();
  return {
    x: (e.clientX - rect.left - px) / zoom,
    y: (e.clientY - rect.top - py) / zoom,
  };
}

function moodboardItemRect(item) {
  return {
    x: Number(item.x || 0),
    y: Number(item.y || 0),
    w: Number(item.w || 0),
    h: Number(item.h || 0),
  };
}

function normalizeMoodboardRect(a, b) {
  const x = Math.min(a.x, b.x);
  const y = Math.min(a.y, b.y);
  return {
    x,
    y,
    w: Math.abs(a.x - b.x),
    h: Math.abs(a.y - b.y),
  };
}

function rectsIntersect(a, b) {
  return a.x < b.x + b.w
    && a.x + a.w > b.x
    && a.y < b.y + b.h
    && a.y + a.h > b.y;
}

function moodboardBoundsForItems(items) {
  if (!items.length) return null;
  const rects = items.map(moodboardItemRect);
  const left = Math.min(...rects.map(rect => rect.x));
  const top = Math.min(...rects.map(rect => rect.y));
  const right = Math.max(...rects.map(rect => rect.x + rect.w));
  const bottom = Math.max(...rects.map(rect => rect.y + rect.h));
  return { x: left, y: top, w: right - left, h: bottom - top };
}

function moodboardSelectionBounds(board = getActiveMoodboard()) {
  return moodboardBoundsForItems(selectedMoodboardItems(board));
}

function setMoodboardRectStyle(el, rect) {
  el.style.left = `${Math.round(rect.x)}px`;
  el.style.top = `${Math.round(rect.y)}px`;
  el.style.width = `${Math.max(1, Math.round(rect.w))}px`;
  el.style.height = `${Math.max(1, Math.round(rect.h))}px`;
}

function syncMoodboardSelectionBox(board = getActiveMoodboard()) {
  const box = $('moodboard-selection-box');
  const bounds = moodboardSelectionBounds(board);
  if (!box || !bounds) return;
  setMoodboardRectStyle(box, bounds);
}

function renderMoodboardSelectionBox(board = getActiveMoodboard()) {
  const space = $('moodboard-canvas');
  const items = selectedMoodboardItems(board);
  if (!space || items.length < 2) return;
  const bounds = moodboardBoundsForItems(items);
  if (!bounds) return;
  const box = document.createElement('div');
  box.id = 'moodboard-selection-box';
  box.className = 'moodboard-selection-box';
  setMoodboardRectStyle(box, bounds);
  box.innerHTML = ['nw', 'n', 'ne', 'e', 'se', 's', 'sw', 'w']
    .map(handle => `<span class="moodboard-selection-handle ${handle}" data-handle="${handle}"></span>`)
    .join('') +
    `<button class="moodboard-group-delete" title="Delete selected">×</button>`;
  box.addEventListener('pointerdown', e => {
    if (e.target.closest('.moodboard-selection-handle, .moodboard-group-delete')) return;
    startMoodboardGroupMove(e, board);
  });
  box.querySelectorAll('.moodboard-selection-handle').forEach(handle => {
    handle.addEventListener('pointerdown', e => {
      startMoodboardGroupResize(e, board, handle.dataset.handle);
    });
  });
  box.querySelector('.moodboard-group-delete').addEventListener('click', e => {
    e.stopPropagation();
    pushMoodboardUndo();
    const ids = new Set(moodboardSelectionIds(board));
    board.items = (board.items || []).filter(item => !ids.has(item.id));
    clearMoodboardSelection();
    board.updatedAt = now();
    S.moodboard.updatedAt = now();
    markDirty();
    renderMoodboard();
  });
  space.appendChild(box);
}

function touchMoodboardAfterInteraction(board, items = []) {
  const stamp = now();
  items.forEach(item => { item.updatedAt = stamp; });
  if (board) board.updatedAt = stamp;
  if (S.moodboard) S.moodboard.updatedAt = stamp;
}

function startMoodboardGroupMove(e, board) {
  if (e.button !== 0) return;
  const targets = selectedMoodboardItems(board);
  if (!targets.length) return;
  e.preventDefault();
  e.stopPropagation();
  pushMoodboardUndo();
  bringMoodboardItemsForward(board, targets);
  const startX = e.clientX;
  const startY = e.clientY;
  const zoom = board?.zoom || 1;
  const entries = targets.map(item => ({
    item,
    x: item.x,
    y: item.y,
    el: getMoodboardItemElement(item.id),
  }));
  entries.forEach(({ item, el }) => { if (el) setMoodboardItemStyle(el, item); });
  syncMoodboardSelectionBox(board);
  const onMove = moveEvent => {
    const dx = (moveEvent.clientX - startX) / zoom;
    const dy = (moveEvent.clientY - startY) / zoom;
    entries.forEach(({ item, x, y, el }) => {
      item.x = x + dx;
      item.y = y + dy;
      if (el) setMoodboardItemStyle(el, item);
    });
    touchMoodboardAfterInteraction(board, targets);
    updateMoodboardSpaceSize(board);
    syncMoodboardSelectionBox(board);
  };
  const onUp = () => {
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    markDirty();
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function startMoodboardGroupResize(e, board, handle = 'se') {
  if (e.button !== 0) return;
  const targets = selectedMoodboardItems(board);
  const startBounds = moodboardBoundsForItems(targets);
  if (targets.length < 2 || !startBounds || !startBounds.w || !startBounds.h) return;
  e.preventDefault();
  e.stopPropagation();
  pushMoodboardUndo();
  const startX = e.clientX;
  const startY = e.clientY;
  const zoom = board?.zoom || 1;
  const entries = targets.map(item => ({
    item,
    rect: moodboardItemRect(item),
    el: getMoodboardItemElement(item.id),
  }));
  const minBox = 120;
  const onMove = moveEvent => {
    const dx = (moveEvent.clientX - startX) / zoom;
    const dy = (moveEvent.clientY - startY) / zoom;
    let left = startBounds.x;
    let top = startBounds.y;
    let right = startBounds.x + startBounds.w;
    let bottom = startBounds.y + startBounds.h;
    if (handle.includes('w')) left = startBounds.x + dx;
    if (handle.includes('e')) right = startBounds.x + startBounds.w + dx;
    if (handle.includes('n')) top = startBounds.y + dy;
    if (handle.includes('s')) bottom = startBounds.y + startBounds.h + dy;
    if (right - left < minBox) {
      if (handle.includes('w')) left = right - minBox;
      else right = left + minBox;
    }
    if (bottom - top < minBox) {
      if (handle.includes('n')) top = bottom - minBox;
      else bottom = top + minBox;
    }
    const nextBounds = { x: left, y: top, w: right - left, h: bottom - top };
    const scaleX = nextBounds.w / startBounds.w;
    const scaleY = nextBounds.h / startBounds.h;
    entries.forEach(({ item, rect, el }) => {
      item.x = nextBounds.x + (rect.x - startBounds.x) * scaleX;
      item.y = nextBounds.y + (rect.y - startBounds.y) * scaleY;
      item.w = Math.max(80, rect.w * scaleX);
      item.h = Math.max(80, rect.h * scaleY);
      if (el) setMoodboardItemStyle(el, item);
    });
    touchMoodboardAfterInteraction(board, targets);
    updateMoodboardSpaceSize(board);
    syncMoodboardSelectionBox(board);
  };
  const onUp = () => {
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    markDirty();
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function startMoodboardInteraction(e, board, item, el, mode) {
  if (e.button !== 0) return;
  const selection = moodboardSelectionIds(board);
  if (selection.includes(item.id) && selection.length > 1) {
    if (mode === 'resize') startMoodboardGroupResize(e, board, 'se');
    else startMoodboardGroupMove(e, board);
    return;
  }
  e.preventDefault();
  e.stopPropagation();
  pushMoodboardUndo();
  bringMoodboardItemForward(board, item);
  setMoodboardItemStyle(el, item);
  el.classList.add(mode === 'resize' ? 'resizing' : 'moving');
  const startX = e.clientX;
  const startY = e.clientY;
  const initial = { x: item.x, y: item.y, w: item.w, h: item.h };
  const zoom = board?.zoom || 1;
  const onMove = moveEvent => {
    const dx = (moveEvent.clientX - startX) / zoom;
    const dy = (moveEvent.clientY - startY) / zoom;
    if (mode === 'resize') {
      item.w = Math.max(80, initial.w + dx);
      item.h = Math.max(80, initial.h + dy);
    } else {
      item.x = initial.x + dx;
      item.y = initial.y + dy;
    }
    item.updatedAt = now();
    board.updatedAt = now();
    S.moodboard.updatedAt = now();
    setMoodboardItemStyle(el, item);
    updateMoodboardSpaceSize(board);
  };
  const onUp = () => {
    el.classList.remove('moving', 'resizing');
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    markDirty();
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function bringMoodboardItemForward(board, item) {
  const maxZ = Math.max(1, ...(board?.items || []).map(next => Number(next.z || 1)));
  item.z = maxZ + 1;
}

function bringMoodboardItemsForward(board, items) {
  const targets = [...items].sort((a, b) => Number(a.z || 1) - Number(b.z || 1));
  let maxZ = Math.max(1, ...(board?.items || []).map(next => Number(next.z || 1)));
  targets.forEach(item => {
    maxZ += 1;
    item.z = maxZ;
  });
}

function moodboardSnapshot() {
  const board = getActiveMoodboard();
  return JSON.stringify({
    boardId: board?.id || null,
    zoom: board?.zoom || 1,
    originX: board?.originX || MOODBOARD_WORLD_MARGIN,
    originY: board?.originY || MOODBOARD_WORLD_MARGIN,
    items: (board?.items || []).map(item => ({ ...item })),
  });
}

function pushMoodboardUndo() {
  V.moodboardHistory.push(moodboardSnapshot());
  if (V.moodboardHistory.length > 50) V.moodboardHistory.shift();
}

function undoMoodboard() {
  const snap = V.moodboardHistory.pop();
  if (!snap) {
    toast('Nothing to undo');
    return;
  }
  try {
    const data = JSON.parse(snap);
    const board = S.moodboard.boards.find(item => sameId(item.id, data.boardId)) || getActiveMoodboard();
    if (!board) return;
    board.items = Array.isArray(data.items) ? data.items.map(ensureMoodboardItemShape) : [];
    board.zoom = clampNumber(data.zoom, board.zoom || 1, .1, 8);
    board.originX = clampNumber(data.originX, board.originX || MOODBOARD_WORLD_MARGIN, 1000, 10000000);
    board.originY = clampNumber(data.originY, board.originY || MOODBOARD_WORLD_MARGIN, 1000, 10000000);
    board.updatedAt = now();
    S.moodboard.activeBoardId = board.id;
    S.activeMoodboardId = board.id;
    S.moodboard.updatedAt = now();
    clearMoodboardSelection();
    markDirty();
    renderMoodboard();
  } catch (e) {
    toast('Could not undo');
  }
}

function clearMoodboard() {
  const board = getActiveMoodboard();
  if (!board?.items.length) return;
  if (!confirm('Clear all moodboard images?')) return;
  pushMoodboardUndo();
  board.items = [];
  clearMoodboardSelection();
  board.updatedAt = now();
  S.moodboard.updatedAt = now();
  markDirty();
  renderMoodboard();
}

function removeMoodboardItem(board, itemId) {
  if (!board) return;
  pushMoodboardUndo();
  board.items = board.items.filter(item => item.id !== itemId);
  setMoodboardSelection(moodboardSelectionIds(board).filter(id => id !== itemId), board);
  board.updatedAt = now();
  S.moodboard.updatedAt = now();
  markDirty();
  renderMoodboard();
}

function bindMoodboardMarquee(viewport, canvas, board) {
  if (!viewport || !canvas || !board) return;

  let marqueeActive = false;

  viewport.addEventListener('pointerdown', e => {
    if (e.button !== 0) return;
    if (V._mbPanMode) return;
    // Only start marquee on empty viewport/canvas (not on items or selection box)
    const onItem = e.target.closest('.moodboard-item, .moodboard-selection-box, .moodboard-group-delete, button');
    if (onItem) return;

    e.preventDefault();
    e.stopPropagation();
    marqueeActive = true;

    const additive = e.shiftKey || e.ctrlKey || e.metaKey;
    const baseIds = additive ? [...moodboardSelectionIds(board)] : [];
    const startW = moodboardClientPoint(e);
    let cur = { ...startW };
    let moved = false;

    // Create marquee element on the canvas (so it transforms with zoom/pan)
    const marqueeEl = document.createElement('div');
    marqueeEl.className = 'moodboard-marquee';
    setMoodboardRectStyle(marqueeEl, { x: startW.x, y: startW.y, w: 0, h: 0 });
    canvas.appendChild(marqueeEl);

    const onMove = mv => {
      cur = moodboardClientPoint(mv);
      const rect = normalizeMoodboardRect(startW, cur);
      moved = moved || rect.w > 3 || rect.h > 3;
      setMoodboardRectStyle(marqueeEl, rect);
    };
    const onUp = uv => {
      cur = moodboardClientPoint(uv);
      marqueeEl.remove();
      marqueeActive = false;
      document.removeEventListener('pointermove', onMove, true);
      document.removeEventListener('pointerup', onUp, true);

      if (moved) {
        const rect = normalizeMoodboardRect(startW, cur);
        const hits = (board.items || [])
          .filter(item => rectsIntersect(rect, moodboardItemRect(item)))
          .map(item => item.id);
        const next = new Set(baseIds);
        hits.forEach(id => next.add(id));
        setMoodboardSelection([...next], board);
      } else if (!additive) {
        clearMoodboardSelection();
      }
      renderMoodboard();
    };
    document.addEventListener('pointermove', onMove, true);
    document.addEventListener('pointerup', onUp, true);
  });
}

function bindMoodboardViewport(viewport, canvas, board) {
  if (!viewport || !canvas || !board) return;

  viewport.addEventListener('contextmenu', e => e.preventDefault());

  // Zoom: scroll wheel toward cursor
  viewport.addEventListener('wheel', e => {
    e.preventDefault();
    const zoom = board.zoom || 1;
    if (e.shiftKey && !e.ctrlKey) {
      V.mbPanX = (V.mbPanX || 0) - e.deltaY * 0.8;
    } else {
      const factor = Math.pow(1.0015, -e.deltaY);
      const nextZoom = clampNumber(zoom * factor, zoom, 0.05, 20);
      if (Math.abs(nextZoom - zoom) < 0.0001) return;
      const rect = viewport.getBoundingClientRect();
      const mx = e.clientX - rect.left;
      const my = e.clientY - rect.top;
      const px = V.mbPanX || 0;
      const py = V.mbPanY || 0;
      V.mbPanX = mx - (mx - px) * (nextZoom / zoom);
      V.mbPanY = my - (my - py) * (nextZoom / zoom);
      board.zoom = nextZoom;
    }
    board.panX = V.mbPanX;
    board.panY = V.mbPanY;
    board.updatedAt = now();
    S.moodboard.updatedAt = now();
    applyMoodboardTransform(canvas, board);
    markDirty();
  }, { passive: false });

  V._mbPanMode = false;
  let panning = false;
  let panStartX = 0, panStartY = 0, panStartPX = 0, panStartPY = 0;

  const onKeyDown = e => {
    if (e.code === 'Space' && !['INPUT','TEXTAREA'].includes(document.activeElement?.tagName)) {
      e.preventDefault();
      V._mbPanMode = true;
      viewport.classList.add('pan-mode');
    }
  };
  const onKeyUp = e => {
    if (e.code === 'Space') {
      V._mbPanMode = false;
      if (!panning) viewport.classList.remove('pan-mode');
    }
  };
  document.addEventListener('keydown', onKeyDown);
  document.addEventListener('keyup', onKeyUp);
  viewport._mbCleanup = () => {
    document.removeEventListener('keydown', onKeyDown);
    document.removeEventListener('keyup', onKeyUp);
  };

  const startPan = e => {
    panning = true;
    panStartX = e.clientX; panStartY = e.clientY;
    panStartPX = V.mbPanX || 0; panStartPY = V.mbPanY || 0;
    viewport.classList.add('panning');
    try { viewport.setPointerCapture(e.pointerId); } catch(_) {}
    e.preventDefault();
    e.stopPropagation();
  };

  viewport.addEventListener('pointerdown', e => {
    // Right mouse = pan (Miro style)
    if (e.button === 2) { startPan(e); return; }
    // Middle mouse = pan
    if (e.button === 1) { startPan(e); return; }
    // Space + left = pan
    if (e.button === 0 && V._mbPanMode) { startPan(e); return; }
    // Left without space: marquee handled by bindMoodboardMarquee
  });

  viewport.addEventListener('pointermove', e => {
    if (!panning) return;
    V.mbPanX = panStartPX + (e.clientX - panStartX);
    V.mbPanY = panStartPY + (e.clientY - panStartY);
    board.panX = V.mbPanX;
    board.panY = V.mbPanY;
    applyMoodboardTransform(canvas, board);
  });

  const stopPan = e => {
    if (!panning) return;
    panning = false;
    viewport.classList.remove('panning');
    if (!V._mbPanMode) viewport.classList.remove('pan-mode');
    try { viewport.releasePointerCapture(e.pointerId); } catch(_) {}
    markDirty();
  };
  viewport.addEventListener('pointerup', stopPan);
  viewport.addEventListener('pointercancel', stopPan);
}

function bindMoodboardDrop(viewport, canvas, board) {
  viewport.addEventListener('dragover', e => {
    if (dropHasFiles(e.dataTransfer)) {
      e.preventDefault();
      e.dataTransfer.dropEffect = 'copy';
      viewport.classList.add('drag-over');
    }
  });
  viewport.addEventListener('dragleave', e => {
    if (!viewport.contains(e.relatedTarget)) viewport.classList.remove('drag-over');
  });
  viewport.addEventListener('drop', e => {
    if (!dropHasFiles(e.dataTransfer)) return;
    e.preventDefault();
    const files = filePathsFromDrop(e.dataTransfer);
    if (!files.length) {
      viewport.classList.remove('drag-over');
      toast('Could not read dropped files');
      return;
    }
    viewport.classList.remove('drag-over');
    addMoodboardFiles(files, moodboardClientPoint(e, canvas, board));
  });
}

async function addMoodboardMedia() {
  const files = await pickMediaFiles('photo');
  const viewport = $('moodboard-viewport');
  const board = getActiveMoodboard();
  const zoom = board?.zoom || 1;
  const vw = viewport?.clientWidth || 800;
  const vh = viewport?.clientHeight || 600;
  const px = V.mbPanX || 0;
  const py = V.mbPanY || 0;
  addMoodboardFiles(files, {
    x: (vw / 2 - px) / zoom - 140,
    y: (vh / 2 - py) / zoom - 100,
  });
}

function addMoodboardFiles(files, point = { x: 120, y: 120 }) {
  const board = getActiveMoodboard();
  if (!board) return;
  const valid = (files || []).filter(fp => kindAllowsFile('photo', fp));
  if (!valid.length) {
    toast('Use image files');
    return;
  }
  pushMoodboardUndo();
  const addedIds = [];
  valid.forEach((fp, index) => {
    const media = registerMediaFile(fp, board.id, 'photo', 'moodboard');
    if (!media) return;
    const item = ensureMoodboardItemShape({
      id: 'mbi_' + uid(),
      mediaId: media.id,
      x: Math.round(point.x + index * 28),
      y: Math.round(point.y + index * 28),
      w: 280,
      h: 210,
      z: board.items.length + index + 1,
      createdAt: now(),
      updatedAt: now(),
    });
    board.items.push(item);
    addedIds.push(item.id);
  });
  setMoodboardSelection(addedIds, board);
  board.updatedAt = now();
  S.moodboard.updatedAt = now();
  markDirty();
  renderMoodboard();
  toast(`Added: ${valid.length}`);
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
    ['board', 'Board'],
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
  else if (S.activeProjectTab === 'board') renderProjectPaintBoard(project);
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

function renderProjectPaintBoard(project) {
  renderPaintWorkspace(project, 'project', 'project-tab-content');
}

function renderGamePaintBoard(game) {
  renderPaintWorkspace(game, 'game', 'tab-content');
}

function renderPaintWorkspace(owner, ownerKind, mountId) {
  ensurePaintOwner(owner, ownerKind);
  const workspace = getPaintWorkspaceForOwner(owner);
  const content = $(mountId);
  if (!content) return;
  if (!workspace.boardOpen) {
    renderPaintBoardLibrary(owner, ownerKind, workspace, content);
    return;
  }
  const board = getActivePaintBoard(workspace);
  if (!board) {
    workspace.boardOpen = false;
    renderPaintBoardLibrary(owner, ownerKind, workspace, content);
    return;
  }
  renderPaintBoardCanvas(owner, ownerKind, workspace, board, content);
}

function ensurePaintOwner(owner, ownerKind) {
  if (ownerKind === 'project') ensureProjectShape(owner);
  else ensureGameShape(owner);
}

function rerenderPaintWorkspace(owner, ownerKind) {
  if (ownerKind === 'project') renderProjectPaintBoard(owner);
  else renderGamePaintBoard(owner);
}

function touchPaintOwner(owner, ownerKind) {
  if (ownerKind === 'project') touchProject(owner);
  else touchGame(owner.id);
}

function touchPaintWorkspace(owner, ownerKind, workspace, board) {
  const stamp = now();
  if (board) board.updatedAt = stamp;
  if (workspace) workspace.updatedAt = stamp;
  touchPaintOwner(owner, ownerKind);
  markDirty();
}

function paintCategoryCount(workspace, categoryId) {
  return (workspace.boards || []).filter(board => sameId(board.categoryId, categoryId)).length;
}

function paintCategoryControlsHTML(workspace) {
  const active = getActivePaintCategory(workspace);
  return `
    <div class="category-controls media-category-controls paint-category-controls">
      <button type="button" class="category-menu-btn" id="paint-category">
        <span>${esc(active?.title || 'Main')}</span>
        <small>${paintCategoryCount(workspace, active?.id)}</small>
        <span class="select-caret">v</span>
      </button>
      <button class="mini-btn" id="paint-category-add">+ Category</button>
      <button class="mini-btn" id="paint-category-rename">Rename</button>
      <button class="mini-btn danger-lite" id="paint-category-delete">Delete</button>
    </div>`;
}

function bindPaintCategoryControls(owner, ownerKind, workspace) {
  const categoryBtn = $('paint-category');
  if (categoryBtn) {
    categoryBtn.onclick = e => {
      openCategoryMenu(e.currentTarget, getPaintCategories(workspace), workspace.activeCategoryId, category => {
        setActivePaintCategory(workspace, category.id);
        const firstBoard = workspace.boards.find(board => sameId(board.categoryId, category.id));
        if (firstBoard) workspace.activeBoardId = firstBoard.id;
        touchPaintWorkspace(owner, ownerKind, workspace);
        rerenderPaintWorkspace(owner, ownerKind);
      }, {
        title: 'Board categories',
        countFor: category => paintCategoryCount(workspace, category.id),
      });
    };
  }
  const add = $('paint-category-add');
  if (add) add.onclick = () => createPaintCategoryFlow(owner, ownerKind, workspace);
  const rename = $('paint-category-rename');
  if (rename) rename.onclick = () => renamePaintCategory(owner, ownerKind, workspace);
  const del = $('paint-category-delete');
  if (del) del.onclick = () => deletePaintCategory(owner, ownerKind, workspace);
}

function renderPaintBoardLibrary(owner, ownerKind, workspace, content) {
  const activeCategory = getActivePaintCategory(workspace);
  const boards = workspace.boards.filter(board => sameId(board.categoryId, activeCategory?.id));
  content.innerHTML = `
    <div class="tab-scroll paint-board-library">
      <div class="toolbar">
        <div class="toolbar-left">
          <div class="eyebrow">Board</div>
        </div>
        <div class="toolbar-right">
          <button class="ghost-btn" id="paint-new-sheet">+ Sheet</button>
        </div>
      </div>
      ${paintCategoryControlsHTML(workspace)}
      <div class="category-card-grid" id="paint-board-grid"></div>
    </div>`;

  $('paint-new-sheet').onclick = () => createPaintBoardFlow(owner, ownerKind, workspace);
  bindPaintCategoryControls(owner, ownerKind, workspace);

  const grid = $('paint-board-grid');
  if (!boards.length) {
    const empty = document.createElement('button');
    empty.className = 'album-drop-card fixed-drop';
    empty.textContent = '+ Sheet';
    empty.onclick = () => createPaintBoardFlow(owner, ownerKind, workspace);
    grid.appendChild(empty);
    return;
  }

  boards.forEach(board => {
    const card = document.createElement('button');
    card.className = 'category-card media-category-card paint-sheet-card';
    const cover = getPaintBoardCover(board);
    card.innerHTML = `
      <div class="category-card-cover paint-sheet-cover">${cover ? mediaPreviewHTML(cover, true) : '<span class="paint-sheet-mark">B</span>'}</div>
      <div class="category-card-main">
        <div class="category-card-title">${esc(board.title)}</div>
        <div class="card-sub">${(board.elements || []).length} items</div>
      </div>`;
    card.onclick = () => {
      workspace.activeBoardId = board.id;
      workspace.activeCategoryId = board.categoryId;
      workspace.boardOpen = true;
      V.paintSelection = null;
      touchPaintWorkspace(owner, ownerKind, workspace, board);
      rerenderPaintWorkspace(owner, ownerKind);
    };
    grid.appendChild(card);
  });

  const add = document.createElement('button');
  add.className = 'album-drop-card fixed-drop';
  add.textContent = '+ Sheet';
  add.onclick = () => createPaintBoardFlow(owner, ownerKind, workspace);
  grid.appendChild(add);
}

function getPaintBoardCover(board) {
  const image = (board.elements || []).find(element => element.type === 'image' && getMediaById(element.mediaId));
  return image ? getMediaById(image.mediaId) : null;
}

function createPaintCategoryFlow(owner, ownerKind, workspace) {
  askText('New Board Category', '', 'Create', title => {
    const category = ensurePaintCategoryShape({ id: 'paintcat_' + uid(), title, createdAt: now(), updatedAt: now() });
    workspace.categories.push(category);
    workspace.activeCategoryId = category.id;
    touchPaintWorkspace(owner, ownerKind, workspace);
    rerenderPaintWorkspace(owner, ownerKind);
  });
}

function renamePaintCategory(owner, ownerKind, workspace) {
  const category = getActivePaintCategory(workspace);
  if (!category) return;
  askText('Rename Category', category.title || '', 'Save', title => {
    category.title = title;
    category.updatedAt = now();
    touchPaintWorkspace(owner, ownerKind, workspace);
    rerenderPaintWorkspace(owner, ownerKind);
  });
}

function deletePaintCategory(owner, ownerKind, workspace) {
  const category = getActivePaintCategory(workspace);
  if (!category) return;
  if (workspace.categories.length <= 1) {
    toast('Keep one category');
    return;
  }
  if (!confirm(`Delete category "${category.title}"? Sheets move to the first category.`)) return;
  const next = workspace.categories.find(item => !sameId(item.id, category.id));
  workspace.boards.forEach(board => {
    if (sameId(board.categoryId, category.id)) board.categoryId = next.id;
  });
  workspace.categories = workspace.categories.filter(item => !sameId(item.id, category.id));
  workspace.activeCategoryId = next.id;
  workspace.activeBoardId = workspace.boards.find(board => sameId(board.categoryId, next.id))?.id || workspace.boards[0]?.id || null;
  touchPaintWorkspace(owner, ownerKind, workspace);
  rerenderPaintWorkspace(owner, ownerKind);
}

function createPaintBoardFlow(owner, ownerKind, workspace) {
  const category = getActivePaintCategory(workspace);
  askText('New Board Sheet', '', 'Create', title => {
    const board = createPaintBoard(title, category?.id || 'paintcat_default');
    workspace.boards.push(board);
    workspace.activeBoardId = board.id;
    workspace.activeCategoryId = board.categoryId;
    workspace.boardOpen = true;
    V.paintSelection = null;
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    rerenderPaintWorkspace(owner, ownerKind);
  });
}

function renderPaintBoardCanvas(owner, ownerKind, workspace, board, content) {
  if (V.paintCleanup) {
    V.paintCleanup();
    V.paintCleanup = null;
  }
  board = ensurePaintBoardShape(board, workspace.activeCategoryId);
  workspace.activeBoardId = board.id;
  workspace.activeCategoryId = board.categoryId;
  const zoom = board.zoom || 1;
  content.innerHTML = `
    <div class="paint-board-shell">
      <div class="paint-toolbar">
        <div class="paint-toolbar-row">
          <div class="paint-title-wrap">
            <input id="paint-board-title" class="text-input paint-board-title" value="${esc(board.title)}">
            <span class="moodboard-zoom-label" id="paint-zoom-label">${Math.round(zoom * 100)}%</span>
          </div>
          <div class="paint-actions">
            <button class="ghost-btn" id="paint-back-sheets">Sheets</button>
            <button class="inline-btn" id="paint-add-block">+ Block</button>
            <button class="ghost-btn" id="paint-add-photo">+ Photo</button>
            <button class="ghost-btn" id="paint-undo">Undo</button>
            <button class="danger-btn" id="paint-delete-selected">Delete</button>
          </div>
        </div>
        <div class="paint-sheet-row">
          <div class="paint-sheet-tabs" id="paint-sheet-tabs"></div>
          <button class="ghost-btn paint-sheet-add-btn" id="paint-new-sheet">+ Sheet</button>
        </div>
      </div>
      <div class="paint-viewport" id="paint-viewport" style="background-color:${esc(board.background)}">
        <div class="paint-canvas" id="paint-canvas"></div>
        ${!(board.elements || []).length ? `
        <div class="paint-empty-overlay" id="paint-empty-overlay">
          <button class="paint-empty-box" id="paint-empty-block">
            <span class="paint-empty-icon">+</span>
            <span class="paint-empty-title">Add Block</span>
          </button>
        </div>` : ''}
      </div>
    </div>`;

  bindPaintToolbar(owner, ownerKind, workspace, board);
  renderPaintSheetTabs(owner, ownerKind, workspace, board);
  const viewport = $('paint-viewport');
  const canvas = $('paint-canvas');
  applyPaintTransform(canvas, board);
  renderPaintElements(owner, ownerKind, workspace, board);
  bindPaintViewport(owner, ownerKind, workspace, board, viewport, canvas);
  bindPaintDrop(owner, ownerKind, workspace, board, viewport);

  if (!V.paintViewportReady) V.paintViewportReady = {};
  const readyKey = `${owner.id}:${board.id}`;
  if (!V.paintViewportReady[readyKey]) {
    V.paintViewportReady[readyKey] = true;
    requestAnimationFrame(() => centerPaintView(board));
  }
}

function bindPaintToolbar(owner, ownerKind, workspace, board) {
  $('paint-back-sheets').onclick = () => {
    workspace.boardOpen = false;
    V.paintSelection = null;
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    rerenderPaintWorkspace(owner, ownerKind);
  };
  $('paint-new-sheet').onclick = () => createPaintBoardFlow(owner, ownerKind, workspace);
  $('paint-add-block').onclick = () => addPaintBlockAtCenter(owner, ownerKind, workspace, board);
  $('paint-add-photo').onclick = () => addPaintBoardMedia(owner, ownerKind, workspace, board);
  $('paint-undo').onclick = () => undoPaintBoard(owner, ownerKind, workspace, board);
  $('paint-delete-selected').onclick = () => deletePaintSelection(owner, ownerKind, workspace, board);
  $('paint-board-title').oninput = e => {
    board.title = e.target.value;
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    renderPaintSheetTabs(owner, ownerKind, workspace, board);
  };
  if ($('paint-empty-block')) $('paint-empty-block').onclick = () => addPaintBlockAtCenter(owner, ownerKind, workspace, board);
}

function renderPaintSheetTabs(owner, ownerKind, workspace, activeBoard) {
  const tabs = $('paint-sheet-tabs');
  if (!tabs) return;
  tabs.innerHTML = '';
  const boards = workspace.boards.filter(board => sameId(board.categoryId, activeBoard.categoryId));
  boards.forEach(board => {
    const btn = document.createElement('button');
    btn.className = 'chip-btn' + (sameId(board.id, activeBoard.id) ? ' active' : '');
    btn.textContent = board.title;
    btn.onclick = () => {
      workspace.activeBoardId = board.id;
      workspace.activeCategoryId = board.categoryId;
      V.paintSelection = null;
      touchPaintWorkspace(owner, ownerKind, workspace, board);
      rerenderPaintWorkspace(owner, ownerKind);
    };
    tabs.appendChild(btn);
  });
}

function applyPaintTransform(canvas, board) {
  if (!canvas || !board) return;
  canvas.style.transform = `translate(${board.panX || 0}px, ${board.panY || 0}px) scale(${board.zoom || 1})`;
  const label = $('paint-zoom-label');
  if (label) label.textContent = Math.round((board.zoom || 1) * 100) + '%';
}

function centerPaintView(board) {
  const viewport = $('paint-viewport');
  const canvas = $('paint-canvas');
  if (!viewport || !canvas || !board) return;
  const bounds = paintBoundsForElements(board.elements || [], board);
  const zoom = board.zoom || 1;
  if (!bounds) {
    board.panX = viewport.clientWidth / 2;
    board.panY = viewport.clientHeight / 2;
  } else {
    board.panX = viewport.clientWidth / 2 - (bounds.x + bounds.w / 2) * zoom;
    board.panY = viewport.clientHeight / 2 - (bounds.y + bounds.h / 2) * zoom;
  }
  applyPaintTransform(canvas, board);
}

function renderPaintElements(owner, ownerKind, workspace, board) {
  const canvas = $('paint-canvas');
  if (!canvas) return;
  canvas.innerHTML = '';
  (board.elements || [])
    .map(ensurePaintElementShape)
    .filter(Boolean)
    .sort((a, b) => paintVisualZ(a) - paintVisualZ(b))
    .forEach(element => {
      const node = createPaintElementNode(element, board, owner, ownerKind, workspace, false);
      if (node) canvas.appendChild(node);
    });
}

function createPaintElementNode(element, board, owner, ownerKind, workspace, preview = false) {
  const bounds = paintElementBounds(element, board);
  if (!bounds) return null;
  const el = document.createElement('div');
  el.className = 'paint-element'
    + (preview ? ' paint-preview' : '')
    + (V.paintSelection === element.id ? ' selected' : '')
    + (V.paintConnectorFrom === element.id ? ' connector-source' : '');
  el.dataset.paintElement = element.id;
  el.style.left = `${Math.round(bounds.x)}px`;
  el.style.top = `${Math.round(bounds.y)}px`;
  el.style.width = `${Math.max(1, Math.round(bounds.w))}px`;
  el.style.height = `${Math.max(1, Math.round(bounds.h))}px`;
  el.style.zIndex = String(paintVisualZ(element));

  if (element.type === 'path') {
    const d = paintPathD(element.points, bounds);
    el.classList.add('paint-path-element');
    el.innerHTML = `<svg viewBox="0 0 ${Math.max(1, bounds.w)} ${Math.max(1, bounds.h)}" preserveAspectRatio="none">
      <path d="${esc(d)}" fill="none" stroke="${esc(element.color)}" stroke-width="${esc(element.width)}" stroke-linecap="round" stroke-linejoin="round"></path>
    </svg>`;
  } else if (element.type === 'line' || element.type === 'arrow') {
    const line = paintLineSvg(element, bounds);
    el.classList.add('paint-line-element');
    el.innerHTML = line;
  } else if (element.type === 'connector') {
    el.classList.add('paint-connector-element');
    el.innerHTML = paintConnectorSvg(element, bounds, board);
  } else if (element.type === 'rect' || element.type === 'ellipse') {
    el.classList.add('paint-shape-element', element.type === 'ellipse' ? 'paint-ellipse-element' : 'paint-rect-element');
    el.style.borderColor = element.color;
    el.style.borderWidth = `${Math.round(element.width)}px`;
    el.style.background = element.fill === 'transparent' ? 'transparent' : element.fill;
    if (element.type === 'ellipse') el.style.borderRadius = '50%';
  } else if (element.type === 'text') {
    el.classList.add('paint-text-element');
    el.style.color = element.color;
    el.style.fontSize = `${Math.round(element.fontSize || 28)}px`;
    el.innerHTML = `<div class="paint-element-text">${esc(element.text || 'Text').replace(/\n/g, '<br>')}</div>`;
  } else if (element.type === 'note') {
    el.classList.add('paint-note-element');
    el.style.borderColor = element.color;
    el.style.background = element.fill === 'transparent' ? '#fff3a3' : element.fill;
    el.style.fontSize = `${Math.round(element.fontSize || 18)}px`;
    el.innerHTML = `<div class="paint-element-text">${esc(element.text || 'Note').replace(/\n/g, '<br>')}</div>`;
  } else if (element.type === 'block') {
    el.classList.add('paint-block-element');
    el.style.borderColor = element.color;
    el.style.background = element.fill === 'transparent' ? '#191d22' : element.fill;
    el.style.fontSize = `${Math.round(element.fontSize || 14)}px`;
    el.innerHTML = `<div class="paint-element-text">${esc(element.text || 'Block').replace(/\n/g, '<br>')}</div>`;
  } else if (element.type === 'image') {
    const media = getMediaById(element.mediaId);
    el.classList.add('paint-image-element');
    el.innerHTML = media ? mediaPreviewHTML(media, true) : '<span>Missing</span>';
  }

  if (!preview) {
    if (['rect', 'ellipse', 'text', 'note', 'block', 'image'].includes(element.type)) {
      const handle = document.createElement('span');
      handle.className = 'paint-resize-handle';
      handle.title = 'Resize';
      el.appendChild(handle);
    }
    if (paintIsTileElement(element)) {
      ['n', 'e', 's', 'w'].forEach(side => {
        const dot = document.createElement('span');
        dot.className = `paint-connect-dot ${side}`;
        dot.dataset.side = side;
        dot.title = 'Connect';
        el.appendChild(dot);
      });
    }
    if (V.paintSelection === element.id && paintIsTileElement(element)) {
      const toolbar = document.createElement('div');
      toolbar.className = 'paint-selection-toolbar';
      toolbar.innerHTML = `
        <button class="paint-selection-btn paint-delete-element" title="Delete">
          <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M6 7h12M10 7V5h4v2M9 10v8M15 10v8M8 7l1 13h6l1-13"/></svg>
        </button>`;
      toolbar.querySelector('.paint-delete-element').onclick = event => {
        event.stopPropagation();
        deletePaintElement(owner, ownerKind, workspace, board, element.id);
      };
      el.appendChild(toolbar);
    }
    el.addEventListener('pointerdown', e => handlePaintElementPointerDown(e, owner, ownerKind, workspace, board, element, el));
    if (paintElementHasInlineText(element)) {
      el.addEventListener('dblclick', e => {
        e.stopPropagation();
        editPaintText(owner, ownerKind, workspace, board, element);
      });
    }
    if (element.type === 'image') {
      el.ondblclick = e => {
        e.stopPropagation();
        if (element.mediaId) openAlbumPhoto(element.mediaId);
      };
    }
  }
  return el;
}

function paintLineSvg(element, bounds) {
  const x1 = element.x1 - bounds.x;
  const y1 = element.y1 - bounds.y;
  const x2 = element.x2 - bounds.x;
  const y2 = element.y2 - bounds.y;
  const markerId = `paint-arrow-${String(element.id).replace(/[^a-zA-Z0-9_-]/g, '')}`;
  const marker = element.type === 'arrow'
    ? `<defs><marker id="${esc(markerId)}" markerWidth="12" markerHeight="12" refX="10" refY="4" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,8 L10,4 z" fill="${esc(element.color)}"></path></marker></defs>`
    : '';
  return `<svg viewBox="0 0 ${Math.max(1, bounds.w)} ${Math.max(1, bounds.h)}" preserveAspectRatio="none">
    ${marker}
    <line x1="${esc(x1)}" y1="${esc(y1)}" x2="${esc(x2)}" y2="${esc(y2)}" stroke="${esc(element.color)}" stroke-width="${esc(element.width)}" stroke-linecap="round" marker-end="${element.type === 'arrow' ? `url(#${esc(markerId)})` : ''}"></line>
  </svg>`;
}

function paintConnectorSvg(element, bounds, board) {
  const points = paintConnectorPoints(element, board);
  const x1 = points.x1 - bounds.x;
  const y1 = points.y1 - bounds.y;
  const x2 = points.x2 - bounds.x;
  const y2 = points.y2 - bounds.y;
  const curve = Math.max(60, Math.min(240, Math.abs(x2 - x1) * .45));
  const markerId = `paint-connector-${String(element.id).replace(/[^a-zA-Z0-9_-]/g, '')}`;
  return `<svg viewBox="0 0 ${Math.max(1, bounds.w)} ${Math.max(1, bounds.h)}" preserveAspectRatio="none">
    <defs><marker id="${esc(markerId)}" markerWidth="12" markerHeight="12" refX="10" refY="4" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,8 L10,4 z" fill="${esc(element.color)}"></path></marker></defs>
    <path d="M ${esc(x1)} ${esc(y1)} C ${esc(x1 + curve)} ${esc(y1)}, ${esc(x2 - curve)} ${esc(y2)}, ${esc(x2)} ${esc(y2)}" fill="none" stroke="${esc(element.color)}" stroke-width="${esc(element.width)}" stroke-linecap="round" marker-end="url(#${esc(markerId)})"></path>
  </svg>`;
}

function paintPathD(points, bounds) {
  return points.map((point, index) => {
    const x = point.x - bounds.x;
    const y = point.y - bounds.y;
    return `${index ? 'L' : 'M'} ${roundPaintCoord(x)} ${roundPaintCoord(y)}`;
  }).join(' ');
}

function roundPaintCoord(value) {
  return Math.round(Number(value || 0) * 10) / 10;
}

function paintElementBounds(element, board = null) {
  if (!element) return null;
  if (element.type === 'path') return paintPointsBounds(element.points || [], element.width || 4);
  if (element.type === 'line' || element.type === 'arrow' || element.type === 'connector') {
    const points = element.type === 'connector' ? paintConnectorPoints(element, board) : element;
    const pad = Math.ceil((element.width || 4) + 16);
    const left = Math.min(points.x1, points.x2) - pad;
    const top = Math.min(points.y1, points.y2) - pad;
    const right = Math.max(points.x1, points.x2) + pad;
    const bottom = Math.max(points.y1, points.y2) + pad;
    return { x: left, y: top, w: Math.max(1, right - left), h: Math.max(1, bottom - top) };
  }
  if (['rect', 'ellipse', 'image', 'text', 'note', 'block'].includes(element.type)) {
    return {
      x: Number(element.x || 0),
      y: Number(element.y || 0),
      w: Math.max(1, Number(element.w || 1)),
      h: Math.max(1, Number(element.h || 1)),
    };
  }
  return null;
}

function paintConnectorPoints(element, board = null) {
  const from = board?.elements?.find(item => sameId(item.id, element.fromId));
  const to = board?.elements?.find(item => sameId(item.id, element.toId));
  const fromCenter = paintAnchorForElement(from, element.fromSide || 's');
  const toCenter = paintAnchorForElement(to, element.toSide || 'n');
  return {
    x1: from ? fromCenter.x : paintNumber(element.x1, 0),
    y1: from ? fromCenter.y : paintNumber(element.y1, 0),
    x2: to ? toCenter.x : paintNumber(element.x2, 0),
    y2: to ? toCenter.y : paintNumber(element.y2, 0),
  };
}

function paintPointsBounds(points, width = 4) {
  if (!points?.length) return null;
  const pad = Math.ceil(width + 8);
  const xs = points.map(point => point.x);
  const ys = points.map(point => point.y);
  const left = Math.min(...xs) - pad;
  const top = Math.min(...ys) - pad;
  const right = Math.max(...xs) + pad;
  const bottom = Math.max(...ys) + pad;
  return { x: left, y: top, w: Math.max(1, right - left), h: Math.max(1, bottom - top) };
}

function paintBoundsForElements(elements, board = null) {
  const bounds = (elements || []).map(element => paintElementBounds(element, board)).filter(Boolean);
  if (!bounds.length) return null;
  const left = Math.min(...bounds.map(rect => rect.x));
  const top = Math.min(...bounds.map(rect => rect.y));
  const right = Math.max(...bounds.map(rect => rect.x + rect.w));
  const bottom = Math.max(...bounds.map(rect => rect.y + rect.h));
  return { x: left, y: top, w: right - left, h: bottom - top };
}

function handlePaintElementPointerDown(e, owner, ownerKind, workspace, board, element, el) {
  if (e.button !== 0) return;
  if (e.target.closest('.paint-element-text.editing, .paint-element-text[contenteditable="true"]')) {
    e.stopPropagation();
    return;
  }
  if (e.detail > 1 && paintElementHasInlineText(element)) {
    e.preventDefault();
    e.stopPropagation();
    editPaintText(owner, ownerKind, workspace, board, element);
    return;
  }
  const dot = e.target.closest('.paint-connect-dot');
  if (dot) {
    startPaintConnectorDrag(e, owner, ownerKind, workspace, board, element, dot.dataset.side || 's');
    return;
  }
  e.preventDefault();
  e.stopPropagation();
  V.paintSelection = element.id;
  if (e.target.closest('.paint-resize-handle')) {
    startPaintElementResize(e, owner, ownerKind, workspace, board, element, el);
  } else {
    startPaintElementMove(e, owner, ownerKind, workspace, board, element, el);
  }
}

function startPaintElementMove(e, owner, ownerKind, workspace, board, element, el) {
  pushPaintUndo(board);
  bringPaintElementForward(board, element);
  el.classList.add('moving', 'selected');
  const startX = e.clientX;
  const startY = e.clientY;
  const zoom = board.zoom || 1;
  const snap = paintElementSnapshot(element);
  const onMove = mv => {
    const dx = (mv.clientX - startX) / zoom;
    const dy = (mv.clientY - startY) / zoom;
    applyPaintElementMove(element, snap, dx, dy);
    const bounds = paintElementBounds(element, board);
    if (bounds) {
      el.style.left = `${Math.round(bounds.x)}px`;
      el.style.top = `${Math.round(bounds.y)}px`;
      el.style.width = `${Math.max(1, Math.round(bounds.w))}px`;
      el.style.height = `${Math.max(1, Math.round(bounds.h))}px`;
    }
    element.updatedAt = now();
    syncPaintConnectorNodes(board);
  };
  const onUp = () => {
    el.classList.remove('moving');
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    renderPaintElements(owner, ownerKind, workspace, board);
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function startPaintElementResize(e, owner, ownerKind, workspace, board, element, el) {
  if (!['rect', 'ellipse', 'image', 'text', 'note', 'block'].includes(element.type)) return;
  pushPaintUndo(board);
  e.preventDefault();
  e.stopPropagation();
  el.classList.add('resizing', 'selected');
  const startX = e.clientX;
  const startY = e.clientY;
  const zoom = board.zoom || 1;
  const start = { w: element.w, h: element.h };
  const onMove = mv => {
    const dx = (mv.clientX - startX) / zoom;
    const dy = (mv.clientY - startY) / zoom;
    element.w = Math.max(PAINT_GRID_SIZE, paintSnap(start.w + dx));
    element.h = Math.max(PAINT_GRID_SIZE, paintSnap(start.h + dy));
    el.style.width = `${Math.round(element.w)}px`;
    el.style.height = `${Math.round(element.h)}px`;
    element.updatedAt = now();
    syncPaintConnectorNodes(board);
  };
  const onUp = () => {
    el.classList.remove('resizing');
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    touchPaintWorkspace(owner, ownerKind, workspace, board);
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function paintElementSnapshot(element) {
  return JSON.parse(JSON.stringify(element));
}

function syncPaintConnectorNodes(board) {
  (board?.elements || []).forEach(element => {
    if (element.type !== 'connector') return;
    const points = paintConnectorPoints(element, board);
    element.x1 = points.x1;
    element.y1 = points.y1;
    element.x2 = points.x2;
    element.y2 = points.y2;
  });
}

function startPaintConnectorDrag(e, owner, ownerKind, workspace, board, fromElement, fromSide = 's') {
  if (!paintIsTileElement(fromElement)) return;
  e.preventDefault();
  e.stopPropagation();
  const viewport = $('paint-viewport');
  const canvas = $('paint-canvas');
  if (!viewport || !canvas) return;
  const start = paintAnchorForElement(fromElement, fromSide);
  const preview = ensurePaintElementShape({
    id: 'preview_connector',
    type: 'connector',
    x1: start.x,
    y1: start.y,
    x2: start.x,
    y2: start.y,
    color: board.color,
    fill: 'transparent',
    width: Math.max(2, board.lineWidth),
    z: 1,
    createdAt: now(),
    updatedAt: now(),
  });
  V.paintConnectorFrom = fromElement.id;
  V.paintSelection = fromElement.id;
  updatePaintPreview(canvas, board, preview);

  const onMove = mv => {
    const point = paintWorldPoint(mv, viewport, board);
    preview.x2 = point.x;
    preview.y2 = point.y;
    updatePaintPreview(canvas, board, preview);
  };
  const onUp = up => {
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    clearPaintPreview(canvas);
    const dropTarget = document.elementFromPoint(up.clientX, up.clientY);
    const targetDot = dropTarget?.closest?.('.paint-connect-dot');
    const targetNode = targetDot?.closest?.('[data-paint-element]') || dropTarget?.closest?.('[data-paint-element]');
    const target = targetNode
      ? board.elements.find(item => sameId(item.id, targetNode.dataset.paintElement))
      : null;
    if (target && !sameId(target.id, fromElement.id) && paintIsTileElement(target)) {
      const point = paintWorldPoint(up, viewport, board);
      addPaintConnector(owner, ownerKind, workspace, board, fromElement, target, fromSide, targetDot?.dataset.side || paintNearestSide(target, point));
    } else {
      V.paintConnectorFrom = null;
      renderPaintElements(owner, ownerKind, workspace, board);
    }
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function paintNearestSide(element, point) {
  const x = Number(element.x || 0);
  const y = Number(element.y || 0);
  const w = Number(element.w || 0);
  const h = Number(element.h || 0);
  const distances = [
    ['n', Math.abs(point.y - y)],
    ['s', Math.abs(point.y - (y + h))],
    ['w', Math.abs(point.x - x)],
    ['e', Math.abs(point.x - (x + w))],
  ];
  distances.sort((a, b) => a[1] - b[1]);
  return distances[0]?.[0] || 'n';
}

function addPaintConnector(owner, ownerKind, workspace, board, fromElement, toElement, fromSide = 's', toSide = 'n') {
  pushPaintUndo(board);
  const start = paintAnchorForElement(fromElement, fromSide);
  const end = paintAnchorForElement(toElement, toSide);
  const connector = ensurePaintElementShape({
    id: 'pel_' + uid(),
    type: 'connector',
    fromId: fromElement.id,
    toId: toElement.id,
    fromSide,
    toSide,
    x1: start.x,
    y1: start.y,
    x2: end.x,
    y2: end.y,
    color: '#8d949e',
    fill: 'transparent',
    width: 2,
    z: 1,
    createdAt: now(),
    updatedAt: now(),
  });
  if (connector) board.elements.push(connector);
  V.paintConnectorFrom = null;
  V.paintSelection = toElement.id;
  touchPaintWorkspace(owner, ownerKind, workspace, board);
  rerenderPaintWorkspace(owner, ownerKind);
}

function applyPaintElementMove(element, snap, dx, dy) {
  if (snap.type === 'path') {
    element.points = snap.points.map(point => ({ x: point.x + dx, y: point.y + dy }));
  } else if (snap.type === 'line' || snap.type === 'arrow') {
    element.x1 = paintSnap(snap.x1 + dx);
    element.y1 = paintSnap(snap.y1 + dy);
    element.x2 = paintSnap(snap.x2 + dx);
    element.y2 = paintSnap(snap.y2 + dy);
  } else if (snap.type === 'connector') {
    element.x1 = paintSnap(snap.x1 + dx);
    element.y1 = paintSnap(snap.y1 + dy);
    element.x2 = paintSnap(snap.x2 + dx);
    element.y2 = paintSnap(snap.y2 + dy);
  } else {
    element.x = paintSnap(snap.x + dx);
    element.y = paintSnap(snap.y + dy);
  }
}

function editPaintText(owner, ownerKind, workspace, board, element, options = {}) {
  const node = getPaintElementNode(element.id);
  const host = node?.querySelector('.paint-element-text');
  if (!host) return;
  const placeCaret = () => {
    host.focus({ preventScroll: true });
    const range = document.createRange();
    range.selectNodeContents(host);
    if (!options.selectAll) range.collapse(false);
    const selection = window.getSelection();
    selection.removeAllRanges();
    selection.addRange(range);
  };
  if (host.classList.contains('editing')) {
    placeCaret();
    return;
  }
  const before = element.text || '';
  if (options.pushUndo !== false) pushPaintUndo(board);
  V.paintSelection = element.id;
  node.classList.add('editing', 'selected');
  host.setAttribute('contenteditable', 'true');
  host.spellcheck = false;
  host.classList.add('editing');
  requestAnimationFrame(placeCaret);
  let finished = false;
  const finish = save => {
    if (finished) return;
    finished = true;
    host.setAttribute('contenteditable', 'false');
    host.classList.remove('editing');
    node.classList.remove('editing');
    host.removeEventListener('blur', onBlur);
    host.removeEventListener('keydown', onKeyDown);
    host.removeEventListener('pointerdown', onPointerDown, true);
    element.text = save ? host.innerText.trim() || (element.type === 'block' ? 'Block' : element.type === 'note' ? 'Note' : 'Text') : before;
    element.updatedAt = now();
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    rerenderPaintWorkspace(owner, ownerKind);
  };
  const onBlur = () => finish(true);
  const onPointerDown = e => e.stopPropagation();
  const onKeyDown = e => {
    if (e.key === 'Escape') {
      e.preventDefault();
      finish(false);
    }
    if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
      e.preventDefault();
      finish(true);
    }
  };
  host.addEventListener('blur', onBlur);
  host.addEventListener('keydown', onKeyDown);
  host.addEventListener('pointerdown', onPointerDown, true);
}

function getPaintElementNode(elementId) {
  return Array.from(document.querySelectorAll('[data-paint-element]'))
    .find(node => sameId(node.dataset.paintElement, elementId)) || null;
}

function bindPaintViewport(owner, ownerKind, workspace, board, viewport, canvas) {
  if (!viewport || !canvas || !board) return;
  viewport.addEventListener('contextmenu', e => e.preventDefault());
  viewport.addEventListener('dblclick', e => {
    const node = e.target.closest?.('[data-paint-element]');
    if (!node) return;
    const element = (board.elements || []).find(item => sameId(item.id, node.dataset.paintElement));
    if (!paintElementHasInlineText(element)) return;
    e.preventDefault();
    e.stopPropagation();
    V.paintSelection = element.id;
    editPaintText(owner, ownerKind, workspace, board, element);
  }, true);

  viewport.addEventListener('wheel', e => {
    e.preventDefault();
    const zoom = board.zoom || 1;
    if (e.shiftKey && !e.ctrlKey) {
      board.panX = (board.panX || 0) - e.deltaY * 0.8;
    } else {
      const factor = Math.pow(1.0015, -e.deltaY);
      const nextZoom = clampNumber(zoom * factor, zoom, 0.05, 20);
      if (Math.abs(nextZoom - zoom) < 0.0001) return;
      const rect = viewport.getBoundingClientRect();
      const mx = e.clientX - rect.left;
      const my = e.clientY - rect.top;
      board.panX = mx - (mx - (board.panX || 0)) * (nextZoom / zoom);
      board.panY = my - (my - (board.panY || 0)) * (nextZoom / zoom);
      board.zoom = nextZoom;
    }
    board.updatedAt = now();
    workspace.updatedAt = now();
    applyPaintTransform(canvas, board);
    touchPaintOwner(owner, ownerKind);
    markDirty();
  }, { passive: false });

  V._paintPanMode = false;
  let panning = false;
  let panStartX = 0;
  let panStartY = 0;
  let panStartPX = 0;
  let panStartPY = 0;

  const onKeyDown = e => {
    if (e.code === 'Space' && !['INPUT', 'TEXTAREA'].includes(document.activeElement?.tagName)) {
      e.preventDefault();
      V._paintPanMode = true;
      viewport.classList.add('pan-mode');
    }
  };
  const onKeyUp = e => {
    if (e.code === 'Space') {
      V._paintPanMode = false;
      if (!panning) viewport.classList.remove('pan-mode');
    }
  };
  document.addEventListener('keydown', onKeyDown);
  document.addEventListener('keyup', onKeyUp);
  V.paintCleanup = () => {
    document.removeEventListener('keydown', onKeyDown);
    document.removeEventListener('keyup', onKeyUp);
  };

  const startPan = e => {
    panning = true;
    panStartX = e.clientX;
    panStartY = e.clientY;
    panStartPX = board.panX || 0;
    panStartPY = board.panY || 0;
    viewport.classList.add('panning');
    try { viewport.setPointerCapture(e.pointerId); } catch (_) {}
    e.preventDefault();
    e.stopPropagation();
  };

  viewport.addEventListener('pointerdown', e => {
    if (e.target.closest('.paint-element, .paint-empty-box')) return;
    if (e.button === 2 || e.button === 1 || (e.button === 0 && V._paintPanMode)) {
      startPan(e);
      return;
    }
    if (e.button !== 0) return;
    V.paintSelection = null;
    V.paintConnectorFrom = null;
    renderPaintElements(owner, ownerKind, workspace, board);
  });

  viewport.addEventListener('pointermove', e => {
    if (!panning) return;
    board.panX = panStartPX + (e.clientX - panStartX);
    board.panY = panStartPY + (e.clientY - panStartY);
    applyPaintTransform(canvas, board);
  });
  const stopPan = e => {
    if (!panning) return;
    panning = false;
    viewport.classList.remove('panning');
    if (!V._paintPanMode) viewport.classList.remove('pan-mode');
    try { viewport.releasePointerCapture(e.pointerId); } catch (_) {}
    touchPaintWorkspace(owner, ownerKind, workspace, board);
  };
  viewport.addEventListener('pointerup', stopPan);
  viewport.addEventListener('pointercancel', stopPan);
}

function paintWorldPoint(e, viewport = $('paint-viewport'), board = getActivePaintContext()?.board) {
  if (!viewport || !board) return { x: 0, y: 0 };
  const rect = viewport.getBoundingClientRect();
  return {
    x: (e.clientX - rect.left - (board.panX || 0)) / (board.zoom || 1),
    y: (e.clientY - rect.top - (board.panY || 0)) / (board.zoom || 1),
  };
}

function startPaintDraw(e, owner, ownerKind, workspace, board, viewport, canvas) {
  e.preventDefault();
  e.stopPropagation();
  pushPaintUndo(board);
  const start = paintWorldPoint(e, viewport, board);
  const tool = board.tool;
  let points = [start];
  let preview = createPaintDraftElement(board, tool, start, start, points);
  updatePaintPreview(canvas, board, preview);

  const onMove = mv => {
    const point = paintWorldPoint(mv, viewport, board);
    if (['pencil', 'brush', 'eraser'].includes(tool)) {
      const last = points[points.length - 1];
      if (Math.hypot(point.x - last.x, point.y - last.y) > 1) points.push(point);
      preview = createPaintDraftElement(board, tool, start, point, points);
    } else {
      preview = createPaintDraftElement(board, tool, start, point, points);
    }
    updatePaintPreview(canvas, board, preview);
  };
  const onUp = up => {
    document.removeEventListener('pointermove', onMove, true);
    document.removeEventListener('pointerup', onUp, true);
    clearPaintPreview(canvas);
    const end = paintWorldPoint(up, viewport, board);
    const element = ensurePaintElementShape(createPaintDraftElement(board, tool, start, end, points));
    if (element && paintElementHasSize(element)) {
      element.z = paintNextZ(board);
      board.elements.push(element);
      V.paintSelection = element.id;
      touchPaintWorkspace(owner, ownerKind, workspace, board);
      rerenderPaintWorkspace(owner, ownerKind);
    }
  };
  document.addEventListener('pointermove', onMove, true);
  document.addEventListener('pointerup', onUp, true);
}

function createPaintDraftElement(board, tool, start, end, points) {
  const base = {
    id: 'pel_' + uid(),
    color: tool === 'eraser' ? board.background || PAINT_BACKGROUND : board.color,
    fill: board.fillShapes ? board.fillColor : 'transparent',
    width: tool === 'brush' ? Math.max(6, board.lineWidth * 2) : tool === 'eraser' ? Math.max(14, board.lineWidth * 3) : board.lineWidth,
    createdAt: now(),
    updatedAt: now(),
  };
  if (['pencil', 'brush', 'eraser'].includes(tool)) {
    return { ...base, type: 'path', tool, points: [...points] };
  }
  if (tool === 'line' || tool === 'arrow') {
    return { ...base, type: tool, x1: start.x, y1: start.y, x2: end.x, y2: end.y };
  }
  const rect = normalizePaintDrawRect(start, end);
  return { ...base, type: tool, x: rect.x, y: rect.y, w: rect.w, h: rect.h };
}

function normalizePaintDrawRect(a, b) {
  const start = paintSnapPoint(a);
  const end = paintSnapPoint(b);
  return {
    x: Math.min(start.x, end.x),
    y: Math.min(start.y, end.y),
    w: Math.abs(start.x - end.x),
    h: Math.abs(start.y - end.y),
  };
}

function paintElementHasSize(element) {
  if (element.type === 'path') return (element.points || []).length > 1;
  if (element.type === 'line' || element.type === 'arrow' || element.type === 'connector') return Math.hypot(element.x2 - element.x1, element.y2 - element.y1) > 3;
  return Number(element.w || 0) > 4 && Number(element.h || 0) > 4;
}

function updatePaintPreview(canvas, board, element) {
  clearPaintPreview(canvas);
  const node = createPaintElementNode(element, board, null, null, null, true);
  if (node) canvas.appendChild(node);
}

function clearPaintPreview(canvas = $('paint-canvas')) {
  if (!canvas) return;
  canvas.querySelectorAll('.paint-preview').forEach(node => node.remove());
}

function addPaintBlockAtCenter(owner, ownerKind, workspace, board) {
  const center = paintViewportCenter(board);
  const w = 280;
  const h = 160;
  const point = { x: center.x - w / 2, y: center.y - h / 2 };
  addPaintTextElement(owner, ownerKind, workspace, board, point, 'block', { autoEdit: true });
}

function addPaintTextElement(owner, ownerKind, workspace, board, point, type, options = {}) {
  const snapped = paintSnapPoint(point);
  pushPaintUndo(board);
  const element = ensurePaintElementShape({
    id: 'pel_' + uid(),
    type,
    x: snapped.x,
    y: snapped.y,
    w: type === 'block' ? 280 : type === 'note' ? 280 : 320,
    h: type === 'block' ? 160 : type === 'note' ? 170 : Math.max(PAINT_GRID_SIZE, board.fontSize * 2.1),
    text: type === 'block' ? 'Block' : type === 'note' ? 'Note' : 'Text',
    color: type === 'block' ? '#5d6674' : board.color,
    fill: type === 'block' ? '#181b20' : type === 'text' ? 'transparent' : type === 'note' ? '#272421' : board.fillColor,
    width: Math.max(1, board.lineWidth),
    fontSize: type === 'block' ? 14 : type === 'note' ? 18 : board.fontSize,
    z: paintNextZ(board),
    createdAt: now(),
    updatedAt: now(),
  });
  if (element) {
    board.elements.push(element);
    V.paintSelection = element.id;
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    rerenderPaintWorkspace(owner, ownerKind);
    if (options.autoEdit) {
      requestAnimationFrame(() => editPaintText(owner, ownerKind, workspace, board, element, { pushUndo: false, selectAll: true }));
    }
  }
}

function deletePaintSelection(owner, ownerKind, workspace, board) {
  if (!V.paintSelection) {
    toast('Select a block or photo first');
    return;
  }
  deletePaintElement(owner, ownerKind, workspace, board, V.paintSelection);
}

function deletePaintElement(owner, ownerKind, workspace, board, elementId) {
  const target = (board.elements || []).find(element => sameId(element.id, elementId));
  if (!target) return;
  pushPaintUndo(board);
  const mediaId = target.type === 'image' ? target.mediaId : null;
  board.elements = (board.elements || []).filter(element =>
    !sameId(element.id, elementId) &&
    !sameId(element.fromId, elementId) &&
    !sameId(element.toId, elementId)
  );
  if (mediaId) S.media = S.media.filter(media => !sameId(media.id, mediaId));
  V.paintSelection = null;
  V.paintConnectorFrom = null;
  touchPaintWorkspace(owner, ownerKind, workspace, board);
  rerenderPaintWorkspace(owner, ownerKind);
}

function paintNextZ(board) {
  return Math.max(1, ...(board.elements || []).map(element => Number(element.z || 1))) + 1;
}

function bringPaintElementForward(board, element) {
  element.z = paintNextZ(board);
}

function pushPaintUndo(board) {
  if (!board) return;
  if (!V.paintHistory) V.paintHistory = {};
  const key = board.id;
  V.paintHistory[key] ??= [];
  V.paintHistory[key].push(JSON.stringify({
    background: board.background || PAINT_BACKGROUND,
    elements: (board.elements || []).map(element => ({ ...element })),
  }));
  if (V.paintHistory[key].length > 80) V.paintHistory[key].shift();
}

function undoPaintBoard(owner, ownerKind, workspace, board) {
  const history = V.paintHistory?.[board.id] || [];
  const snap = history.pop();
  if (!snap) {
    toast('Nothing to undo');
    return;
  }
  try {
    const data = JSON.parse(snap);
    board.background = paintColor(data.background, board.background || PAINT_BACKGROUND);
    board.elements = Array.isArray(data.elements) ? data.elements.map(ensurePaintElementShape).filter(Boolean) : [];
    V.paintSelection = null;
    touchPaintWorkspace(owner, ownerKind, workspace, board);
    rerenderPaintWorkspace(owner, ownerKind);
  } catch (e) {
    toast('Could not undo');
  }
}

function clearPaintBoard(owner, ownerKind, workspace, board) {
  if (!board?.elements?.length) return;
  if (!confirm(`Clear sheet "${board.title}"?`)) return;
  pushPaintUndo(board);
  const mediaIds = new Set(board.elements.filter(element => element.type === 'image').map(element => element.mediaId).filter(Boolean));
  board.elements = [];
  S.media = S.media.filter(media => !mediaIds.has(media.id));
  V.paintSelection = null;
  touchPaintWorkspace(owner, ownerKind, workspace, board);
  rerenderPaintWorkspace(owner, ownerKind);
}

function deletePaintBoard(owner, ownerKind, workspace, board) {
  if (workspace.boards.length <= 1) {
    toast('Keep one sheet');
    return;
  }
  if (!confirm(`Delete sheet "${board.title}"?`)) return;
  const mediaIds = new Set((board.elements || []).filter(element => element.type === 'image').map(element => element.mediaId).filter(Boolean));
  S.media = S.media.filter(media => !mediaIds.has(media.id));
  workspace.boards = workspace.boards.filter(item => !sameId(item.id, board.id));
  workspace.activeBoardId = workspace.boards.find(item => sameId(item.categoryId, workspace.activeCategoryId))?.id || workspace.boards[0]?.id || null;
  workspace.boardOpen = false;
  V.paintSelection = null;
  touchPaintWorkspace(owner, ownerKind, workspace);
  rerenderPaintWorkspace(owner, ownerKind);
}

async function addPaintBoardMedia(owner, ownerKind, workspace, board, point = null) {
  const files = await pickMediaFiles('photo');
  addPaintBoardFiles(files, owner, ownerKind, workspace, board, point);
}

function addPaintBoardFiles(files, owner, ownerKind, workspace, board, point = null) {
  const valid = (files || []).filter(fp => kindAllowsFile('photo', fp));
  if (!valid.length) return;
  const center = point || paintViewportCenter(board);
  pushPaintUndo(board);
  let lastId = null;
  valid.forEach((fp, index) => {
    const media = registerMediaFile(fp, owner.id, 'photo', 'paint');
    if (!media) return;
    const element = ensurePaintElementShape({
      id: 'pel_' + uid(),
      type: 'image',
      mediaId: media.id,
      x: paintSnap(center.x - 180 + index * 40),
      y: paintSnap(center.y - 120 + index * 40),
      w: 360,
      h: 240,
      color: '#5d6674',
      fill: 'transparent',
      width: 1,
      z: paintNextZ(board),
      createdAt: now(),
      updatedAt: now(),
    });
    if (element) {
      board.elements.push(element);
      lastId = element.id;
    }
  });
  if (lastId) V.paintSelection = lastId;
  touchPaintWorkspace(owner, ownerKind, workspace, board);
  rerenderPaintWorkspace(owner, ownerKind);
  toast(`Added: ${valid.length}`);
}

function paintViewportCenter(board) {
  const viewport = $('paint-viewport');
  if (!viewport || !board) return { x: 0, y: 0 };
  return {
    x: (viewport.clientWidth / 2 - (board.panX || 0)) / (board.zoom || 1),
    y: (viewport.clientHeight / 2 - (board.panY || 0)) / (board.zoom || 1),
  };
}

function bindPaintDrop(owner, ownerKind, workspace, board, viewport) {
  if (!viewport) return;
  viewport.addEventListener('dragover', e => {
    if (dropHasFiles(e.dataTransfer)) {
      e.preventDefault();
      e.dataTransfer.dropEffect = 'copy';
      viewport.classList.add('drag-over');
    }
  });
  viewport.addEventListener('dragleave', e => {
    if (!viewport.contains(e.relatedTarget)) viewport.classList.remove('drag-over');
  });
  viewport.addEventListener('drop', e => {
    if (!dropHasFiles(e.dataTransfer)) return;
    e.preventDefault();
    viewport.classList.remove('drag-over');
    const files = filePathsFromDrop(e.dataTransfer);
    if (!files.length) {
      toast('Could not read dropped files');
      return;
    }
    addPaintBoardFiles(files, owner, ownerKind, workspace, board, paintWorldPoint(e, viewport, board));
  });
}

function removePaintMediaRefs(workspace, mediaId) {
  if (!workspace?.boards) return;
  workspace.boards.forEach(board => {
    board.elements = (board.elements || []).filter(element => !(element.type === 'image' && sameId(element.mediaId, mediaId)));
    board.updatedAt = now();
  });
  workspace.updatedAt = now();
}

function getActivePaintContext() {
  if (S.view === 'projects' && S.activeProjectTab === 'board') {
    const owner = getActiveProject();
    if (!owner) return null;
    const workspace = getPaintWorkspaceForOwner(owner);
    if (!workspace.boardOpen) return null;
    return { owner, ownerKind: 'project', workspace, board: getActivePaintBoard(workspace) };
  }
  if (S.view === 'game' && S.activeTab === 'board') {
    const owner = getActiveGame();
    if (!owner) return null;
    const workspace = getPaintWorkspaceForOwner(owner);
    if (!workspace.boardOpen) return null;
    return { owner, ownerKind: 'game', workspace, board: getActivePaintBoard(workspace) };
  }
  return null;
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
    col.className = 'kanban-column' + (key === 'done' ? ' kanban-column-done' : '');
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
      if (key === 'done') syncExtraQuestDone(payload.taskId);
    });
    tasks.forEach(task => taskList.appendChild(buildTaskCard(project, milestone, board, key, task)));
    columns.appendChild(col);
  });
}

function buildTaskCard(project, milestone, board, columnKey, task) {
  ensureTaskShape(task);
  const card = document.createElement('div');
  const isDone = columnKey === 'done';
  card.className = `task-card task-importance-${esc(importanceLevel(task.importance).id)}${isDone ? ' task-done' : ''}`;
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
    isDone ? `Done${task.completedAt ? ` ${formatShortDate(task.completedAt)}` : ''}` : '',
    (task.notes || '').trim().slice(0, 96),
    (task.mediaIds || []).length ? `${(task.mediaIds || []).length} media` : '',
  ].filter(Boolean).join(' - ');
  const alreadyInDaily = isKanbanTaskLinkedToExtras(task.id);
  card.innerHTML = `
    <div class="task-card-top">
      ${importanceBadgeHTML(task.importance)}
      <span class="task-title-btn">${esc(task.title || 'Untitled')}</span>
      ${isDone ? '<span class="task-done-mark">Done</span>' : ''}
      <button class="task-to-today-btn${alreadyInDaily ? ' added' : ''}" data-task-id="${esc(task.id)}" title="Add to Today's extras" ${alreadyInDaily ? 'disabled' : ''}>${alreadyInDaily ? '✓' : '+Today'}</button>
    </div>
    ${meta ? `<div class="task-card-meta">${esc(meta)}</div>` : ''}`;
  card.querySelector('.task-to-today-btn').addEventListener('click', e => {
    e.stopPropagation();
    addKanbanTaskToTodayExtras(task);
  });
  card.addEventListener('click', e => {
    if (dragging || e.target.closest('.rarity-badge, .task-to-today-btn')) return;
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
      completedAt: columnKey === 'done' ? now() : null,
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
  if (fromColumn === toColumn) return;
  const list = board.columns[fromColumn] || [];
  const task = list.find(item => item.id === taskId);
  if (!task || !board.columns[toColumn]) return;
  const previousCompletedDate = taskCompletedISO(task);
  let dailyDay = null;
  let beforeDailyStats = null;
  if (toColumn === 'done' && S.dailies?.enabled !== false) {
    ensureDailiesReady({ dirty: false });
    dailyDay = getOrCreateDailyDay(todayISO());
    beforeDailyStats = dailyStats(dailyDay);
  }
  board.columns[fromColumn] = list.filter(item => item.id !== taskId);
  board.columns[toColumn].push(task);
  if (toColumn === 'done') task.completedAt = now();
  else if (fromColumn === 'done') task.completedAt = null;
  task.updatedAt = now();
  board.updatedAt = now();
  milestone.updatedAt = now();
  touchProject(project);
  if (dailyDay) {
    touchDailyDay(dailyDay);
    updateDailyCompletion(dailyDay, beforeDailyStats, { title: task.title || 'Task', source: 'project' }, 'done');
  }
  const nextCompletedDate = taskCompletedISO(task);
  if (previousCompletedDate && previousCompletedDate !== nextCompletedDate) {
    refreshDailyStatusForDate(previousCompletedDate);
  }
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
  S.activeTab = normalizeGameTab(S.activeTab);

  const tabs = [
    ['notes', 'Notes'],
    ['board', 'Board'],
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
  else if (S.activeTab === 'board') renderGamePaintBoard(game);
  else if (S.activeTab === 'photos') renderGameMediaGridTab(game, 'photo');
  else if (S.activeTab === 'videos') renderGameMediaGridTab(game, 'video');
  else if (S.activeTab === 'sound') renderMediaTab(game, 'sound');
  else renderNotesTab(game);
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
    <div class="tab-scroll" id="game-notes-scroll">
      <div class="toolbar">
        <div class="toolbar-left">
          <div>
            <div class="eyebrow">Notes</div>
          </div>
        </div>
        <div class="toolbar-right note-add-top" id="note-add-top">
          <button class="ghost-btn" data-note-add="text">+ Text</button>
          <button class="ghost-btn" data-note-add="photo">+ Photo</button>
          <button class="ghost-btn" data-note-add="sound">+ Sound</button>
          <button class="ghost-btn" data-note-add="video">+ Video</button>
        </div>
      </div>
      ${blockCategoryControlsHTML(game.notes, 'game-note')}
      <div class="notes-list" id="notes-list"></div>
      <div class="note-add-float" id="note-add-float" aria-hidden="true">
        <button class="ghost-btn" data-note-add="text">+ Text</button>
        <button class="ghost-btn" data-note-add="photo">+ Photo</button>
        <button class="ghost-btn" data-note-add="sound">+ Sound</button>
        <button class="ghost-btn" data-note-add="video">+ Video</button>
      </div>
    </div>`;

  bindBlockCategoryControls(game.notes, 'game-note', shouldRender => {
    touchGame(game.id);
    markDirty();
    if (shouldRender) renderNotesTab(game);
  });
  const addTextNote = () => {
    game.notes = ensureBlockContainerShape(game.notes);
    const block = createTextBlock();
    block.categoryId = getActiveBlockCategory(game.notes).id;
    game.notes.blocks.push(block);
    touchGame(game.id);
    markDirty();
    renderNotesTab(game);
  };
  $('tab-content').querySelectorAll('[data-note-add]').forEach(btn => {
    btn.onclick = () => {
      const kind = btn.dataset.noteAdd;
      if (kind === 'text') addTextNote();
      else addNoteMedia(game, kind);
    };
  });
  const syncFloatingNoteAdd = () => {
    const scrollEl = $('game-notes-scroll');
    const topAdd = $('note-add-top');
    const floatAdd = $('note-add-float');
    if (!scrollEl || !topAdd || !floatAdd) return;
    const scrollRect = scrollEl.getBoundingClientRect();
    const topRect = topAdd.getBoundingClientRect();
    const topVisible = topRect.bottom > scrollRect.top + 4 && topRect.top < scrollRect.bottom - 4;
    const canScroll = scrollEl.scrollHeight > scrollEl.clientHeight + 4;
    const shouldShow = canScroll && !topVisible;
    floatAdd.classList.toggle('show', shouldShow);
    floatAdd.setAttribute('aria-hidden', shouldShow ? 'false' : 'true');
  };
  $('game-notes-scroll').addEventListener('scroll', syncFloatingNoteAdd, { passive: true });

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
  requestAnimationFrame(syncFloatingNoteAdd);
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
      notes: { blocks: [] },
      createdAt: now(),
      updatedAt: now(),
    });
    S.games.push(game);
    S.activeGameId = game.id;
    S.activeTab = 'notes';
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
  const files = filePathsFromDrop(fileList);
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

function filePathsFromDrop(dataTransferOrFiles) {
  const files = dataTransferOrFiles?.files || dataTransferOrFiles || [];
  return Array.from(files)
    .map(file => {
      try {
        return file?.path || (webUtils?.getPathForFile ? webUtils.getPathForFile(file) : '');
      } catch (e) {
        return file?.path || '';
      }
    })
    .filter(Boolean);
}

function dropHasFiles(dataTransfer) {
  return Array.from(dataTransfer?.types || []).includes('Files')
    || Array.from(dataTransfer?.files || []).length > 0;
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
  const drawing = S.drawing?.id === gameId ? ensureDrawingShape(S.drawing) : null;
  const paintWorkspace = scope === 'paint' && (game || project)
    ? getPaintWorkspaceForOwner(game || project)
    : null;
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
        : scope === 'drawing' && drawing
          ? getActiveMediaCategory(drawing, kind).id
          : scope === 'paint' && paintWorkspace
            ? getActivePaintCategory(paintWorkspace).id
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
    removePaintMediaRefs(game.paintBoards, mediaId);
  });
  S.dailyNotes.forEach(note => {
    note.blocks = (note.blocks || []).filter(block => block.mediaId !== mediaId);
  });
  if (S.notes?.blocks) {
    S.notes.blocks = S.notes.blocks.filter(block => block.mediaId !== mediaId);
  }
  if (S.moodboard?.boards) {
    S.moodboard.boards.forEach(board => {
      board.items = (board.items || []).filter(item => item.mediaId !== mediaId);
      board.updatedAt = now();
    });
    S.moodboard.updatedAt = now();
  }
  if (S.drawing?.id) {
    S.drawing.updatedAt = now();
  }
  S.photoBoards.forEach(board => {
    board.photoIds = (board.photoIds || []).filter(id => id !== mediaId);
  });
  S.projects.forEach(project => {
    if (project.doc?.blocks) project.doc.blocks = project.doc.blocks.filter(block => block.mediaId !== mediaId);
    if (project.notes?.blocks) project.notes.blocks = project.notes.blocks.filter(block => block.mediaId !== mediaId);
    removePaintMediaRefs(project.paintBoards, mediaId);
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
  const mediaGame = S.games.find(game => sameId(game.id, media.gameId));
  const mediaProject = S.projects.find(project => sameId(project.id, media.gameId));
  if (mediaGame) touchGame(mediaGame.id);
  if (mediaProject) touchProject(mediaProject);
  markDirty();
  if (S.view === 'projects') renderProjects();
  else if (S.view === 'game') renderGameWorkspace();
  else if (S.view === 'moodboard') renderMoodboard();
  else if (S.view === 'drawing') renderDrawing();
  else if (S.view === 'photo-boards') renderPhotoBoards();
  else renderApp();
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
  ensureWorkspaceShape();
  return {
    version: APP_VERSION,
    type: APP_TYPE,
    createdAt: S.createdAt,
    notes: S.notes,
    dailies: S.dailies,
    moodboard: S.moodboard,
    drawing: S.drawing,
    dailyNotes: S.dailyNotes,
    photoBoards: S.photoBoards,
    projects: S.projects,
    games: S.games.map(gameWithoutQuestions),
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

function detectProjectCreatedAt(data, fp) {
  if (data?.createdAt) return data.createdAt;
  try {
    const stat = fs.statSync(fp);
    const date = stat.birthtime || stat.ctime || stat.mtime;
    if (date && !Number.isNaN(date.getTime())) return date.toISOString();
  } catch (e) {}
  return now();
}

function loadProjectData(data, fp) {
  stopViewer();
  sessionCacheClear();
  const next = freshState();
  next.projectPath = fp;
  next.projectName = nodePath.basename(fp, '.refboard');
  next.createdAt = detectProjectCreatedAt(data, fp);
  next.modified = false;

  if (data.type === APP_TYPE && Number(data.version || 0) >= 2) {
    next.questionTemplates = [];
    next.games = Array.isArray(data.games) ? data.games.map(ensureGameShape).map(gameWithoutQuestions) : [];
    next.dailyNotes = Array.isArray(data.dailyNotes) ? data.dailyNotes.map(ensureDailyNoteShape) : [];
    next.notes = data.notes ? ensureNotesShape(data.notes) : notesFromLegacyDailyNotes(next.dailyNotes);
    next.dailies = ensureDailiesShape(data.dailies ? { ...data.dailies, createdAt: data.dailies.createdAt || next.createdAt } : { createdAt: next.createdAt });
    next.moodboard = ensureMoodboardShape(data.moodboard);
    next.drawing = ensureDrawingShape(data.drawing);
    next.photoBoards = Array.isArray(data.photoBoards) ? data.photoBoards.map(ensurePhotoBoardShape) : [];
    next.projects = Array.isArray(data.projects) ? data.projects.map(ensureProjectShape) : [];
    next.media = Array.isArray(data.media) ? data.media.map(ensureMediaShape) : [];
  } else {
    const migrated = migrateV1ToV2(data, next.projectName);
    next.questionTemplates = [];
    next.games = migrated.games.map(ensureGameShape).map(gameWithoutQuestions);
    next.media = migrated.media.map(ensureMediaShape);
    next.dailyNotes = [];
    next.notes = ensureNotesShape({ blocks: [] });
    next.dailies = ensureDailiesShape({ createdAt: next.createdAt });
    next.moodboard = ensureMoodboardShape();
    next.drawing = ensureDrawingShape();
    next.photoBoards = [];
    next.projects = [];
  }

  next.view = 'library';
  next.activeGameId = null;
  next.activeTab = 'notes';
  next.activeMediaId = null;
  next.activeDailyNoteId = null;
  next.activePhotoBoardId = null;
  next.activeProjectId = null;
  next.activeProjectTab = 'doc';
  next.activeMilestoneId = null;
  next.activeKanbanBoardId = null;
  next.activeDailyDate = todayISO();
  next.dailyCalendarMonth = monthISO(todayISO());
  next.activeMoodboardId = next.moodboard?.activeBoardId || null;
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
    notes: { blocks: [] },
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
  return { questionTemplates: [], games: [game], media };
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
    btn.onclick = () => handleMainNavClick(btn.dataset.view);
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
      if (S.view === 'moodboard' && S.moodboard?.boardOpen && moodboardSelectionIds(getActiveMoodboard()).length) {
        e.preventDefault();
        clearMoodboardSelection();
        renderMoodboard();
        return;
      }
      const paintContext = getActivePaintContext();
      if (paintContext && V.paintSelection) {
        e.preventDefault();
        V.paintSelection = null;
        rerenderPaintWorkspace(paintContext.owner, paintContext.ownerKind);
        return;
      }
      e.preventDefault();
      goBack();
      return;
    }
    if (['INPUT', 'TEXTAREA'].includes(e.target.tagName) || e.target.isContentEditable) return;
    const k = e.key.toLowerCase();
    if ((e.ctrlKey || e.metaKey) && k === 'z' && S.view === 'moodboard') {
      e.preventDefault();
      undoMoodboard();
      return;
    }
    if ((e.ctrlKey || e.metaKey) && k === 'a' && S.view === 'moodboard' && S.moodboard?.boardOpen) {
      e.preventDefault();
      const board = getActiveMoodboard();
      setMoodboardSelection((board?.items || []).map(item => item.id), board);
      renderMoodboard();
      return;
    }
    const paintContext = getActivePaintContext();
    if ((e.ctrlKey || e.metaKey) && k === 'z' && paintContext) {
      e.preventDefault();
      undoPaintBoard(paintContext.owner, paintContext.ownerKind, paintContext.workspace, paintContext.board);
      return;
    }
    if ((e.key === 'Delete' || e.key === 'Backspace') && paintContext && V.paintSelection) {
      e.preventDefault();
      deletePaintSelection(paintContext.owner, paintContext.ownerKind, paintContext.workspace, paintContext.board);
      return;
    }
    if (paintContext && k === ' ') {
      e.preventDefault();
      return;
    }
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

  setInterval(() => {
    if (!S.dailies?.enabled) return;
    const changed = ensureDailiesReady();
    if (changed && S.view === 'dailies') renderDailies();
  }, 60000);
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
