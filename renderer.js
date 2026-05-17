'use strict';
const { ipcRenderer } = require('electron');
const nodePath = require('path');
const fs = require('fs');
const os = require('os');
const crypto = require('crypto');

let parseGIF, decompressFrames;
try { ({ parseGIF, decompressFrames } = require('gifuct-js')); }
catch (e) { /* GIF frame control unavailable */ }

// ── Disk-based Session Cache (like Obsidian) ───────────────────────────────────
// Store decoded GIF metadata on disk instead of RAM.
// Cleared automatically when app closes.
const SESSION_CACHE_DIR = nodePath.join(os.tmpdir(), 'refboard-session-' + process.pid);
try { fs.mkdirSync(SESSION_CACHE_DIR, { recursive: true }); } catch (e) {}

function sessionCacheKey(fp) {
  return crypto.createHash('md5').update(fp).digest('hex');
}
function sessionCacheWrite(fp, data) {
  try {
    const p = nodePath.join(SESSION_CACHE_DIR, sessionCacheKey(fp) + '.json');
    fs.writeFileSync(p, JSON.stringify(data));
    return true;
  } catch (e) { return false; }
}
function sessionCacheRead(fp) {
  try {
    const p = nodePath.join(SESSION_CACHE_DIR, sessionCacheKey(fp) + '.json');
    if (!fs.existsSync(p)) return null;
    return JSON.parse(fs.readFileSync(p, 'utf8'));
  } catch (e) { return null; }
}
function sessionCacheClear() {
  try {
    fs.readdirSync(SESSION_CACHE_DIR).forEach(f => {
      try { fs.unlinkSync(nodePath.join(SESSION_CACHE_DIR, f)); } catch(e) {}
    });
  } catch (e) {}
}
// Clean up temp files on exit
process.on('exit', sessionCacheClear);

// ── State ─────────────────────────────────────────────────────────────────────
let S = {
  projectPath: null,
  projectName: 'Untitled',
  modified: false,
  folders: [],
  selFolder: null,
  selPage: null,
  selMedia: null,
};

let V = {
  zoom: 1, panX: 0, panY: 0,
  panning: false, px: 0, py: 0,
  gifFrames: null,
  gifIdx: 0,
  gifPlaying: false,
  gifTimer: null,
  gifRenderedFrames: null,
  gifTotalDuration: 0,
  speed: 1,
  tlDragging: false,
  frameMode: 'playback',
  pixelPerfect: true,
  currentMediaType: null,
};

// ── Single GIF slot — only 1 decoded GIF lives in RAM at once ─────────────────
let activeGifCache = null; // { fp, frames, rendered, w, h }

function evictActiveGif() {
  if (!activeGifCache) return;
  if (activeGifCache.rendered) {
    activeGifCache.rendered.forEach(c => { c.width = 0; c.height = 0; });
  }
  activeGifCache.rendered = null;
  activeGifCache.frames = null;
  activeGifCache = null;
}

// ── Virtual Scroll ─────────────────────────────────────────────────────────────
// Only DOM nodes for visible thumbnails exist. Invisible ones are freed.
const THUMB_H    = 132; // 120px height + 10px gap + 2px border
const THUMB_OVER = 3;

let vsState = {
  page: null,
  rendered: new Map(), // idx -> DOM node
};

// Loading state
let loadingState = { active: false, text: 'Loading...', progress: 0, total: 0 };

// ── Loading Overlay ───────────────────────────────────────────────────────────
function showLoading(text = 'Loading...', total = 0) {
  loadingState = { active: true, text, progress: 0, total };
  const ov = $('loading-overlay');
  if (ov) {
    ov.classList.remove('hidden');
    ov.querySelector('.loading-text').textContent = text;
    updateLoadingProgress(0);
  }
}
function hideLoading() {
  loadingState.active = false;
  const ov = $('loading-overlay');
  if (ov) ov.classList.add('hidden');
}
function updateLoadingProgress(n) {
  loadingState.progress = n;
  const bar = document.querySelector('.loading-progress-bar');
  if (bar && loadingState.total > 0)
    bar.style.width = Math.min(100, (n / loadingState.total) * 100) + '%';
}
function updateLoadingText(text) {
  loadingState.text = text;
  const el = document.querySelector('.loading-text');
  if (el) el.textContent = text;
}

// ── DOM refs ──────────────────────────────────────────────────────────────────
const $  = id => document.getElementById(id);
const folderTree   = $('folder-tree');
const mediaList    = $('media-list');
const mediaPanel   = $('media-panel');
const pageTitleLbl = $('page-title-label');
const viewerEmpty  = $('viewer-empty');
const viewerStage  = $('viewer-stage');
const gifCanvas    = $('gif-canvas');
const imgViewer    = $('img-viewer');
const vidViewer    = $('vid-viewer');
const playbackBar  = $('playback-bar');
const infoPanel    = $('info-panel');
const frameDsp     = $('frame-display');
const zoomPct      = $('zoom-pct');
const projName     = $('project-name');
const modalBg      = $('modal-bg');
const tlFill       = $('tl-fill');
const tlThumb      = $('tl-thumb');
const tCurrent     = $('t-current');
const tTotal       = $('t-total');
const timelineRow  = $('timeline-row');

// ── Helpers ───────────────────────────────────────────────────────────────────
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
const esc = s => s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');

function mediaType(fp) {
  const e = nodePath.extname(fp).toLowerCase();
  if (e === '.gif') return 'gif';
  if (['.mp4','.webm','.mov','.mkv'].includes(e)) return 'video';
  return 'image';
}

const getFolder  = id => S.folders.find(f => f.id === id);
const getCurPage = () => getFolder(S.selFolder)?.pages.find(p => p.id === S.selPage);
const getCurMedia= () => getCurPage()?.media.find(m => m.id === S.selMedia);

// ── Toast ─────────────────────────────────────────────────────────────────────
let toastTimer;
function toast(msg) {
  const el = $('toast');
  el.textContent = msg;
  el.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => el.classList.remove('show'), 2000);
}

// ── Sidebar ───────────────────────────────────────────────────────────────────
function renderSidebar() {
  folderTree.innerHTML = '';
  S.folders.forEach(folder => {
    const wrap = document.createElement('div');
    wrap.className = 'folder-item';

    const hdr = document.createElement('div');
    hdr.className = 'folder-hdr' + (S.selFolder === folder.id ? ' sel' : '');
    hdr.innerHTML = `
      <span class="f-arrow ${folder.open ? 'open' : ''}">▶</span>
      <span class="f-ico">📁</span>
      <span class="f-name">${esc(folder.name)}</span>
      <div class="f-actions">
        <button class="tiny-btn" title="Rename">✎</button>
        <button class="tiny-btn del" title="Delete">✕</button>
      </div>`;

    hdr.addEventListener('click', e => {
      if (e.target.closest('.f-actions')) return;
      folder.open = !folder.open;
      markDirty(); renderSidebar();
    });
    hdr.querySelectorAll('.tiny-btn')[0].onclick = e => {
      e.stopPropagation();
      showModal('Rename Folder', folder.name, 'Rename', name => {
        folder.name = name; markDirty(); renderSidebar();
      });
    };
    hdr.querySelectorAll('.tiny-btn')[1].onclick = e => {
      e.stopPropagation();
      if (!confirm(`Delete folder "${folder.name}" and all its content?`)) return;
      S.folders = S.folders.filter(f => f.id !== folder.id);
      if (S.selFolder === folder.id) { S.selFolder = S.selPage = S.selMedia = null; clearViewer(); renderMediaPanel(); }
      markDirty(); renderSidebar();
    };

    const pList = document.createElement('div');
    pList.className = 'pages-list';
    pList.style.display = folder.open ? '' : 'none';

    folder.pages.forEach(page => {
      const row = document.createElement('div');
      row.className = 'page-row' + (S.selPage === page.id ? ' active' : '');
      row.innerHTML = `
        <span class="page-name">${esc(page.name)}</span>
        <div class="p-actions">
          <button class="tiny-btn" title="Rename">✎</button>
          <button class="tiny-btn del" title="Delete">✕</button>
        </div>`;
      row.addEventListener('click', e => {
        if (e.target.closest('.p-actions')) return;
        S.selFolder = folder.id; S.selPage = page.id; S.selMedia = null;
        evictActiveGif();
        clearViewer(); renderMediaPanel(); renderSidebar();
      });
      row.querySelectorAll('.tiny-btn')[0].onclick = e => {
        e.stopPropagation();
        showModal('Rename Page', page.name, 'Rename', name => {
          page.name = name; markDirty(); renderSidebar(); renderMediaPanel();
        });
      };
      row.querySelectorAll('.tiny-btn')[1].onclick = e => {
        e.stopPropagation();
        if (!confirm(`Delete page "${page.name}"?`)) return;
        folder.pages = folder.pages.filter(p => p.id !== page.id);
        if (S.selPage === page.id) { S.selPage = S.selMedia = null; clearViewer(); }
        markDirty(); renderSidebar();
      };
      pList.appendChild(row);
    });

    const addRow = document.createElement('div');
    addRow.className = 'add-page-row';
    addRow.innerHTML = '<span>+</span><span>New page</span>';
    addRow.onclick = () => showModal('New Page', '', 'Create', name => {
      folder.pages.push({ id: uid(), name, media: [], comments: '' });
      folder.open = true; markDirty(); renderSidebar();
    });
    pList.appendChild(addRow);

    wrap.appendChild(hdr);
    wrap.appendChild(pList);
    folderTree.appendChild(wrap);
  });

  const addFolderCard = document.createElement('div');
  addFolderCard.className = 'add-folder-card';
  addFolderCard.innerHTML = `<div class="add-card-content"><span class="add-card-icon">+</span><span class="add-card-text">New Folder</span></div>`;
  addFolderCard.onclick = () => showModal('New Folder', '', 'Create', name => {
    S.folders.push({ id: uid(), name, open: true, pages: [] });
    markDirty(); renderSidebar();
  });
  addFolderCard.addEventListener('dragover', e => { e.preventDefault(); e.stopPropagation(); });
  folderTree.appendChild(addFolderCard);
}

// ── Media Panel — Virtual Scroll ───────────────────────────────────────────────
let draggedItem = null;
let draggedIdx  = null;
let vsScrollRaf = null;

function renderMediaPanel() {
  const page = getCurPage();
  if (!page) { mediaPanel.classList.add('hidden'); infoPanel.classList.add('hidden'); return; }
  mediaPanel.classList.remove('hidden');
  pageTitleLbl.textContent = page.name;

  // Full reset
  mediaList.innerHTML = '';
  vsState.rendered.clear();
  vsState.page = page;

  const total = page.media.length;

  // Tall spacer = virtual list height
  const spacer = document.createElement('div');
  spacer.id = 'vs-spacer';
  spacer.style.cssText = `height:${total * THUMB_H}px;position:relative;`;
  mediaList.appendChild(spacer);

  // "Add Media" card always at bottom (outside spacer flow)
  mediaList.appendChild(buildAddMediaCard());

  vsRender(page);

  mediaList.onscroll = () => {
    if (vsScrollRaf) return;
    vsScrollRaf = requestAnimationFrame(() => {
      vsScrollRaf = null;
      vsRender(vsState.page);
    });
  };
}

function vsRender(page) {
  if (!page) return;
  const total    = page.media.length;
  const scrollTop = mediaList.scrollTop;
  const viewH    = mediaList.clientHeight;
  const start    = Math.max(0, Math.floor(scrollTop / THUMB_H) - THUMB_OVER);
  const end      = Math.min(total - 1, Math.ceil((scrollTop + viewH) / THUMB_H) + THUMB_OVER);

  // Remove out-of-view nodes — frees img/canvas memory
  vsState.rendered.forEach((node, idx) => {
    if (idx < start || idx > end) {
      const img = node.querySelector('img');
      if (img) img.src = '';
      const c = node.querySelector('canvas');
      if (c) { c.width = 0; c.height = 0; }
      node.remove();
      vsState.rendered.delete(idx);
    }
  });

  const spacer = $('vs-spacer');
  for (let i = start; i <= end; i++) {
    if (vsState.rendered.has(i)) continue;
    const item = page.media[i];
    if (!item) continue;
    const node = buildThumb(item, i, page);
    node.style.cssText += `;position:absolute;top:${i * THUMB_H}px;left:0;right:0;`;
    spacer.appendChild(node);
    vsState.rendered.set(i, node);
  }
}

function buildThumb(item, idx, page) {
  const thumb = document.createElement('div');
  thumb.className = 'm-thumb' + (S.selMedia === item.id ? ' active' : '');
  thumb.dataset.mediaId = item.id;
  thumb.draggable = true;

  const [cls, lbl] = item.type === 'gif' ? ['b-gif','GIF'] : item.type === 'video' ? ['b-vid','VID'] : ['b-img','IMG'];

  if (item.type === 'video') {
    const c = document.createElement('canvas'); c.width = 176; c.height = 110;
    thumb.appendChild(c);
    const v = document.createElement('video');
    v.muted = true;
    v.src = 'file://' + item.path;
    v.currentTime = 0.05;
    v.addEventListener('seeked', () => {
      try { c.getContext('2d').drawImage(v, 0, 0, 176, 110); } catch(e) {}
      v.src = ''; v.load(); // release decoder
    }, { once: true });
  } else {
    const img = document.createElement('img');
    img.loading = 'lazy';
    img.decoding = 'async';
    img.src = 'file://' + item.path;
    img.draggable = false;
    thumb.appendChild(img);
  }

  thumb.insertAdjacentHTML('beforeend', `
    <div class="m-label">${esc(item.name)}</div>
    <span class="m-badge ${cls}">${lbl}</span>
    <button class="m-del" title="Remove">✕</button>`);

  thumb.querySelector('.m-del').onclick = e => {
    e.stopPropagation();
    if (S.selMedia === item.id) { S.selMedia = null; clearViewer(); }
    getCurPage().media = getCurPage().media.filter(m => m.id !== item.id);
    markDirty(); renderMediaPanel();
  };

  thumb.onclick = () => {
    S.selMedia = item.id;
    V.currentMediaType = item.type;
    vsState.rendered.forEach(n => n.classList.remove('active'));
    thumb.classList.add('active');
    loadMedia(item);
    renderInfo(item, page);
  };

  // Drag-reorder
  thumb.addEventListener('dragstart', e => {
    draggedItem = item; draggedIdx = idx;
    thumb.classList.add('dragging');
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('text/plain', item.id);
  });
  thumb.addEventListener('dragend', () => {
    thumb.classList.remove('dragging');
    draggedItem = null; draggedIdx = null;
    vsState.rendered.forEach(n => n.classList.remove('drag-over-top','drag-over-bottom'));
  });
  thumb.addEventListener('dragover', e => {
    e.preventDefault(); e.stopPropagation();
    if (!draggedItem || draggedItem.id === item.id) return;
    const mid = thumb.getBoundingClientRect().top + THUMB_H / 2;
    thumb.classList.toggle('drag-over-top',    e.clientY < mid);
    thumb.classList.toggle('drag-over-bottom', e.clientY >= mid);
  });
  thumb.addEventListener('dragleave', () => {
    thumb.classList.remove('drag-over-top','drag-over-bottom');
  });
  thumb.addEventListener('drop', e => {
    e.preventDefault(); e.stopPropagation();
    if (!draggedItem || draggedItem.id === item.id) return;
    const mid = thumb.getBoundingClientRect().top + THUMB_H / 2;
    const insertBefore = e.clientY < mid;
    const media = getCurPage().media;
    const from = media.findIndex(m => m.id === draggedItem.id);
    if (from === -1) return;
    const [removed] = media.splice(from, 1);
    let to = media.findIndex(m => m.id === item.id);
    if (!insertBefore) to++;
    media.splice(to, 0, removed);
    markDirty(); renderMediaPanel();
    thumb.classList.remove('drag-over-top','drag-over-bottom');
  });

  return thumb;
}

function buildAddMediaCard() {
  const card = document.createElement('div');
  card.className = 'add-media-card';
  card.id = 'add-media-drop-zone';
  card.innerHTML = `<div class="add-card-content"><span class="add-card-icon">+</span><span class="add-card-text">Add Media</span><span class="add-card-hint">Click or drop files</span></div>`;
  card.onclick = addMedia;
  card.addEventListener('dragover', e => { e.preventDefault(); e.stopPropagation(); card.classList.add('drag-target'); });
  card.addEventListener('dragleave', () => card.classList.remove('drag-target'));
  card.addEventListener('drop', e => {
    e.preventDefault(); e.stopPropagation();
    card.classList.remove('drag-target');
    if (draggedItem) { draggedItem = null; draggedIdx = null; return; }
    handleDroppedFiles(e.dataTransfer.files);
  });
  return card;
}

// ── GIF frame rendering ───────────────────────────────────────────────────────
function preRenderGifFrames(frames, w, h) {
  const rendered = [];
  const comp = document.createElement('canvas'); comp.width = w; comp.height = h;
  const compCtx = comp.getContext('2d');
  const prev = document.createElement('canvas'); prev.width = w; prev.height = h;
  const prevCtx = prev.getContext('2d');
  const patch = document.createElement('canvas');
  const patchCtx = patch.getContext('2d');

  frames.forEach(frame => {
    if (frame.disposalType === 3) { prevCtx.clearRect(0,0,w,h); prevCtx.drawImage(comp,0,0); }
    if (patch.width !== frame.dims.width || patch.height !== frame.dims.height) {
      patch.width = frame.dims.width; patch.height = frame.dims.height;
    }
    patchCtx.putImageData(new ImageData(new Uint8ClampedArray(frame.patch), frame.dims.width, frame.dims.height), 0, 0);
    compCtx.drawImage(patch, frame.dims.left, frame.dims.top);

    const fc = document.createElement('canvas'); fc.width = w; fc.height = h;
    fc.getContext('2d').drawImage(comp, 0, 0);
    rendered.push(fc);

    if      (frame.disposalType === 2) compCtx.clearRect(frame.dims.left, frame.dims.top, frame.dims.width, frame.dims.height);
    else if (frame.disposalType === 3) { compCtx.clearRect(0,0,w,h); compCtx.drawImage(prev,0,0); }
  });

  comp.width = prev.width = patch.width = 0;
  comp.height = prev.height = patch.height = 0;
  return rendered;
}

// ── Info panel ────────────────────────────────────────────────────────────────
function renderInfo(item, page) {
  infoPanel.classList.remove('hidden');
  $('inp-title').value = item.name;
  $('inp-desc').value  = item.description || '';
  $('inp-notes').value = page.comments || '';
  $('media-meta').innerHTML = `
    <div class="meta-row"><span class="meta-key">Type</span><span class="meta-value">${item.type.toUpperCase()}</span></div>
    <div class="meta-row"><span class="meta-key">File</span><span class="meta-value" style="font-size:10.5px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:130px">${nodePath.basename(item.path)}</span></div>
  `;
  $('inp-title').oninput = () => { item.name = $('inp-title').value; markDirty(); vsRefreshLabel(item); };
  $('inp-desc').oninput  = () => { item.description = $('inp-desc').value; markDirty(); };
  $('inp-notes').oninput = () => { page.comments = $('inp-notes').value; markDirty(); };
}

function vsRefreshLabel(item) {
  vsState.rendered.forEach(node => {
    if (node.dataset.mediaId === item.id) {
      const lbl = node.querySelector('.m-label');
      if (lbl) lbl.textContent = item.name;
    }
  });
}

// ── Viewer ────────────────────────────────────────────────────────────────────
function clearViewer() {
  viewerEmpty.classList.remove('hidden');
  viewerStage.classList.add('hidden');
  playbackBar.classList.add('hidden');
  infoPanel.classList.add('hidden');
  stopGif(); vidViewer.pause();
  vidViewer.src = ''; vidViewer.load();
  imgViewer.src = '';
  gifCanvas.getContext('2d').clearRect(0, 0, gifCanvas.width, gifCanvas.height);
  setTimeline(0, 0);
  V.zoom = 1; V.panX = 0; V.panY = 0;
  V.gifFrames = null; V.gifRenderedFrames = null; V.currentMediaType = null;
}

function loadMedia(item) {
  viewerEmpty.classList.add('hidden');
  viewerStage.classList.remove('hidden');
  stopGif(); vidViewer.pause();
  gifCanvas.classList.add('hidden');
  imgViewer.classList.add('hidden');
  vidViewer.classList.add('hidden');
  V.zoom = 1; V.panX = 0; V.panY = 0;
  V.currentMediaType = item.type;
  updateZoomDisplay();
  applyPixelPerfect();

  const url = 'file://' + item.path;

  if (item.type === 'gif') {
    loadGif(item.path, url);
    playbackBar.classList.remove('hidden');
    updateModeUI(); updateTimelineVisibility();
  } else if (item.type === 'video') {
    vidViewer.classList.remove('hidden');
    vidViewer.src = url;
    vidViewer.volume = $('vol-slider').value / 100;
    vidViewer.playbackRate = V.speed;
    vidViewer.play();
    playbackBar.classList.remove('hidden');
    applyXform(vidViewer); updatePlayIcons(); updateModeUI(); updateTimelineVisibility();
  } else {
    imgViewer.classList.remove('hidden');
    imgViewer.src = url;
    imgViewer.onload = fitToScreen;
    playbackBar.classList.add('hidden');
    frameDsp.textContent = 'IMAGE';
    setTimeline(0, 0);
  }
}

function updateTimelineVisibility() {
  if (!timelineRow) return;
  timelineRow.classList.toggle('hidden', V.currentMediaType === 'gif' && V.frameMode === 'playback');
}

// ── GIF Loading ───────────────────────────────────────────────────────────────
function loadGif(fp, url) {
  if (V.frameMode === 'playback') { showNativeGif(url); return; }

  // Already in RAM?
  if (activeGifCache && activeGifCache.fp === fp) {
    useGifFrames(activeGifCache.frames, activeGifCache.rendered, activeGifCache.w, activeGifCache.h);
    return;
  }

  evictActiveGif();

  showLoading('Processing GIF…', 100);
  gifCanvas.classList.remove('hidden');
  imgViewer.classList.add('hidden');
  frameDsp.textContent = 'Loading…';

  setTimeout(() => {
    try {
      if (!parseGIF || !decompressFrames) { hideLoading(); showNativeGif(url); return; }

      updateLoadingProgress(20);
      const buf = fs.readFileSync(fp);
      const ab  = buf.buffer.slice(buf.byteOffset, buf.byteOffset + buf.byteLength);

      updateLoadingProgress(40);
      const gif    = parseGIF(ab);
      const frames = decompressFrames(gif, true);
      if (!frames.length) throw new Error('no frames');

      updateLoadingProgress(60);
      const w = gif.lsd.width, h = gif.lsd.height;
      const rendered = preRenderGifFrames(frames, w, h);

      updateLoadingProgress(90);
      // Write lightweight metadata to disk (NOT pixel data)
      sessionCacheWrite(fp, { w, h, delays: frames.map(f => f.delay || 100), count: frames.length });

      activeGifCache = { fp, frames, rendered, w, h };
      hideLoading();
      useGifFrames(frames, rendered, w, h);
    } catch (e) {
      hideLoading(); showNativeGif(url);
    }
  }, 10);
}

function showNativeGif(url) {
  imgViewer.classList.remove('hidden');
  gifCanvas.classList.add('hidden');
  imgViewer.src = url;
  imgViewer.onload = fitToScreen;
  frameDsp.textContent = 'GIF (Playback)';
  V.gifFrames = null; V.gifRenderedFrames = null;
}

function useGifFrames(frames, rendered, w, h) {
  V.gifFrames = frames; V.gifRenderedFrames = rendered;
  V.gifIdx = 0;
  V.gifTotalDuration = frames.reduce((s, f) => s + (f.delay || 100), 0);
  gifCanvas.width = w; gifCanvas.height = h;
  gifCanvas.classList.remove('hidden');
  imgViewer.classList.add('hidden');
  drawGifFrame(0);
  applyXform(gifCanvas); fitToScreen(); updateFrameDisplay();
}

function drawGifFrame(idx) {
  if (!V.gifRenderedFrames || idx >= V.gifRenderedFrames.length) return;
  const ctx = gifCanvas.getContext('2d');
  ctx.clearRect(0, 0, gifCanvas.width, gifCanvas.height);
  ctx.drawImage(V.gifRenderedFrames[idx], 0, 0);
}

function stopGif() {
  V.gifPlaying = false;
  if (V.gifTimer) { clearTimeout(V.gifTimer); V.gifTimer = null; }
}

function playGif() {
  if (!V.gifFrames || V.frameMode === 'playback') return;
  V.gifPlaying = true; updatePlayIcons();
  const tick = () => {
    if (!V.gifPlaying || !V.gifFrames) return;
    V.gifTimer = setTimeout(() => {
      V.gifIdx = (V.gifIdx + 1) % V.gifFrames.length;
      drawGifFrame(V.gifIdx); updateFrameDisplay(); tick();
    }, (V.gifFrames[V.gifIdx].delay || 100) / V.speed);
  };
  tick();
}

function pauseGif() { stopGif(); updatePlayIcons(); }

function updateFrameDisplay() {
  if (!V.gifFrames) return;
  frameDsp.textContent = `Frame ${V.gifIdx + 1} / ${V.gifFrames.length}`;
  let elapsed = 0;
  for (let i = 0; i < V.gifIdx; i++) elapsed += V.gifFrames[i].delay || 100;
  setTimeline(elapsed, V.gifTotalDuration);
}

function updateModeUI() {
  const btn = $('btn-mode');
  if (!btn) return;
  if (V.frameMode === 'playback') { btn.textContent = '▶ Playback'; btn.classList.remove('fbf'); }
  else                             { btn.textContent = '⊞ Frames';   btn.classList.add('fbf'); }
  updateTimelineVisibility();
}

function toggleMode() {
  const cur = getCurMedia();
  if (!cur) return;
  V.frameMode = V.frameMode === 'playback' ? 'framebyframe' : 'playback';
  updateModeUI(); stopGif(); loadMedia(cur);
}

// ── Video events ──────────────────────────────────────────────────────────────
vidViewer.addEventListener('timeupdate', () => {
  if (!V.tlDragging) setTimeline(vidViewer.currentTime * 1000, vidViewer.duration * 1000);
  if (V.frameMode === 'framebyframe') frameDsp.textContent = `Frame ~${Math.floor(vidViewer.currentTime * 30)} @ 30fps`;
});
vidViewer.addEventListener('loadedmetadata', () => { setTimeline(0, vidViewer.duration * 1000); fitToScreen(); });
vidViewer.addEventListener('play',  updatePlayIcons);
vidViewer.addEventListener('pause', updatePlayIcons);

function updatePlayIcons() {
  const playing = !vidViewer.paused || V.gifPlaying;
  $('icon-play').classList.toggle('hidden',  playing);
  $('icon-pause').classList.toggle('hidden', !playing);
}

// ── Timeline ──────────────────────────────────────────────────────────────────
function setTimeline(curMs, totalMs) {
  const pct = totalMs > 0 ? (curMs / totalMs) * 100 : 0;
  tlFill.style.width = pct + '%';
  tlThumb.style.left = pct + '%';
  tCurrent.textContent = fmtTime(curMs);
  tTotal.textContent   = fmtTime(totalMs);
}
function fmtTime(ms) {
  const s = Math.floor((ms || 0) / 1000), m = Math.floor(s / 60);
  return `${m}:${String(s % 60).padStart(2, '0')}`;
}

const tlTrack = $('timeline-track');
tlTrack.addEventListener('mousedown', e => {
  V.tlDragging = true; seekToMouse(e);
  document.addEventListener('mousemove', onTlMove);
  document.addEventListener('mouseup',   onTlUp);
});
function onTlMove(e) { if (V.tlDragging) seekToMouse(e); }
function onTlUp()    { V.tlDragging = false; document.removeEventListener('mousemove', onTlMove); document.removeEventListener('mouseup', onTlUp); }

function seekToMouse(e) {
  const rect = tlTrack.getBoundingClientRect();
  const pct  = Math.max(0, Math.min(1, (e.clientX - rect.left) / rect.width));
  if (!vidViewer.classList.contains('hidden') && vidViewer.duration) {
    vidViewer.currentTime = pct * vidViewer.duration;
  } else if (V.gifFrames && V.frameMode === 'framebyframe') {
    V.gifIdx = Math.max(0, Math.min(V.gifFrames.length - 1, Math.floor(pct * V.gifFrames.length)));
    drawGifFrame(V.gifIdx); updateFrameDisplay();
  }
}

// ── Playback buttons ──────────────────────────────────────────────────────────
$('pb-play').onclick = () => {
  if (!vidViewer.classList.contains('hidden')) { vidViewer.paused ? vidViewer.play() : vidViewer.pause(); }
  else if (V.gifFrames && V.frameMode === 'framebyframe') { V.gifPlaying ? pauseGif() : playGif(); }
};
$('pb-prev').onclick = () => {
  if (!vidViewer.classList.contains('hidden')) {
    vidViewer.currentTime = Math.max(0, vidViewer.currentTime - (V.frameMode === 'framebyframe' ? 1/30 : 1));
  } else if (V.gifFrames && V.frameMode === 'framebyframe') {
    V.gifIdx = (V.gifIdx - 1 + V.gifFrames.length) % V.gifFrames.length;
    drawGifFrame(V.gifIdx); updateFrameDisplay();
  }
};
$('pb-next').onclick = () => {
  if (!vidViewer.classList.contains('hidden')) {
    vidViewer.currentTime = Math.min(vidViewer.duration, vidViewer.currentTime + (V.frameMode === 'framebyframe' ? 1/30 : 1));
  } else if (V.gifFrames && V.frameMode === 'framebyframe') {
    V.gifIdx = (V.gifIdx + 1) % V.gifFrames.length;
    drawGifFrame(V.gifIdx); updateFrameDisplay();
  }
};
$('btn-mode').onclick = toggleMode;

document.querySelectorAll('.spd').forEach(btn => {
  btn.onclick = () => {
    document.querySelectorAll('.spd').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    V.speed = parseFloat(btn.dataset.v);
    vidViewer.playbackRate = V.speed;
  };
});

$('vol-slider').oninput = () => { vidViewer.volume = $('vol-slider').value / 100; updateVolIcon(); };
$('btn-mute').onclick   = () => { vidViewer.muted = !vidViewer.muted; updateVolIcon(); };
function updateVolIcon() {
  const muted = vidViewer.muted || vidViewer.volume === 0;
  $('icon-vol').classList.toggle('hidden',  muted);
  $('icon-mute').classList.toggle('hidden', !muted);
}

// ── Zoom / Pan ────────────────────────────────────────────────────────────────
function activeEl() {
  if (!gifCanvas.classList.contains('hidden')) return gifCanvas;
  if (!imgViewer.classList.contains('hidden'))  return imgViewer;
  return vidViewer;
}
function applyXform(el) { el.style.transform = `translate(${V.panX}px,${V.panY}px) scale(${V.zoom})`; }
function updateZoomDisplay() { zoomPct.textContent = Math.round(V.zoom * 100) + '%'; }

$('z-in').onclick  = () => changeZoom(0.25);
$('z-out').onclick = () => changeZoom(-0.25);
$('z-fit').onclick = fitToScreen;

function changeZoom(d) {
  V.zoom = Math.max(0.1, Math.min(10, V.zoom + d));
  updateZoomDisplay(); applyXform(activeEl());
}

function fitToScreen() {
  const el   = activeEl();
  const wrap = $('viewer-wrap');
  const maxW = wrap.clientWidth * 0.9, maxH = wrap.clientHeight * 0.85;
  const w = el.naturalWidth || el.videoWidth || el.width;
  const h = el.naturalHeight || el.videoHeight || el.height;
  if (!w || !h) return;
  V.zoom = Math.min(maxW / w, maxH / h, 1);
  V.panX = V.panY = 0;
  updateZoomDisplay(); applyXform(el);
}

// Pan
viewerStage.addEventListener('mousedown', e => { if (e.button !== 0) return; V.panning = true; V.px = e.clientX; V.py = e.clientY; });
document.addEventListener('mousemove', e => {
  if (!V.panning) return;
  V.panX += e.clientX - V.px; V.panY += e.clientY - V.py;
  V.px = e.clientX; V.py = e.clientY;
  applyXform(activeEl());
});
document.addEventListener('mouseup', () => { V.panning = false; });

// Wheel zoom — batched in rAF to prevent jank
let wheelRaf = null, pendingDelta = 0;
$('viewer-wrap').addEventListener('wheel', e => {
  e.preventDefault();
  pendingDelta += e.deltaY < 0 ? 0.1 : -0.1;
  if (!wheelRaf) {
    wheelRaf = requestAnimationFrame(() => {
      changeZoom(pendingDelta);
      pendingDelta = 0; wheelRaf = null;
    });
  }
}, { passive: false });

function applyPixelPerfect() {
  const val = V.pixelPerfect ? 'pixelated' : 'auto';
  gifCanvas.style.imageRendering = val;
  imgViewer.style.imageRendering  = val;
  vidViewer.style.imageRendering  = val;
}

// ── Keyboard shortcuts ────────────────────────────────────────────────────────
document.addEventListener('keydown', e => {
  if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;
  const k = e.key.toLowerCase();
  if (k === ' ')          { e.preventDefault(); $('pb-play').click(); }
  if (k === 'arrowleft')  { e.preventDefault(); $('pb-prev').click(); }
  if (k === 'arrowright') { e.preventDefault(); $('pb-next').click(); }
  if (k === 'f') fitToScreen();
  if (k === 'p') { V.pixelPerfect = !V.pixelPerfect; applyPixelPerfect(); }
  if (k === 'm') toggleMode();
  if (e.ctrlKey || e.metaKey) {
    if (k === 'n') { e.preventDefault(); newProject(); }
    if (k === 'o') { e.preventDefault(); openProject(); }
    if (k === 's') { e.preventDefault(); e.shiftKey ? saveAsProject() : saveProject(); }
  }
});

// ── Drag & Drop on viewer ─────────────────────────────────────────────────────
const viewerWrap = $('viewer-wrap');
viewerWrap.addEventListener('dragover',  e => { e.preventDefault(); e.stopPropagation(); viewerWrap.classList.add('drag-over'); });
viewerWrap.addEventListener('dragleave', e => { e.preventDefault(); e.stopPropagation(); viewerWrap.classList.remove('drag-over'); });
viewerWrap.addEventListener('drop', e => {
  e.preventDefault(); e.stopPropagation();
  viewerWrap.classList.remove('drag-over');
  handleDroppedFiles(e.dataTransfer.files);
});

function handleDroppedFiles(files) {
  const page = getCurPage();
  if (!page) { toast('Select a page first'); return; }
  const valid = Array.from(files).filter(f => /\.(png|jpe?g|gif|webp|bmp|svg|mp4|webm|mov|mkv)$/i.test(f.name));
  if (!valid.length) { toast('No valid media files'); return; }
  valid.forEach(f => {
    page.media.push({ id: uid(), name: nodePath.basename(f.path, nodePath.extname(f.path)), path: f.path, type: mediaType(f.path), description: '' });
  });
  markDirty(); renderMediaPanel();
  toast(`Added ${valid.length} file(s)`);
}

// ── Project I/O ───────────────────────────────────────────────────────────────
function markDirty() {
  S.modified = true;
  projName.textContent = S.projectName + ' •';
}

function newProject() {
  if (S.modified && !confirm('Discard unsaved changes?')) return;
  evictActiveGif(); sessionCacheClear();
  S = { projectPath: null, projectName: 'Untitled', modified: false, folders: [], selFolder: null, selPage: null, selMedia: null };
  projName.textContent = S.projectName;
  clearViewer(); renderSidebar(); renderMediaPanel();
}

function openProject() {
  ipcRenderer.invoke('dialog:open', {
    title: 'Open RefBoard Project',
    filters: [{ name: 'RefBoard', extensions: ['refboard'] }],
    properties: ['openFile'],
  }).then(result => {
    if (result.canceled || !result.filePaths.length) return;
    const fp = result.filePaths[0];
    showLoading('Opening project…', 100);
    evictActiveGif(); sessionCacheClear();
    setTimeout(() => {
      try {
        updateLoadingProgress(30);
        const data = JSON.parse(fs.readFileSync(fp, 'utf-8'));
        updateLoadingProgress(60);
        S.projectPath = fp;
        S.projectName = nodePath.basename(fp, '.refboard');
        S.folders = data.folders || [];
        S.selFolder = S.selPage = S.selMedia = null;
        S.modified = false;
        projName.textContent = S.projectName;
        updateLoadingProgress(80);
        clearViewer(); renderSidebar(); renderMediaPanel();
        updateLoadingProgress(100); hideLoading();
        toast('Project opened');
      } catch (e) { hideLoading(); toast('Failed to open project'); }
    }, 50);
  });
}

function saveProject()   { if (!S.projectPath) { saveAsProject(); return; } doSave(S.projectPath); }
function saveAsProject() {
  ipcRenderer.invoke('dialog:save', {
    title: 'Save RefBoard Project',
    defaultPath: S.projectName + '.refboard',
    filters: [{ name: 'RefBoard', extensions: ['refboard'] }],
  }).then(result => {
    if (result.canceled || !result.filePath) return;
    S.projectPath = result.filePath;
    S.projectName = nodePath.basename(result.filePath, '.refboard');
    doSave(result.filePath);
  });
}

function doSave(fp) {
  try {
    fs.writeFileSync(fp, JSON.stringify({ folders: S.folders }, null, 2));
    S.modified = false;
    projName.textContent = S.projectName;
    toast('Saved ✓');
  } catch (e) { toast('Failed to save'); }
}

// ── Add media ─────────────────────────────────────────────────────────────────
function addMedia() {
  const page = getCurPage();
  if (!page) { toast('Select a page first'); return; }
  ipcRenderer.invoke('dialog:open', {
    title: 'Add Media',
    filters: [{ name: 'Media', extensions: ['png','jpg','jpeg','gif','webp','bmp','svg','mp4','webm','mov','mkv'] }],
    properties: ['openFile', 'multiSelections'],
  }).then(result => {
    if (result.canceled || !result.filePaths.length) return;
    result.filePaths.forEach(fp => {
      page.media.push({ id: uid(), name: nodePath.basename(fp, nodePath.extname(fp)), path: fp, type: mediaType(fp), description: '' });
    });
    markDirty(); renderMediaPanel();
    toast(`Added ${result.filePaths.length} file(s)`);
  });
}

// ── Modal ─────────────────────────────────────────────────────────────────────
let modalCb = null;
function showModal(title, value, okLabel, cb) {
  $('modal-title').textContent = title;
  $('modal-inp').value = value;
  $('modal-ok').textContent = okLabel;
  modalCb = cb;
  modalBg.classList.remove('hidden');
  $('modal-inp').focus();
}
$('modal-cancel').onclick = () => modalBg.classList.add('hidden');
$('modal-ok').onclick = () => {
  const v = $('modal-inp').value.trim();
  if (!v) return;
  modalBg.classList.add('hidden');
  if (modalCb) modalCb(v);
};
$('modal-inp').addEventListener('keydown', e => {
  if (e.key === 'Enter')  $('modal-ok').click();
  if (e.key === 'Escape') $('modal-cancel').click();
});

// ── Titlebar ──────────────────────────────────────────────────────────────────
$('btn-new').onclick    = newProject;
$('btn-open').onclick   = openProject;
$('btn-save').onclick   = saveProject;
$('btn-saveas').onclick = saveAsProject;
$('btn-min').onclick    = () => ipcRenderer.invoke('win:minimize');
$('btn-max').onclick    = () => ipcRenderer.invoke('win:maximize');
$('btn-close').onclick  = () => {
  if (S.modified && !confirm('Discard unsaved changes?')) return;
  ipcRenderer.invoke('win:close');
};

// ── Visibility handling ───────────────────────────────────────────────────────
let wasPlaying = false, wasGifPlaying = false;
document.addEventListener('visibilitychange', () => {
  if (document.hidden) {
    wasPlaying = !vidViewer.paused; wasGifPlaying = V.gifPlaying;
    if (wasPlaying)    vidViewer.pause();
    if (wasGifPlaying) pauseGif();
  } else {
    if (wasPlaying && !vidViewer.classList.contains('hidden'))          vidViewer.play();
    if (wasGifPlaying && V.gifFrames && V.frameMode === 'framebyframe') playGif();
  }
});
window.addEventListener('focus', () => {
  if (!viewerStage.classList.contains('hidden')) applyXform(activeEl());
});

// ── Init ──────────────────────────────────────────────────────────────────────
renderSidebar();
renderMediaPanel();
