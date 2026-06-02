'use strict';
const { app, BrowserWindow, ipcMain, dialog } = require('electron');
const path = require('path');
const fs = require('fs');

let mainWindow = null;

function createWindow() {
  mainWindow = new BrowserWindow({
    width: 1440,
    height: 900,
    minWidth: 1000,
    minHeight: 640,
    frame: false,
    backgroundColor: '#080910',
    webPreferences: {
      nodeIntegration: true,
      contextIsolation: false,
      webSecurity: false,
    },
  });
  mainWindow.loadFile('index.html');
  mainWindow.on('closed', () => { mainWindow = null; });
}

app.whenReady().then(createWindow);
app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') app.quit();
});
app.on('activate', () => {
  if (BrowserWindow.getAllWindows().length === 0) createWindow();
});

// ── IPC handlers ──────────────────────────────────────────────────────────────
ipcMain.handle('dialog:open', async (_, options) => {
  const result = await dialog.showOpenDialog(options);
  return result;
});

ipcMain.handle('dialog:save', async (_, options) => {
  const result = await dialog.showSaveDialog(options);
  return result;
});

ipcMain.handle('dialog:openMedia', async () => {
  const result = await dialog.showOpenDialog({
    properties: ['openFile', 'multiSelections'],
    filters: [{ name: 'Media', extensions: ['jpg','jpeg','png','gif','webp','bmp','mp4','webm','mov','mkv'] }],
  });
  return result.canceled ? [] : result.filePaths;
});

ipcMain.handle('dialog:saveProject', async (_, defaultName) => {
  const result = await dialog.showSaveDialog({
    defaultPath: (defaultName || 'untitled') + '.refboard',
    filters: [{ name: 'RefBoard Project', extensions: ['refboard'] }],
  });
  return result.canceled ? null : result.filePath;
});

ipcMain.handle('dialog:openProject', async () => {
  const result = await dialog.showOpenDialog({
    properties: ['openFile'],
    filters: [{ name: 'RefBoard Project', extensions: ['refboard'] }],
  });
  return result.canceled ? null : result.filePaths[0];
});

ipcMain.handle('fs:write', (_, fp, data) => { fs.writeFileSync(fp, data, 'utf8'); return true; });
ipcMain.handle('fs:read',  (_, fp) => fs.readFileSync(fp, 'utf8'));

ipcMain.handle('win:minimize', () => BrowserWindow.getFocusedWindow()?.minimize());
ipcMain.handle('win:maximize', () => {
  const w = BrowserWindow.getFocusedWindow();
  w?.isMaximized() ? w.unmaximize() : w?.maximize();
});
ipcMain.handle('win:close', () => BrowserWindow.getFocusedWindow()?.close());
