const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.1.1';
const STATE_EPOCH = 3; // Clean v3 account + password + GIFs epoch
const SERVER_BOOT_ID = crypto.randomBytes(6).toString('hex');
const PUBLIC_WEB_URL = process.env.PUBLIC_WEB_URL || 'https://min-chat-qtl0.onrender.com';
const ADMIN_HANDLE = 'kvartsbuen';

function compareVersions(a, b) {
  const pa = String(a || '0').replace(/^v/i, '').split('.').map((n) => parseInt(n, 10) || 0);
  const pb = String(b || '0').replace(/^v/i, '').split('.').map((n) => parseInt(n, 10) || 0);
  for (let i = 0; i < Math.max(pa.length, pb.length); i++) {
    const da = pa[i] || 0;
    const db = pb[i] || 0;
    if (da !== db) return da > db ? 1 : -1;
  }
  return 0;
}
const MAX_CHANNEL_HISTORY = 80;
const MAX_DM_HISTORY = 80;
const MAX_VAULT_MEMORY = 6000;
const MAX_CUSTOM_CHANNELS_PER_USER = 5;
const MAX_FILE_BYTES = 2 * 1024 * 1024; // 2 MB live relay only (never stored!)
const MAX_GIF_FAVORITES = 100;
const DEFAULT_CHANNELS = ['#general-1', '#general-2'];
const ALLOWED_REACTIONS = new Set([
  '👍', '👎', '❤️', '🧡', '💛', '💚', '💙', '💜',
  '🖤', '🤍', '💔', '💖', '😂', '🤣', '😭', '😅',
  '😊', '😍', '🥰', '😎', '🥳', '🤯', '😱', '😮',
  '😢', '😴', '🤔', '🤨', '😏', '🙄', '😬', '🤓',
  '🫠', '🫣', '😈', '😇', '🤡', '👻', '💀', '☠️',
  '👽', '🤖', '💩', '🔥', '✨', '⚡', '💥', '💯',
  '🎉', '🎊', '🏆', '👑', '💎', '👀', '🫡', '🤝',
  '🙏', '👏', '🙌', '💪', '🫶', '✌️', '🤞', '👌',
  '🤙', '🤌', '🧠', '🍿', '🍕', '☕', '🎮', '🎵',
  '🐶', '🐱', '🐸', '🗿', '✅', '❌', '❓', '❗'
]);
const RESERVED_HANDLES = new Set(['system', 'server', 'melding', 'varsel', 'admin', 'moderator']);

// RSA-2048 Public Key (kept strictly as emergency Admin password recovery for @kvartsbuen!)
const DEFAULT_ADMIN_PUBKEY_XML = '<RSAKeyValue><Modulus>uCZ/7WUZF48t94dqjt4OwPJBuJRoauq2QnoO5PnayAP3nk6duqdw2jTZqNW644NucJZtTIyreh/9PXvTKOx3KoPOLFcSnyXOKEN8rtaoWZRlOCyTwxCFj6tGAZXukBj/4NkMQLUcX7xTnI9cJBNdJYIXtfmTF1m0+q9oao1/LIa4GeC7OJ3M/n+nWuviC2J3HdpETYuK/IJrmBMg0g74syTBkVhl8sHY5ePNrFzBAvcJRlQo5Izej5aynHdJPgX9t0HgLBWkw5n7GEQt/ceA93ftaWm5RcXefHpQZWJ3tOKH7sHGD3HKPoWJuuL+9VNOr0n4LEtqKIGvsmLpz/V9XQ==</Modulus><Exponent>AQAB</Exponent></RSAKeyValue>';
const ADMIN_PUBKEY_XML = (process.env.ADMIN_PUBKEY_XML || DEFAULT_ADMIN_PUBKEY_XML).trim();

const DATA_DIR = process.env.DATA_DIR || __dirname;
const STATE_FILE = path.join(DATA_DIR, 'chat_relay_state.json');
const VAULT_FILE = path.join(DATA_DIR, 'chat_relay_vault.jsonl');

function canonicalizeRsaXml(xml) {
  if (typeof xml !== 'string') return null;
  const mod = xml.match(/<Modulus>\s*([^<\s]+)\s*<\/Modulus>/)?.[1];
  const exp = xml.match(/<Exponent>\s*([^<\s]+)\s*<\/Exponent>/)?.[1];
  if (!mod || !exp) return null;
  return `<RSAKeyValue><Modulus>${mod}</Modulus><Exponent>${exp}</Exponent></RSAKeyValue>`;
}

function rsaPublicKeyFromXml(xml) {
  const canon = canonicalizeRsaXml(xml);
  if (!canon) return null;
  const mod = canon.match(/<Modulus>([^<]+)<\/Modulus>/)[1];
  const exp = canon.match(/<Exponent>([^<]+)<\/Exponent>/)[1];
  return {
    canon,
    keyObj: crypto.createPublicKey({
      key: {
        kty: 'RSA',
        n: Buffer.from(mod, 'base64').toString('base64url'),
        e: Buffer.from(exp, 'base64').toString('base64url')
      },
      format: 'jwk'
    })
  };
}

function verifyRsaSha256(xml, textData, sigBase64) {
  try {
    const parsed = rsaPublicKeyFromXml(xml);
    if (!parsed || typeof sigBase64 !== 'string') return null;
    const sigBuf = Buffer.from(sigBase64, 'base64');
    const ok = crypto.verify('sha256', Buffer.from(textData, 'utf8'), parsed.keyObj, sigBuf);
    if (!ok) return null;
    const hashHex = crypto.createHash('sha256').update(parsed.canon, 'utf8').digest('hex').toUpperCase();
    return {
      deviceId: hashHex.slice(0, 16),
      fingerprint: `${hashHex.slice(0, 4)}-${hashHex.slice(4, 8)}`
    };
  } catch {
    return null;
  }
}

function hashPassword(password, salt) {
  const s = salt || crypto.randomBytes(16).toString('hex');
  const hash = crypto.scryptSync(String(password), s, 64).toString('hex');
  return { salt: s, hash };
}

function verifyPassword(password, salt, expectedHash) {
  try {
    if (!password || !salt || !expectedHash) return false;
    const actual = crypto.scryptSync(String(password), String(salt), 64);
    const expected = Buffer.from(String(expectedHash), 'hex');
    if (actual.length !== expected.length) return false;
    return crypto.timingSafeEqual(actual, expected);
  } catch {
    return false;
  }
}

function formatIsoNow() {
  const d = new Date();
  const pad = (n) => String(n).padStart(2, '0');
  return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
}

function formatShortTime() {
  return formatIsoNow().slice(11, 16);
}

function deviceTagFor(deviceId) {
  const clean = String(deviceId || '').toUpperCase().replace(/[^A-F0-9]/g, '');
  return clean ? '#' + clean.slice(0, 4) : '';
}

function sanitizeHandle(raw, allowAdminHandle = false) {
  if (typeof raw !== 'string') return '';
  const cleaned = raw.trim().replace(/^@+/, '').toLowerCase().replace(/[^a-z0-9æøå._-]/g, '').slice(0, 20);
  if (cleaned.length < 3) return '';
  if (/^[._-]|[._-]$|\.\./.test(cleaned)) return '';
  if (!/[a-z0-9æøå]/.test(cleaned)) return '';
  if (RESERVED_HANDLES.has(cleaned)) return '';
  if (!allowAdminHandle && cleaned === ADMIN_HANDLE) return '';
  return cleaned;
}

function validateDisplayName(deviceId, raw, isAdmin = false) {
  const stripped = String(raw || '').replace(/@/g, '').replace(/\s+/g, ' ').trim().slice(0, 24);
  if (!stripped) return { ok: false, error: 'Visningsnavnet kan ikke være tomt.' };
  const norm = stripped.toLowerCase().replace(/[^a-z0-9æøå._-]/g, '');
  if (RESERVED_HANDLES.has(norm)) {
    return { ok: false, error: 'Dette visningsnavnet er reservert.' };
  }
  if (!isAdmin && norm === ADMIN_HANDLE) {
    return { ok: false, error: `Du kan ikke bruke «${stripped}» fordi @${ADMIN_HANDLE} tilhører en annen person.` };
  }
  const handleOwner = state.handleOwners[norm];
  if (handleOwner && handleOwner !== deviceId) {
    return {
      ok: false,
      error: `Du kan ikke bruke «${stripped}» fordi @${norm} er det faste brukernavnet til en annen person.`
    };
  }
  return { ok: true, name: stripped };
}

function sanitizeChannelSlug(raw) {
  let s = String(raw || '').trim().toLowerCase();
  s = s.replace(/^#+/, '').replace(/\s+/g, '-').replace(/[^a-z0-9æøå_-]/g, '').slice(0, 22);
  if (!s) return '';
  return '#' + s;
}

function sanitizeGifObj(gifObj) {
  if (!gifObj || typeof gifObj !== 'object') return null;
  const rawUrl = String(gifObj.url || '').trim().slice(0, 500);
  if (!/^https:\/\/[^\s"'<>]+$/i.test(rawUrl)) return null;
  let parsedUrl;
  try { parsedUrl = new URL(rawUrl); } catch { return null; }
  const host = parsedUrl.hostname.toLowerCase();
  const isKnownGifHost = /(^|\.)(tenor\.com|giphy\.com|klipy\.com|imgur\.com|discordapp\.net|discordapp\.com|wikimedia\.org|redd\.it)$/i.test(host);
  const isGifPath = /\.(gif|webp|mp4)(\?.*)?$/i.test(parsedUrl.pathname);
  if (!isKnownGifHost && !isGifPath) return null;
  const rawPreview = String(gifObj.preview || rawUrl).trim().slice(0, 500);
  const preview = /^https:\/\/[^\s"'<>]+$/i.test(rawPreview) ? rawPreview : rawUrl;
  const title = String(gifObj.title || 'GIF').trim().slice(0, 80) || 'GIF';
  const id = String(gifObj.id || crypto.createHash('sha1').update(rawUrl).digest('hex').slice(0, 12)).slice(0, 48);
  return { id, url: rawUrl, preview, title };
}

function resolveAuthoritativeReply(replyObj, historyList) {
  if (!replyObj || typeof replyObj !== 'object') return null;
  const msgId = String(replyObj.msgId || '').trim().slice(0, 64);
  if (!msgId) return null;
  if (Array.isArray(historyList)) {
    const orig = historyList.find((m) => m.msgId === msgId);
    if (orig) {
      const origDev = orig.deviceId || orig.fromDeviceId || '';
      const fallbackText = orig.gif ? '[GIF]' : (orig.file ? `[Fil: ${orig.file.name}]` : '');
      return {
        msgId: orig.msgId,
        deviceId: origDev,
        user: orig.user || 'Bruker',
        handle: orig.handle || getHandleFor(origDev),
        deviceTag: deviceTagFor(origDev),
        color: orig.color || '#dbdee1',
        text: String(orig.text || fallbackText).trim().slice(0, 140)
      };
    }
  }
  return null;
}

// Validates live file/image attachment for transit ONLY
function sanitizeLiveAttachment(fileObj) {
  if (!fileObj || typeof fileObj !== 'object') return null;
  const data = typeof fileObj.data === 'string' ? fileObj.data : '';
  if (!data || data.length > 3 * 1024 * 1024) return null;
  const name = String(fileObj.name || 'fil').replace(/[<>:"/\\|?*\x00-\x1F]/g, '_').slice(0, 80) || 'fil';
  const size = typeof fileObj.size === 'number' && fileObj.size >= 0
    ? Math.min(MAX_FILE_BYTES, Math.round(fileObj.size))
    : Math.round((data.length * 3) / 4);
  const isImage = !!fileObj.isImage || /\.(png|jpe?g|gif|bmp|webp)$/i.test(name);
  return { name, size, isImage, data };
}

// Strips binary data so server NEVER stores images or file contents — ONLY filename & size!
function stripFileData(fileObj) {
  if (!fileObj) return null;
  return { name: fileObj.name, size: fileObj.size, isImage: !!fileObj.isImage };
}

function dmRoomKey(devA, devB) {
  return [String(devA || ''), String(devB || '')].sort().join('|');
}

const state = {
  epoch: STATE_EPOCH,
  settings: {
    heartbeatEnabled: true,
    heartbeatSec: 30,
    accessMode: 'open', // open | approval | invite | trusted_only
    secretTrustedOnly: false,
    webOnlyMode: true,
    gifApiKey: '' // Optional KLIPY API key (Tenor web search works automatically without any key!)
  },
  updater: {
    latestVersion: SERVER_VERSION,
    minVersion: '3.0.0',
    notes: 'Chat v3.0: Brukernavn + passord med Chrome-lagring, forblir innlogget, Tenor GIFs med søk og favoritter, og 80 reaksjons-emojier!',
    downloadUrl: PUBLIC_WEB_URL,
    driveUrl: PUBLIC_WEB_URL,
    forceModal: false
  },
  announcement: null,
  cooldowns: {
    global: 0,
    channels: {}
  },
  accounts: {},       // accountId -> { accountId, handle, displayName, color, role, passwordSalt, passwordHash, createdAt, firstJoinedMs, lastSeenIso, gifFavorites }
  sessions: {},       // sessionToken -> { accountId, createdAt, lastUsedIso }
  handles: {},        // accountId -> lockedHandle
  handleOwners: {},   // lockedHandle -> accountId
  trustedDevices: {},
  verifiedDevices: {},
  bannedDevices: {},
  mutedDevices: {},
  heartbeatOffDevices: {},
  knownDevices: {},
  invites: {},
  friends: {},
  friendRequests: {},
  customChannels: {}
};

const channelHistory = new Map();
const dmHistory = new Map();
const lastMsgByDeviceChannel = new Map();
const vault = [];
const recoverChallenges = new Map(); // nonce -> expiresAtMs
const gifSearchCache = new Map();    // key -> { expiresAt, payload }
let nextSeq = 1;
let nextConnNum = 1;

function saveState() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8');
  } catch { }
}

function syncKnownDeviceFromAccount(acc, extra = {}) {
  if (!acc || !acc.accountId) return;
  const id = acc.accountId;
  state.handles[id] = acc.handle;
  state.handleOwners[acc.handle] = id;
  const prev = state.knownDevices[id] || {};
  state.knownDevices[id] = {
    deviceId: id,
    fingerprint: `${id.slice(0, 4).toUpperCase()}-${id.slice(4, 8).toUpperCase()}`,
    user: acc.displayName,
    handle: acc.handle,
    clientVersion: extra.clientVersion || prev.clientVersion || SERVER_VERSION,
    color: acc.color || '#3498DB',
    ip: extra.ip || prev.ip || '',
    host: extra.host || prev.host || 'Web',
    lastChannel: extra.lastChannel || prev.lastChannel || '#general-1',
    firstJoinedMs: acc.firstJoinedMs || Date.now(),
    lastSeenIso: acc.lastSeenIso || formatIsoNow()
  };
}

function publicAccountSummary(acc) {
  if (!acc) return null;
  return {
    accountId: acc.accountId,
    deviceTag: deviceTagFor(acc.accountId),
    handle: acc.handle,
    user: acc.displayName,
    color: acc.color || '#3498DB',
    role: acc.handle === ADMIN_HANDLE ? 'admin' : (acc.role || 'verified'),
    gifFavorites: Array.isArray(acc.gifFavorites) ? acc.gifFavorites : [],
    createdAt: acc.createdAt || ''
  };
}

function createAccount({ handle, displayName, password, color, role = 'verified' }) {
  const accountId = crypto.randomBytes(8).toString('hex');
  const { salt, hash } = hashPassword(password);
  const nowIso = formatIsoNow();
  const nowMs = Date.now();
  const finalRole = handle === ADMIN_HANDLE ? 'admin' : role;
  const acc = {
    accountId,
    handle,
    displayName: displayName || handle,
    color: /^#[0-9A-Fa-f]{6}$/.test(color) ? color : '#3498DB',
    role: finalRole,
    passwordSalt: salt,
    passwordHash: hash,
    createdAt: nowIso,
    firstJoinedMs: nowMs,
    lastSeenIso: nowIso,
    gifFavorites: []
  };
  state.accounts[accountId] = acc;
  if (finalRole === 'admin' || finalRole === 'trusted') {
    state.trustedDevices[accountId] = { deviceId: accountId, fingerprint: deviceTagFor(accountId), user: acc.displayName, addedAt: nowIso };
  } else {
    state.verifiedDevices[accountId] = { deviceId: accountId, fingerprint: deviceTagFor(accountId), user: acc.displayName, addedAt: nowIso };
  }
  syncKnownDeviceFromAccount(acc);
  saveState();
  return acc;
}

function createSession(accountId) {
  const token = crypto.randomBytes(32).toString('hex');
  const now = formatIsoNow();
  state.sessions[token] = { accountId, createdAt: now, lastUsedIso: now };
  saveState();
  return token;
}

function getSessionAccount(token) {
  const t = String(token || '').trim();
  if (!t || !state.sessions[t]) return null;
  const sess = state.sessions[t];
  const acc = state.accounts[sess.accountId];
  if (!acc) {
    delete state.sessions[t];
    return null;
  }
  sess.lastUsedIso = formatIsoNow();
  return { token: t, session: sess, account: acc };
}

// Load saved state ONLY if it matches STATE_EPOCH === 3; otherwise start 100% clean!
try {
  let loadedEpochOk = false;
  if (fs.existsSync(STATE_FILE)) {
    const saved = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    if (saved && saved.epoch === STATE_EPOCH) {
      loadedEpochOk = true;
      if (saved.settings) Object.assign(state.settings, saved.settings);
      if (saved.updater) Object.assign(state.updater, saved.updater);
      if (saved.announcement !== undefined) state.announcement = saved.announcement;
      if (saved.cooldowns) {
        state.cooldowns.global = Number(saved.cooldowns.global) || 0;
        if (saved.cooldowns.channels) Object.assign(state.cooldowns.channels, saved.cooldowns.channels);
      }
      if (saved.accounts) Object.assign(state.accounts, saved.accounts);
      if (saved.sessions) Object.assign(state.sessions, saved.sessions);
      if (saved.handles) Object.assign(state.handles, saved.handles);
      if (saved.handleOwners) Object.assign(state.handleOwners, saved.handleOwners);
      if (saved.trustedDevices) Object.assign(state.trustedDevices, saved.trustedDevices);
      if (saved.verifiedDevices) Object.assign(state.verifiedDevices, saved.verifiedDevices);
      if (saved.bannedDevices) Object.assign(state.bannedDevices, saved.bannedDevices);
      if (saved.mutedDevices) Object.assign(state.mutedDevices, saved.mutedDevices);
      if (saved.heartbeatOffDevices) Object.assign(state.heartbeatOffDevices, saved.heartbeatOffDevices);
      if (saved.knownDevices) Object.assign(state.knownDevices, saved.knownDevices);
      if (saved.invites) Object.assign(state.invites, saved.invites);
      if (saved.friends) Object.assign(state.friends, saved.friends);
      if (saved.friendRequests) Object.assign(state.friendRequests, saved.friendRequests);
      if (saved.customChannels) Object.assign(state.customChannels, saved.customChannels);
    } else {
      // Wipe legacy pre-v3 state & vault cleanly!
      try { fs.unlinkSync(STATE_FILE); } catch { }
      try { fs.unlinkSync(VAULT_FILE); } catch { }
    }
  }
  if (loadedEpochOk && fs.existsSync(VAULT_FILE)) {
    const lines = fs.readFileSync(VAULT_FILE, 'utf8').split(/\r?\n/).filter(Boolean);
    for (const line of lines.slice(-MAX_VAULT_MEMORY)) {
      try {
        const rec = JSON.parse(line);
        if (rec.file && rec.file.data) delete rec.file.data;
        vault.push(rec);
        if (typeof rec.seq === 'number' && rec.seq >= nextSeq) nextSeq = rec.seq + 1;
        if (rec.type === 'chat' && rec.channel) {
          const arr = channelHistory.get(rec.channel) || [];
          arr.push(rec);
          if (arr.length > MAX_CHANNEL_HISTORY) arr.shift();
          channelHistory.set(rec.channel, arr);
        } else if (rec.type === 'dm' && rec.fromDeviceId && rec.toDeviceId) {
          const rk = dmRoomKey(rec.fromDeviceId, rec.toDeviceId);
          const arr = dmHistory.get(rk) || [];
          arr.push(rec);
          if (arr.length > MAX_DM_HISTORY) arr.shift();
          dmHistory.set(rk, arr);
        } else if (rec.type === 'delete' && rec.msgId) {
          if (rec.scope === 'channel' && rec.channel) {
            const arr = channelHistory.get(rec.channel) || [];
            channelHistory.set(rec.channel, arr.filter((m) => m.msgId !== rec.msgId));
          } else if (rec.scope === 'dm') {
            for (const [rk, arr] of dmHistory.entries()) {
              dmHistory.set(rk, arr.filter((m) => m.msgId !== rec.msgId));
            }
          }
        } else if (rec.type === 'edit' && rec.msgId && rec.scope === 'channel' && rec.channel) {
          const arr = channelHistory.get(rec.channel) || [];
          const found = arr.find((m) => m.msgId === rec.msgId);
          if (found) {
            found.text = rec.text;
            found.edited = true;
            found.editedAt = rec.time;
          }
        }
      } catch { }
    }
  }
} catch { }

// Optional Render env var: pre-seed @kvartsbuen with ADMIN_PASSWORD if configured
if (process.env.ADMIN_PASSWORD && process.env.ADMIN_PASSWORD.length >= 6 && !state.handleOwners[ADMIN_HANDLE]) {
  createAccount({
    handle: ADMIN_HANDLE,
    displayName: 'Kvartsbuen',
    password: process.env.ADMIN_PASSWORD,
    color: '#2ECC71',
    role: 'admin'
  });
}

function appendVaultRecord(rec) {
  const metaRec = rec.file ? { ...rec, file: stripFileData(rec.file) } : rec;
  vault.push(metaRec);
  if (vault.length > MAX_VAULT_MEMORY) vault.shift();
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    fs.appendFileSync(VAULT_FILE, JSON.stringify(metaRec) + '\n', 'utf8');
  } catch { }
  sendToAdmins({ type: 'admin_log', record: metaRec });
}

function rewriteVaultFile() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const content = vault.length ? vault.map((r) => JSON.stringify(r)).join('\n') + '\n' : '';
    fs.writeFileSync(VAULT_FILE, content, 'utf8');
  } catch { }
}

// =============================================================================
// HTTP Helpers (Cookies, JSON Body, Tenor/Klipy GIF Search Proxy)
// =============================================================================
function parseCookies(req) {
  const out = {};
  const raw = String(req.headers.cookie || '');
  for (const part of raw.split(';')) {
    const idx = part.indexOf('=');
    if (idx === -1) continue;
    const k = part.slice(0, idx).trim();
    const v = part.slice(idx + 1).trim();
    if (k) {
      try { out[k] = decodeURIComponent(v); } catch { out[k] = v; }
    }
  }
  return out;
}

function extractRequestToken(req) {
  const auth = String(req.headers.authorization || '');
  if (auth.startsWith('Bearer ')) return auth.slice(7).trim();
  const cookies = parseCookies(req);
  return cookies.chat_session || '';
}

function setSessionCookie(req, res, token) {
  const isHttps = req.headers['x-forwarded-proto'] === 'https' || req.socket.encrypted;
  const parts = [
    `chat_session=${encodeURIComponent(token)}`,
    'Path=/',
    'HttpOnly',
    'SameSite=Lax',
    'Max-Age=31536000'
  ];
  if (isHttps) parts.push('Secure');
  res.setHeader('Set-Cookie', parts.join('; '));
}

function clearSessionCookie(res) {
  res.setHeader('Set-Cookie', 'chat_session=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0');
}

function sendJsonRes(res, statusCode, obj) {
  res.writeHead(statusCode, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store'
  });
  res.end(JSON.stringify(obj));
}

function readJsonBody(req, maxBytes = 65536) {
  return new Promise((resolve) => {
    let size = 0;
    const chunks = [];
    req.on('data', (c) => {
      size += c.length;
      if (size <= maxBytes) chunks.push(c);
    });
    req.on('end', () => {
      try {
        const raw = Buffer.concat(chunks).toString('utf8');
        resolve(raw ? JSON.parse(raw) : {});
      } catch {
        resolve(null);
      }
    });
    req.on('error', () => resolve(null));
  });
}

function httpsGetText(targetUrl, redirects = 3) {
  return new Promise((resolve, reject) => {
    const req = https.get(targetUrl, {
      headers: {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36',
        'Accept-Language': 'en-US,en;q=0.9,nb;q=0.8',
        'Accept': 'text/html,application/json;q=0.9,*/*;q=0.8'
      },
      timeout: 7000
    }, (res) => {
      if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location && redirects > 0) {
        const nextUrl = new URL(res.headers.location, targetUrl).toString();
        res.resume();
        httpsGetText(nextUrl, redirects - 1).then(resolve, reject);
        return;
      }
      if (res.statusCode >= 400) {
        res.resume();
        reject(new Error('HTTP ' + res.statusCode));
        return;
      }
      const chunks = [];
      let total = 0;
      res.on('data', (c) => {
        total += c.length;
        if (total < 1.5 * 1024 * 1024) chunks.push(c);
      });
      res.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    });
    req.on('timeout', () => { req.destroy(); reject(new Error('Timeout')); });
    req.on('error', reject);
  });
}

async function searchTenorOrKlipyGifs(rawQuery) {
  const q = String(rawQuery || '').trim().slice(0, 60);
  const cacheKey = q.toLowerCase() || '__trending__';
  const cached = gifSearchCache.get(cacheKey);
  if (cached && cached.expiresAt > Date.now()) return cached.payload;

  const klipyKey = (process.env.KLIPY_API_KEY || state.settings.gifApiKey || '').trim();
  let results = [];
  let provider = 'tenor';

  // 1. Optional KLIPY Tenor-compatible v2 API if key is configured
  if (klipyKey) {
    try {
      const apiUrl = q
        ? `https://api.klipy.com/v2/search?q=${encodeURIComponent(q)}&key=${encodeURIComponent(klipyKey)}&limit=24&media_filter=gif,tinygif`
        : `https://api.klipy.com/v2/featured?key=${encodeURIComponent(klipyKey)}&limit=24&media_filter=gif,tinygif`;
      const txt = await httpsGetText(apiUrl);
      const data = JSON.parse(txt);
      const list = Array.isArray(data.results) ? data.results : [];
      for (const item of list) {
        const mf = item.media_formats || {};
        const full = (mf.gif && mf.gif.url) || (mf.mediumgif && mf.mediumgif.url) || (mf.tinygif && mf.tinygif.url) || '';
        const prev = (mf.tinygif && mf.tinygif.url) || (mf.nanogif && mf.nanogif.url) || full;
        if (full) {
          results.push({
            id: String(item.id || crypto.createHash('sha1').update(full).digest('hex').slice(0, 10)),
            title: String(item.content_description || item.title || q || 'GIF').slice(0, 60),
            preview: prev,
            url: full
          });
        }
      }
      if (results.length) provider = 'klipy';
    } catch { }
  }

  // 2. Zero-config Tenor web search (works out of the box with NO API key!)
  if (!results.length) {
    try {
      const slug = q.toLowerCase().replace(/[^a-z0-9æøå]+/g, '-').replace(/^-+|-+$/g, '');
      const tenorUrl = slug
        ? `https://tenor.com/search/${encodeURIComponent(slug)}-gifs`
        : 'https://tenor.com/en-GB/';
      const html = await httpsGetText(tenorUrl);
      const normalized = html.replace(/\\u002F/gi, '/').replace(/\\\//g, '/');
      const urlRe = /https:\/\/media[0-9]?\.tenor\.com\/(?:m\/)?([A-Za-z0-9_-]{8,30})\/([A-Za-z0-9_.-]+\.gif)/gi;
      const seenMap = new Map();
      let m;
      while ((m = urlRe.exec(normalized)) !== null && results.length < 24) {
        const fullUrl = m[0];
        const gifId = m[1];
        const baseId = gifId.replace(/AAAA[A-Za-z0-9_-]$/, '');
        const fileSlug = m[2].replace(/\.gif$/i, '').replace(/[-_]+/g, ' ').trim();
        const existing = seenMap.get(baseId);
        if (existing) {
          if (/AAAAM$/i.test(gifId)) existing.preview = fullUrl;
          else if (/AAAAC$/i.test(gifId)) existing.url = fullUrl;
          continue;
        }
        const entry = {
          id: gifId,
          title: (fileSlug || q || 'Tenor GIF').slice(0, 60),
          preview: fullUrl,
          url: fullUrl
        };
        seenMap.set(baseId, entry);
        results.push(entry);
      }
      provider = 'tenor';
    } catch { }
  }

  const payload = { ok: true, provider, query: q, results };
  if (results.length > 0) {
    if (gifSearchCache.size > 100) gifSearchCache.clear();
    gifSearchCache.set(cacheKey, { expiresAt: Date.now() + 5 * 60 * 1000, payload });
  }
  return payload;
}

// Embedded gzipped Chat.html v2 (auto-populated by build script)
const WEB_CLIENT_HTML_GZIP_B64 = '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';
let WEB_CLIENT_HTML = Buffer.from('<!doctype html><html><body><h1>Chat v2.2</h1></body></html>', 'utf8');
try {
  if (WEB_CLIENT_HTML_GZIP_B64 && !WEB_CLIENT_HTML_GZIP_B64.startsWith('__EMBEDDED')) {
    WEB_CLIENT_HTML = zlib.gunzipSync(Buffer.from(WEB_CLIENT_HTML_GZIP_B64, 'base64'));
  }
} catch { }

// Server-delivered Admin UI bundle (sent ONLY over WebSocket after RSA-2048 adminSig verification!)
const ADMIN_BUNDLE_GZIP_B64 = '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';
let ADMIN_BUNDLE_OBJ = null;
try {
  if (ADMIN_BUNDLE_GZIP_B64 && !ADMIN_BUNDLE_GZIP_B64.startsWith('__EMBEDDED')) {
    ADMIN_BUNDLE_OBJ = JSON.parse(zlib.gunzipSync(Buffer.from(ADMIN_BUNDLE_GZIP_B64, 'base64')).toString('utf8'));
  }
} catch { }

const server = http.createServer(async (req, res) => {
  const parsedUrl = new URL(req.url || '/', 'http://localhost');
  const reqPath = parsedUrl.pathname;

  if (reqPath === '/health' || reqPath === '/status') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end(`Chat Smart Relay v${SERVER_VERSION} OK\n`);
    return;
  }

  if (reqPath === '/manifest.json') {
    res.writeHead(200, { 'Content-Type': 'application/manifest+json; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify({
      name: 'Chat',
      short_name: 'Chat',
      start_url: '/',
      display: 'standalone',
      background_color: '#1e1f22',
      theme_color: '#1e1f22'
    }));
    return;
  }

  if (reqPath === '/version.json') {
    res.writeHead(200, {
      'Content-Type': 'application/json; charset=utf-8',
      'Cache-Control': 'no-store',
      'Access-Control-Allow-Origin': '*'
    });
    res.end(JSON.stringify({
      serverVersion: SERVER_VERSION,
      serverBootId: SERVER_BOOT_ID,
      ...state.updater,
      announcement: state.announcement
    }));
    return;
  }

  // --- Auth API (Chrome Password Manager + Persistent Cookie Sessions!) ---
  if (reqPath === '/api/auth/me' && req.method === 'GET') {
    const found = getSessionAccount(extractRequestToken(req));
    if (!found) {
      sendJsonRes(res, 200, {
        ok: false,
        adminClaimed: !!state.handleOwners[ADMIN_HANDLE],
        accessMode: state.settings.accessMode
      });
      return;
    }
    if (state.bannedDevices[found.account.accountId] && found.account.handle !== ADMIN_HANDLE) {
      clearSessionCookie(res);
      sendJsonRes(res, 403, { ok: false, banned: true, error: 'Denne kontoen er utestengt.' });
      return;
    }
    sendJsonRes(res, 200, {
      ok: true,
      token: found.token,
      account: publicAccountSummary(found.account)
    });
    return;
  }

  if (reqPath === '/api/auth/register' && req.method === 'POST') {
    const body = await readJsonBody(req);
    if (!body) { sendJsonRes(res, 400, { ok: false, error: 'Ugyldig forespørsel.' }); return; }

    const handle = sanitizeHandle(body.username, true);
    if (!handle) {
      sendJsonRes(res, 400, { ok: false, error: 'Ugyldig brukernavn (må være 3–20 tegn: bokstaver, tall, . _ -).' });
      return;
    }
    const password = String(body.password || '');
    if (password.length < 6 || password.length > 128) {
      sendJsonRes(res, 400, { ok: false, error: 'Passordet må være minst 6 tegn.' });
      return;
    }
    if (state.handleOwners[handle]) {
      sendJsonRes(res, 409, { ok: false, error: `Brukernavnet @${handle} er allerede i bruk. Logg inn isteden!` });
      return;
    }

    const isAdminClaim = handle === ADMIN_HANDLE;
    let role = isAdminClaim ? 'admin' : 'verified';

    if (!isAdminClaim && state.settings.accessMode === 'trusted_only') {
      sendJsonRes(res, 403, { ok: false, error: 'Registrering er midlertidig stengt.' });
      return;
    }
    if (!isAdminClaim && state.settings.accessMode === 'invite') {
      const code = String(body.inviteCode || '').trim().toUpperCase();
      const inv = code && state.invites[code];
      if (!inv || inv.usesLeft <= 0) {
        sendJsonRes(res, 403, { ok: false, error: 'Du trenger en gyldig invitasjonskode for å registrere deg.' });
        return;
      }
      inv.usesLeft -= 1;
      if (inv.usesLeft <= 0) delete state.invites[code];
      if (inv.autoTrust) role = 'trusted';
    }

    const rawDisp = String(body.displayName || '').trim() || (isAdminClaim ? 'Kvartsbuen' : handle);
    const dispCheck = validateDisplayName('', rawDisp, isAdminClaim);
    if (!dispCheck.ok) {
      sendJsonRes(res, 400, { ok: false, error: dispCheck.error });
      return;
    }

    const acc = createAccount({
      handle,
      displayName: dispCheck.name,
      password,
      color: body.color,
      role
    });
    const token = createSession(acc.accountId);
    setSessionCookie(req, res, token);
    broadcastSocialStates();
    broadcastAdminState();
    sendJsonRes(res, 200, {
      ok: true,
      token,
      account: publicAccountSummary(acc)
    });
    return;
  }

  if (reqPath === '/api/auth/login' && req.method === 'POST') {
    const body = await readJsonBody(req);
    if (!body) { sendJsonRes(res, 400, { ok: false, error: 'Ugyldig forespørsel.' }); return; }

    const handle = String(body.username || '').trim().replace(/^@+/, '').toLowerCase();
    const password = String(body.password || '');
    const accId = state.handleOwners[handle];
    const acc = accId ? state.accounts[accId] : null;
    if (!acc || !verifyPassword(password, acc.passwordSalt, acc.passwordHash)) {
      sendJsonRes(res, 401, { ok: false, error: 'Feil brukernavn eller passord.' });
      return;
    }
    if (state.bannedDevices[acc.accountId] && acc.handle !== ADMIN_HANDLE) {
      sendJsonRes(res, 403, { ok: false, error: 'Denne kontoen er utestengt.' });
      return;
    }
    const token = createSession(acc.accountId);
    setSessionCookie(req, res, token);
    sendJsonRes(res, 200, {
      ok: true,
      token,
      account: publicAccountSummary(acc)
    });
    return;
  }

  if (reqPath === '/api/auth/logout' && req.method === 'POST') {
    const body = await readJsonBody(req);
    const token = (body && body.token) || extractRequestToken(req);
    if (token && state.sessions[token]) {
      delete state.sessions[token];
      saveState();
    }
    clearSessionCookie(res);
    sendJsonRes(res, 200, { ok: true });
    return;
  }

  if (reqPath === '/api/auth/change-password' && req.method === 'POST') {
    const body = await readJsonBody(req);
    const found = getSessionAccount((body && body.token) || extractRequestToken(req));
    if (!found) { sendJsonRes(res, 401, { ok: false, error: 'Ikke innlogget.' }); return; }
    const cur = String(body.currentPassword || '');
    const next = String(body.newPassword || '');
    if (!verifyPassword(cur, found.account.passwordSalt, found.account.passwordHash)) {
      sendJsonRes(res, 400, { ok: false, error: 'Nåværende passord er feil.' });
      return;
    }
    if (next.length < 6 || next.length > 128) {
      sendJsonRes(res, 400, { ok: false, error: 'Nytt passord må være minst 6 tegn.' });
      return;
    }
    const { salt, hash } = hashPassword(next);
    found.account.passwordSalt = salt;
    found.account.passwordHash = hash;
    saveState();
    sendJsonRes(res, 200, { ok: true });
    return;
  }

  // Emergency RSA recovery for @kvartsbuen (if password ever forgotten!)
  if (reqPath === '/api/auth/recover-challenge' && req.method === 'GET') {
    const nonce = crypto.randomBytes(24).toString('hex');
    recoverChallenges.set(nonce, Date.now() + 5 * 60 * 1000);
    if (recoverChallenges.size > 50) {
      const now = Date.now();
      for (const [k, exp] of recoverChallenges.entries()) if (exp < now) recoverChallenges.delete(k);
    }
    sendJsonRes(res, 200, { ok: true, nonce });
    return;
  }

  if (reqPath === '/api/auth/admin-recover' && req.method === 'POST') {
    const body = await readJsonBody(req);
    if (!body || !body.nonce || !body.sig || !body.newPassword) {
      sendJsonRes(res, 400, { ok: false, error: 'Mangler nøkkel-signatur eller nytt passord.' });
      return;
    }
    const exp = recoverChallenges.get(body.nonce);
    recoverChallenges.delete(body.nonce);
    if (!exp || exp < Date.now()) {
      sendJsonRes(res, 400, { ok: false, error: 'Utløpt forespørsel. Prøv igjen.' });
      return;
    }
    const ok = verifyRsaSha256(ADMIN_PUBKEY_XML, `RECOVER:${body.nonce}`, body.sig);
    if (!ok) {
      sendJsonRes(res, 403, { ok: false, error: 'Ugyldig privat nøkkel.' });
      return;
    }
    const newPassword = String(body.newPassword);
    if (newPassword.length < 6 || newPassword.length > 128) {
      sendJsonRes(res, 400, { ok: false, error: 'Passordet må være minst 6 tegn.' });
      return;
    }
    let accId = state.handleOwners[ADMIN_HANDLE];
    let acc = accId ? state.accounts[accId] : null;
    if (!acc) {
      acc = createAccount({
        handle: ADMIN_HANDLE,
        displayName: 'Kvartsbuen',
        password: newPassword,
        color: '#2ECC71',
        role: 'admin'
      });
    } else {
      const { salt, hash } = hashPassword(newPassword);
      acc.passwordSalt = salt;
      acc.passwordHash = hash;
      acc.role = 'admin';
      for (const [tk, s] of Object.entries(state.sessions)) {
        if (s.accountId === acc.accountId) delete state.sessions[tk];
      }
      saveState();
    }
    const token = createSession(acc.accountId);
    setSessionCookie(req, res, token);
    sendJsonRes(res, 200, { ok: true, token, account: publicAccountSummary(acc) });
    return;
  }

  // --- Tenor / Klipy GIF Search Proxy ---
  if (reqPath === '/api/gifs' && req.method === 'GET') {
    const q = parsedUrl.searchParams.get('q') || '';
    const data = await searchTenorOrKlipyGifs(q);
    sendJsonRes(res, 200, data);
    return;
  }

  if (reqPath === '/download' || reqPath === '/Chat.html' || reqPath === '/Chat-v2.html') {
    res.writeHead(200, {
      'Content-Type': 'text/html; charset=utf-8',
      'Content-Disposition': `attachment; filename="Chat-v${SERVER_VERSION}.html"`,
      'Cache-Control': 'no-store',
      'Access-Control-Allow-Origin': '*'
    });
    res.end(WEB_CLIENT_HTML);
    return;
  }

  if (reqPath === '/' || reqPath === '/index.html') {
    res.writeHead(200, {
      'Content-Type': 'text/html; charset=utf-8',
      'Cache-Control': 'no-store'
    });
    res.end(WEB_CLIENT_HTML);
    return;
  }

  res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end('Not found\n');
});

const wss = new WebSocketServer({ server, maxPayload: 4 * 1024 * 1024 });

function safeSend(ws, obj) {
  if (ws.readyState === WebSocket.OPEN) {
    try { ws.send(typeof obj === 'string' ? obj : JSON.stringify(obj)); } catch { }
  }
}

function sendToAdmins(obj) {
  const payload = JSON.stringify(obj);
  for (const c of wss.clients) {
    if (c.meta && c.meta.role === 'admin' && c.meta.adminUnlocked === true && c.meta.status === 'approved') {
      safeSend(c, payload);
    }
  }
}

function broadcastToAllApproved(obj) {
  const payload = JSON.stringify(obj);
  for (const c of wss.clients) {
    if (c.meta && c.meta.status === 'approved') {
      safeSend(c, payload);
    }
  }
}

// Mask admin role so non-admins NEVER see any difference between admin and a normal user!
function publicRoleFor(role, viewerIsAdmin) {
  if (viewerIsAdmin) return role;
  return role === 'admin' ? 'verified' : role;
}

function canAccessChannel(meta, channel) {
  if (!meta || meta.status !== 'approved') return false;
  if (DEFAULT_CHANNELS.includes(channel)) return true;
  const custom = state.customChannels[channel];
  if (!custom) return false;
  // Admin can silently access/read all custom channels without ever being listed as a member
  if (meta.role === 'admin') return true;
  if (custom.ownerDeviceId === meta.deviceId) return true;
  return Array.isArray(custom.members) && custom.members.includes(meta.deviceId);
}

function effectiveHeartbeatFor(deviceId) {
  if (!state.settings.heartbeatEnabled) return false;
  if (deviceId && state.heartbeatOffDevices[deviceId]) return false;
  return true;
}

function effectiveCooldownSec(channel) {
  const g = Math.max(0, Number(state.cooldowns.global) || 0);
  const c = Math.max(0, Number((state.cooldowns.channels && state.cooldowns.channels[channel]) || 0));
  return Math.max(g, c);
}

function pushConfigToClient(ws) {
  if (!ws.meta) return;
  safeSend(ws, {
    type: 'config_push',
    heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
    globalHeartbeatEnabled: state.settings.heartbeatEnabled,
    heartbeatSec: state.settings.heartbeatSec,
    accessMode: state.settings.accessMode,
    role: ws.meta.role,
    status: ws.meta.status,
    muted: !!(ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId]),
    fingerprint: ws.meta.fingerprint || '',
    handle: ws.meta.handle || '',
    cooldowns: state.cooldowns,
    updater: state.updater,
    announcement: state.announcement
  });
}

function broadcastUpdaterAndAnnouncement() {
  const payload = {
    type: 'updater_push',
    serverVersion: SERVER_VERSION,
    updater: state.updater,
    announcement: state.announcement
  };
  for (const c of wss.clients) {
    safeSend(c, payload);
  }
}

function broadcastCooldowns() {
  broadcastToAllApproved({
    type: 'cooldown_update',
    cooldowns: state.cooldowns
  });
}

function getOnlineByDevice() {
  const map = new Map();
  for (const c of wss.clients) {
    if (c.meta && c.meta.status === 'approved' && c.meta.deviceId) {
      map.set(c.meta.deviceId, c.meta);
    }
  }
  return map;
}

function getDisplayName(deviceId, onlineMap) {
  if (onlineMap && onlineMap.has(deviceId)) return onlineMap.get(deviceId).user;
  if (state.knownDevices[deviceId] && state.knownDevices[deviceId].user) return state.knownDevices[deviceId].user;
  return 'Bruker';
}

function getHandleFor(deviceId, onlineMap) {
  if (state.handles[deviceId]) return state.handles[deviceId];
  if (onlineMap && onlineMap.has(deviceId) && onlineMap.get(deviceId).handle) return onlineMap.get(deviceId).handle;
  if (state.knownDevices[deviceId] && state.knownDevices[deviceId].handle) return state.knownDevices[deviceId].handle;
  return '';
}

function resolveUserDeviceId(query, excludeDeviceId) {
  const raw = String(query || '').trim();
  if (!raw) return '';
  // Direct deviceId match
  if (state.knownDevices[raw] && raw !== excludeDeviceId) return raw;
  // Exact @handle match (highest priority!)
  const cleanHandle = raw.replace(/^@+/, '').toLowerCase();
  if (state.handleOwners[cleanHandle] && state.handleOwners[cleanHandle] !== excludeDeviceId) {
    return state.handleOwners[cleanHandle];
  }
  const lower = raw.toLowerCase();
  // Online display name match
  for (const c of wss.clients) {
    if (c.meta && c.meta.status === 'approved' && c.meta.deviceId !== excludeDeviceId) {
      if (String(c.meta.user || '').toLowerCase() === lower) return c.meta.deviceId;
    }
  }
  // Known devices display name match
  for (const [dId, kn] of Object.entries(state.knownDevices)) {
    if (dId !== excludeDeviceId && String(kn.user || '').toLowerCase() === lower) return dId;
  }
  return '';
}

function sendSocialState(ws) {
  if (!ws.meta || ws.meta.status !== 'approved' || !ws.meta.deviceId) return;
  const myId = ws.meta.deviceId;
  const isAdmin = ws.meta.role === 'admin';
  const onlineMap = getOnlineByDevice();
  const myFriends = Array.isArray(state.friends[myId]) ? state.friends[myId] : [];
  const myReqs = (Array.isArray(state.friendRequests[myId]) ? state.friendRequests[myId] : []).map((r) => ({
    ...r,
    fromUser: getDisplayName(r.fromDeviceId, onlineMap) || r.fromUser,
    fromHandle: getHandleFor(r.fromDeviceId, onlineMap) || r.fromHandle || ''
  }));

  const users = [];
  const seen = new Set();
  for (const [devId, m] of onlineMap.entries()) {
    seen.add(devId);
    users.push({
      deviceId: devId,
      deviceTag: deviceTagFor(devId),
      user: m.user,
      handle: getHandleFor(devId, onlineMap),
      color: m.color,
      role: publicRoleFor(m.role, isAdmin),
      online: true
    });
  }
  for (const fId of myFriends) {
    if (seen.has(fId)) continue;
    const kn = state.knownDevices[fId];
    if (kn) {
      seen.add(fId);
      users.push({
        deviceId: fId,
        deviceTag: deviceTagFor(fId),
        user: kn.user || 'Venn',
        handle: getHandleFor(fId, onlineMap),
        color: kn.color || '#949BA4',
        role: 'verified',
        online: false
      });
    }
  }

  // Visible custom channels for this user (ONLY ones they own or were invited to — NEVER leak other private channels to non-admins!)
  const visibleChannels = [];
  for (const ch of Object.values(state.customChannels)) {
    const isOwner = ch.ownerDeviceId === myId;
    const isMember = Array.isArray(ch.members) && ch.members.includes(myId);
    if (isOwner || isMember) {
      visibleChannels.push({
        name: ch.name,
        ownerDeviceId: ch.ownerDeviceId,
        ownerName: getDisplayName(ch.ownerDeviceId, onlineMap),
        ownerHandle: getHandleFor(ch.ownerDeviceId, onlineMap),
        isOwner,
        members: (ch.members || []).map((id) => ({
          deviceId: id,
          deviceTag: deviceTagFor(id),
          user: getDisplayName(id, onlineMap),
          handle: getHandleFor(id, onlineMap)
        }))
      });
    }
  }

  safeSend(ws, {
    type: 'social_state',
    myDeviceId: myId,
    myDeviceTag: deviceTagFor(myId),
    myHandle: getHandleFor(myId, onlineMap),
    users,
    friends: myFriends,
    requests: myReqs,
    customChannels: visibleChannels,
    cooldowns: state.cooldowns
  });
}

function broadcastSocialStates() {
  for (const c of wss.clients) {
    if (c.meta && c.meta.status === 'approved' && c.meta.deviceId) {
      sendSocialState(c);
    }
  }
}

function clearTypingFor(ws) {
  if (!ws || !ws.meta || !ws.meta.typingTarget) return;
  const prev = ws.meta.typingTarget;
  ws.meta.typingTarget = null;
  if (prev.scope === 'dm' && prev.toDeviceId) {
    for (const c of wss.clients) {
      if (c.meta && c.meta.status === 'approved' && c.meta.deviceId === prev.toDeviceId) {
        safeSend(c, {
          type: 'typing',
          scope: 'dm',
          fromDeviceId: ws.meta.deviceId,
          user: ws.meta.user,
          handle: ws.meta.handle || '',
          active: false
        });
      }
    }
  } else if (prev.scope === 'channel' && prev.channel) {
    for (const c of wss.clients) {
      if (c === ws || !c.meta || c.meta.status !== 'approved') continue;
      if (!canAccessChannel(c.meta, prev.channel)) continue;
      safeSend(c, {
        type: 'typing',
        scope: 'channel',
        channel: prev.channel,
        fromDeviceId: ws.meta.deviceId,
        user: ws.meta.user,
        handle: ws.meta.handle || '',
        active: false
      });
    }
  }
}

function formatChatPayload(m, viewerIsAdmin, liveFile) {
  return {
    type: 'chat',
    msgId: m.msgId,
    channel: m.channel,
    user: m.user,
    handle: m.handle || getHandleFor(m.deviceId),
    deviceTag: m.deviceTag || deviceTagFor(m.deviceId),
    color: m.color,
    role: publicRoleFor(m.role, viewerIsAdmin),
    deviceId: m.deviceId || '',
    text: m.text,
    edited: !!m.edited,
    editedAt: m.editedAt || '',
    replyTo: m.replyTo || null,
    reactions: m.reactions || {},
    gif: m.gif || null,
    file: liveFile !== undefined ? liveFile : (m.file ? stripFileData(m.file) : null),
    time: m.time,
    isoTime: m.isoTime
  };
}

function formatDmPayload(m, viewerIsAdmin, liveFile) {
  return {
    type: 'dm',
    msgId: m.msgId,
    fromDeviceId: m.fromDeviceId,
    toDeviceId: m.toDeviceId,
    user: m.user,
    handle: m.handle || getHandleFor(m.fromDeviceId),
    deviceTag: m.deviceTag || deviceTagFor(m.fromDeviceId),
    color: m.color,
    role: publicRoleFor(m.role, viewerIsAdmin),
    text: m.text,
    edited: !!m.edited,
    editedAt: m.editedAt || '',
    replyTo: m.replyTo || null,
    reactions: m.reactions || {},
    gif: m.gif || null,
    file: liveFile !== undefined ? liveFile : (m.file ? stripFileData(m.file) : null),
    time: m.time,
    isoTime: m.isoTime
  };
}

function replayHistoryToClient(ws) {
  if (!ws.meta || ws.meta.status !== 'approved') return;
  const isAdmin = ws.meta.role === 'admin';
  const myId = ws.meta.deviceId;
  const userJoinMs = ws.meta.firstJoinedMs || Date.now();
  for (const [channel, msgs] of channelHistory.entries()) {
    if (!canAccessChannel(ws.meta, channel)) continue;
    let cutoffMs = userJoinMs;
    const custom = state.customChannels[channel];
    if (custom && custom.memberJoinedMs && typeof custom.memberJoinedMs[myId] === 'number') {
      cutoffMs = Math.max(cutoffMs, custom.memberJoinedMs[myId]);
    }
    for (const m of msgs) {
      // Admin sees full history; normal users NEVER see messages sent before they joined!
      if (!isAdmin) {
        const msgMs = typeof m.unixMs === 'number' ? m.unixMs : 0;
        if (msgMs < cutoffMs) continue;
      }
      safeSend(ws, formatChatPayload(m, isAdmin, undefined));
    }
  }
}

function purgeUserAccount(targetDev, actorLabel, keepBan = true) {
  if (!targetDev) return false;
  const oldHandle = state.handles[targetDev] || (state.accounts[targetDev] && state.accounts[targetDev].handle) || '';
  if (oldHandle === ADMIN_HANDLE) return false; // Never purge the admin handle!
  const oldUser = (state.accounts[targetDev] && state.accounts[targetDev].displayName)
    || (state.knownDevices[targetDev] && state.knownDevices[targetDev].user)
    || 'Bruker';

  if (oldHandle && state.handleOwners[oldHandle] === targetDev) {
    delete state.handleOwners[oldHandle];
  }
  delete state.accounts[targetDev];
  for (const [tk, s] of Object.entries(state.sessions)) {
    if (s && s.accountId === targetDev) delete state.sessions[tk];
  }
  delete state.handles[targetDev];
  delete state.knownDevices[targetDev];
  delete state.trustedDevices[targetDev];
  delete state.verifiedDevices[targetDev];
  delete state.mutedDevices[targetDev];
  delete state.heartbeatOffDevices[targetDev];
  if (!keepBan) delete state.bannedDevices[targetDev];

  // Remove from all friends & friend requests
  delete state.friends[targetDev];
  delete state.friendRequests[targetDev];
  for (const [uid, arr] of Object.entries(state.friends)) {
    if (Array.isArray(arr)) state.friends[uid] = arr.filter((id) => id !== targetDev);
  }
  for (const [uid, arr] of Object.entries(state.friendRequests)) {
    if (Array.isArray(arr)) state.friendRequests[uid] = arr.filter((r) => r.fromDeviceId !== targetDev);
  }

  // Remove owned private channels & remove from member lists of other private channels
  for (const [slug, ch] of Object.entries(state.customChannels)) {
    if (ch.ownerDeviceId === targetDev) {
      delete state.customChannels[slug];
      channelHistory.delete(slug);
      if (state.cooldowns.channels) delete state.cooldowns.channels[slug];
    } else if (Array.isArray(ch.members)) {
      ch.members = ch.members.filter((id) => id !== targetDev);
      if (ch.memberJoinedMs) delete ch.memberJoinedMs[targetDev];
    }
  }

  appendVaultRecord({
    seq: nextSeq++,
    type: 'system',
    channel: '#general-1',
    user: actorLabel || 'SYSTEM',
    handle: '',
    deviceId: targetDev,
    text: `[Bruker slettet: ${oldUser}${oldHandle ? ' (@' + oldHandle + ')' : ''} av ${actorLabel || 'SYSTEM'}]`,
    time: formatShortTime(),
    isoTime: formatIsoNow(),
    unixMs: Date.now()
  });

  // Disconnect active sockets of the deleted account
  for (const c of wss.clients) {
    if (c.meta && c.meta.deviceId === targetDev) {
      c.meta.status = 'deleted';
      safeSend(c, {
        type: 'account_deleted',
        text: 'Brukerkontoen din ble slettet.'
      });
      setTimeout(() => { try { c.close(); } catch { } }, 120);
    }
  }

  saveState();
  broadcastSocialStates();
  broadcastAdminState();
  return true;
}

function buildAdminStateSnapshot() {
  const activeByDevice = new Set();
  const onlineMap = getOnlineByDevice();
  const clients = [];

  for (const ws of wss.clients) {
    const m = ws.meta;
    if (!m) continue;
    if (m.deviceId) activeByDevice.add(m.deviceId);
    clients.push({
      connId: m.connId,
      online: true,
      status: m.status,
      role: m.role,
      user: m.user,
      handle: m.handle || getHandleFor(m.deviceId, onlineMap),
      clientVersion: m.clientVersion || '1.0.0',
      color: m.color,
      deviceId: m.deviceId || '',
      fingerprint: m.fingerprint || 'UKJENT',
      ip: m.ip,
      host: m.host || '',
      channel: m.channel || '#general-1',
      winState: m.winState || 'Synlig',
      connectedAt: m.connectedAt,
      lastHeartbeatIso: m.lastHeartbeatIso || '',
      secondsSincePing: m.lastHeartbeatMs ? Math.max(0, Math.round((Date.now() - m.lastHeartbeatMs) / 1000)) : -1,
      rttMs: m.rttMs || 0,
      heartbeatActive: effectiveHeartbeatFor(m.deviceId),
      muted: !!(m.deviceId && state.mutedDevices[m.deviceId]),
      banned: !!(m.deviceId && state.bannedDevices[m.deviceId])
    });
  }

  for (const [devId, info] of Object.entries(state.knownDevices)) {
    if (activeByDevice.has(devId)) continue;
    const isBanned = !!state.bannedDevices[devId];
    const isTrusted = !!state.trustedDevices[devId];
    const isVerified = !!state.verifiedDevices[devId];
    clients.push({
      connId: '',
      online: false,
      status: isBanned ? 'banned' : 'offline',
      role: isTrusted ? 'trusted' : (isVerified ? 'verified' : 'guest'),
      user: info.user || 'Ukjent',
      handle: getHandleFor(devId, onlineMap),
      clientVersion: info.clientVersion || '1.0.0',
      color: info.color || '#949BA4',
      deviceId: devId,
      fingerprint: info.fingerprint || devId.slice(0, 8),
      ip: info.ip || '',
      host: info.host || '',
      channel: info.lastChannel || '-',
      winState: 'Frakoblet',
      connectedAt: '',
      lastHeartbeatIso: info.lastSeenIso || '',
      secondsSincePing: -1,
      rttMs: 0,
      heartbeatActive: effectiveHeartbeatFor(devId),
      muted: !!state.mutedDevices[devId],
      banned: isBanned
    });
  }

  // All custom channels (stealth visibility ONLY for Admin!)
  const allCustomChannels = Object.values(state.customChannels).map((ch) => ({
    name: ch.name,
    ownerDeviceId: ch.ownerDeviceId,
    ownerName: getDisplayName(ch.ownerDeviceId, onlineMap),
    ownerHandle: getHandleFor(ch.ownerDeviceId, onlineMap),
    members: (ch.members || []).map((id) => ({
      deviceId: id,
      user: getDisplayName(id, onlineMap),
      handle: getHandleFor(id, onlineMap)
    })),
    createdAt: ch.createdAt || '',
    msgCount: (channelHistory.get(ch.name) || []).length,
    cooldownSec: Number((state.cooldowns.channels && state.cooldowns.channels[ch.name]) || 0)
  }));

  // Active DM rooms summary (stealth visibility ONLY for Admin!)
  const dmRooms = [];
  for (const [rk, arr] of dmHistory.entries()) {
    const [a, b] = rk.split('|');
    dmRooms.push({
      key: rk,
      devA: a,
      devB: b,
      nameA: getDisplayName(a, onlineMap),
      handleA: getHandleFor(a, onlineMap),
      nameB: getDisplayName(b, onlineMap),
      handleB: getHandleFor(b, onlineMap),
      msgCount: arr.length
    });
  }

  const nonAdminHandles = Object.values(state.handles).filter((h) => h && h !== ADMIN_HANDLE).length;
  const isFreshEmptyState = nonAdminHandles === 0
    && Object.keys(state.customChannels).length === 0
    && Object.keys(state.friends).length === 0
    && Object.keys(state.bannedDevices).length === 0;

  return {
    type: 'admin_state',
    serverMode: 'cloud-relay',
    serverVersion: SERVER_VERSION,
    adminHandle: ADMIN_HANDLE,
    isFreshEmptyState,
    serverTimeIso: formatIsoNow(),
    totalVaultRecords: vault.length,
    settings: state.settings,
    updater: state.updater,
    announcement: state.announcement,
    cooldowns: state.cooldowns,
    invites: Object.values(state.invites),
    customChannels: allCustomChannels,
    dmRooms,
    clients
  };
}

function broadcastAdminState() {
  sendToAdmins(buildAdminStateSnapshot());
}

function broadcastChatOrSystem(record, liveFile) {
  for (const c of wss.clients) {
    if (!c.meta || c.meta.status !== 'approved') continue;
    if (!canAccessChannel(c.meta, record.channel)) continue;
    const isAdmin = c.meta.role === 'admin';
    if (record.type === 'chat') {
      safeSend(c, formatChatPayload(record, isAdmin, liveFile || null));
    } else if (record.type === 'system') {
      safeSend(c, {
        type: 'system',
        msgId: record.msgId,
        channel: record.channel,
        text: record.text,
        time: record.time,
        isoTime: record.isoTime
      });
    }
  }
}

function recordAndBroadcastSystem(channel, text, actorMeta) {
  const seq = nextSeq++;
  const rec = {
    seq,
    msgId: `${Date.now()}-${seq}`,
    type: 'system',
    channel: channel || '#general-1',
    user: actorMeta ? actorMeta.user : 'SYSTEM',
    handle: actorMeta ? (actorMeta.handle || '') : '',
    color: '#E5C07B',
    role: actorMeta ? actorMeta.role : 'system',
    deviceId: actorMeta ? actorMeta.deviceId : '',
    fingerprint: actorMeta ? actorMeta.fingerprint : 'SYSTEM',
    ip: actorMeta ? actorMeta.ip : '',
    host: actorMeta ? actorMeta.host : '',
    text,
    time: formatShortTime(),
    isoTime: formatIsoNow(),
    unixMs: Date.now()
  };
  appendVaultRecord(rec);
  broadcastChatOrSystem(rec, null);
}

function admitClientSession(ws, newRole, announceText) {
  ws.meta.role = newRole;
  ws.meta.status = 'approved';
  ws.meta.lastHeartbeatMs = Date.now();
  ws.meta.lastHeartbeatIso = formatIsoNow();

  const lockedHandle = state.handles[ws.meta.deviceId] || '';
  ws.meta.handle = lockedHandle;

  const authMsg = {
    type: 'auth_status',
    status: 'approved',
    role: newRole,
    deviceId: ws.meta.deviceId,
    deviceTag: deviceTagFor(ws.meta.deviceId),
    fingerprint: ws.meta.fingerprint,
    handle: lockedHandle,
    needsHandle: !lockedHandle,
    user: ws.meta.user,
    serverVersion: SERVER_VERSION,
    updater: state.updater,
    announcement: state.announcement,
    cooldowns: state.cooldowns,
    heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
    heartbeatSec: state.settings.heartbeatSec,
    text: ''
  };
  if (ws.meta.isAdminAccount) authMsg.uOk = true;
  safeSend(ws, authMsg);

  pushConfigToClient(ws);
  replayHistoryToClient(ws);
  broadcastSocialStates();

  if (announceText) {
    recordAndBroadcastSystem('#general-1', announceText, ws.meta);
  }
}

wss.on('connection', (ws, req) => {
  const forwarded = req.headers['x-forwarded-for'];
  const rawIp = (typeof forwarded === 'string' ? forwarded.split(',')[0].trim() : req.socket.remoteAddress) || 'ukjent';
  const cleanIp = rawIp.replace(/^::ffff:/, '');
  const cookieToken = parseCookies(req).chat_session || '';

  ws.isAlive = true;
  ws.cookieSessionToken = cookieToken;
  ws.on('pong', () => { ws.isAlive = true; });

  const connId = `c${nextConnNum++}`;
  const nonce = crypto.randomBytes(32).toString('hex');

  const originHeader = String(req.headers.origin || '').trim();

  ws.meta = {
    connId,
    nonce,
    origin: originHeader,
    ip: cleanIp,
    user: 'Kobler til...',
    handle: '',
    clientVersion: SERVER_VERSION,
    color: '#3498DB',
    channel: '#general-1',
    host: '',
    winState: 'Synlig',
    deviceId: '',
    fingerprint: 'VENTER',
    role: 'unverified',
    isAdminAccount: false,
    adminUnlocked: false,
    adminUnlockNonce: '',
    adminUnlockExp: 0,
    unlockFailCount: 0,
    unlockFailWindowMs: 0,
    status: 'handshaking',
    typingTarget: null,
    connectedAt: formatIsoNow(),
    lastHeartbeatMs: Date.now(),
    lastHeartbeatIso: formatIsoNow(),
    rttMs: 0
  };

  safeSend(ws, {
    type: 'hello_challenge',
    nonce,
    serverMode: 'cloud-relay',
    serverVersion: SERVER_VERSION,
    serverBootId: SERVER_BOOT_ID,
    accessMode: state.settings.accessMode,
    heartbeatEnabled: state.settings.heartbeatEnabled,
    heartbeatSec: state.settings.heartbeatSec,
    updater: state.updater,
    announcement: state.announcement,
    cooldowns: state.cooldowns
  });

  ws.on('message', (raw) => {
    let msg;
    try { msg = JSON.parse(raw.toString('utf8')); } catch { return; }
    if (!msg || typeof msg.type !== 'string') return;

    if (msg.type === 'ping') {
      safeSend(ws, { type: 'pong', ts: msg.ts || Date.now() });
      return;
    }

    // v3 Session Token Authentication (stays logged in permanently until logout!)
    if (msg.type === 'session_auth') {
      if (ws.meta.status === 'approved') return;
      const token = String(msg.token || ws.cookieSessionToken || '').trim();
      const found = getSessionAccount(token);
      if (!found) {
        ws.meta.status = 'logged_out';
        safeSend(ws, { type: 'auth_status', status: 'logged_out', text: 'Logg inn med brukernavn og passord.' });
        return;
      }

      const acc = found.account;
      const isAdminAcc = acc.handle === ADMIN_HANDLE;
      const clientVersion = String(msg.clientVersion || SERVER_VERSION).trim().slice(0, 20) || SERVER_VERSION;
      const channel = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32) : '#general-1';
      const host = String(msg.host || 'Web').trim().slice(0, 40);

      if (state.bannedDevices[acc.accountId] && !isAdminAcc) {
        safeSend(ws, { type: 'auth_status', status: 'banned', text: 'Denne kontoen er utestengt.' });
        ws.close();
        broadcastAdminState();
        return;
      }

      ws.meta.deviceId = acc.accountId;
      ws.meta.fingerprint = `${acc.accountId.slice(0, 4).toUpperCase()}-${acc.accountId.slice(4, 8).toUpperCase()}`;
      ws.meta.handle = acc.handle;
      ws.meta.user = acc.displayName;
      ws.meta.color = acc.color || '#3498DB';
      ws.meta.channel = channel;
      ws.meta.host = host;
      ws.meta.clientVersion = clientVersion;
      ws.meta.firstJoinedMs = acc.firstJoinedMs || Date.now();
      ws.meta.sessionToken = token;
      ws.meta.isAdminAccount = isAdminAcc;
      ws.meta.adminUnlocked = false; // ALWAYS locked until Alt+U + verified private password file!

      acc.lastSeenIso = formatIsoNow();
      syncKnownDeviceFromAccount(acc, { clientVersion, ip: ws.meta.ip, host, lastChannel: channel });
      saveState();

      // Start as normal trusted/verified session — zero admin UI or admin perms until RSA-2048 password file verified!
      const role = (isAdminAcc || state.trustedDevices[acc.accountId]) ? 'trusted' : 'verified';
      admitClientSession(ws, role, '');

      safeSend(ws, {
        type: 'gif_favorites_sync',
        favorites: Array.isArray(acc.gifFavorites) ? acc.gifFavorites : []
      });

      broadcastAdminState();
      return;
    }

    // Legacy v1/v2 clients -> tell them to refresh/open the v3 website!
    if (msg.type === 'client_auth') {
      safeSend(ws, { type: 'reload_page', serverVersion: SERVER_VERSION });
      safeSend(ws, {
        type: 'auth_status',
        status: 'rejected',
        text: `Chat er oppgradert til v${SERVER_VERSION} med brukernavn og passord! Last inn nettsiden på nytt: ${PUBLIC_WEB_URL}`
      });
      setTimeout(() => { try { ws.close(); } catch { } }, 150);
      return;
    }

    // Step 1 of Alt+U secure unlock: issue single-use 256-bit challenge (ONLY for @kvartsbuen!)
    if (msg.type === 'admin_unlock_req') {
      if (ws.meta.status !== 'approved' || !ws.meta.isAdminAccount || ws.meta.handle !== ADMIN_HANDLE) return;
      ws.meta.adminUnlockNonce = crypto.randomBytes(32).toString('hex');
      ws.meta.adminUnlockExp = Date.now() + 2 * 60 * 1000;
      safeSend(ws, { type: 'admin_unlock_challenge', nonce: ws.meta.adminUnlockNonce });
      return;
    }

    // Step 2 of Alt+U secure unlock: verify RSA-2048-SHA256 signature from private password file!
    if (msg.type === 'admin_unlock_verify') {
      if (ws.meta.status !== 'approved' || !ws.meta.isAdminAccount || ws.meta.handle !== ADMIN_HANDLE) return;
      const now = Date.now();
      if (now - ws.meta.unlockFailWindowMs > 60000) {
        ws.meta.unlockFailWindowMs = now;
        ws.meta.unlockFailCount = 0;
      }
      if (ws.meta.unlockFailCount >= 5) {
        safeSend(ws, { type: 'admin_unlock_result', ok: false, error: 'For mange feilforsøk. Vent 1 minutt og prøv igjen.' });
        return;
      }
      const expectedNonce = ws.meta.adminUnlockNonce;
      const exp = ws.meta.adminUnlockExp;
      ws.meta.adminUnlockNonce = '';
      ws.meta.adminUnlockExp = 0;
      if (!expectedNonce || !exp || now > exp) {
        safeSend(ws, { type: 'admin_unlock_result', ok: false, error: 'Utfordringen utløp. Prøv på nytt.' });
        return;
      }
      const verified = verifyRsaSha256(ADMIN_PUBKEY_XML, `ADMIN_UNLOCK:${expectedNonce}`, String(msg.sig || ''));
      if (!verified) {
        ws.meta.unlockFailCount++;
        safeSend(ws, { type: 'admin_unlock_result', ok: false, error: 'Feil passordfil! Tilgang avslått.' });
        return;
      }
      ws.meta.unlockFailCount = 0;
      ws.meta.role = 'admin';
      ws.meta.adminUnlocked = true;

      safeSend(ws, { type: 'admin_unlock_result', ok: true });
      if (ADMIN_BUNDLE_OBJ) {
        safeSend(ws, { type: 'admin_ui_bundle', ...ADMIN_BUNDLE_OBJ });
      }
      const missing = vault.slice(-300);
      if (missing.length > 0) {
        safeSend(ws, { type: 'admin_vault_sync', records: missing });
      }
      pushConfigToClient(ws);
      safeSend(ws, buildAdminStateSnapshot());
      return;
    }

    // Lock admin panel manually without logging out of chat
    if (msg.type === 'admin_lock') {
      if (ws.meta.status !== 'approved' || !ws.meta.isAdminAccount) return;
      ws.meta.adminUnlocked = false;
      ws.meta.role = 'trusted';
      ws.meta.adminUnlockNonce = '';
      safeSend(ws, { type: 'admin_locked' });
      pushConfigToClient(ws);
      return;
    }

    if (msg.type === 'heartbeat') {
      ws.meta.lastHeartbeatMs = Date.now();
      ws.meta.lastHeartbeatIso = formatIsoNow();
      let changed = false;
      if (typeof msg.user === 'string' && msg.user.trim()) {
        const chk = validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin' || ws.meta.isAdminAccount);
        if (chk.ok && chk.name !== ws.meta.user) { ws.meta.user = chk.name; changed = true; }
      }
      if (/^#[0-9A-Fa-f]{6}$/.test(msg.color) && msg.color !== ws.meta.color) {
        ws.meta.color = msg.color; changed = true;
      }
      if (typeof msg.channel === 'string' && msg.channel.startsWith('#')) ws.meta.channel = msg.channel.slice(0, 32);
      if (typeof msg.winState === 'string') ws.meta.winState = msg.winState.slice(0, 20);
      if (typeof msg.rttMs === 'number' && msg.rttMs >= 0) ws.meta.rttMs = Math.round(msg.rttMs);

      if (ws.meta.deviceId && state.accounts[ws.meta.deviceId]) {
        state.accounts[ws.meta.deviceId].displayName = ws.meta.user;
        state.accounts[ws.meta.deviceId].color = ws.meta.color;
        state.accounts[ws.meta.deviceId].lastSeenIso = ws.meta.lastHeartbeatIso;
      }
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].user = ws.meta.user;
        state.knownDevices[ws.meta.deviceId].color = ws.meta.color;
        state.knownDevices[ws.meta.deviceId].lastChannel = ws.meta.channel;
        state.knownDevices[ws.meta.deviceId].lastSeenIso = ws.meta.lastHeartbeatIso;
      }

      safeSend(ws, {
        type: 'heartbeat_ack',
        clientTs: msg.clientTs || Date.now(),
        heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
        heartbeatSec: state.settings.heartbeatSec
      });
      if (changed) { saveState(); broadcastSocialStates(); }
      broadcastAdminState();
      return;
    }

    if (msg.type === 'admin_cmd') {
      if (ws.meta.role !== 'admin' || ws.meta.adminUnlocked !== true || ws.meta.status !== 'approved') return;
      handleAdminCommand(ws, msg);
      return;
    }

    if (ws.meta.status !== 'approved') return;

    // Self-delete user account (never removes existing ban, never purges Admin)
    if (msg.type === 'delete_self') {
      if (ws.meta.role === 'admin' || ws.meta.handle === ADMIN_HANDLE) {
        safeSend(ws, { type: 'social_notice', text: 'Admin-kontoen kan ikke slettes herfra.' });
        return;
      }
      purgeUserAccount(ws.meta.deviceId, ws.meta.user, true);
      return;
    }

    // Per-account synced GIF Favorites toggle (just like Discord!)
    if (msg.type === 'gif_fav_toggle') {
      const acc = state.accounts[ws.meta.deviceId];
      if (!acc) return;
      const gif = sanitizeGifObj(msg.gif);
      if (!gif) return;
      if (!Array.isArray(acc.gifFavorites)) acc.gifFavorites = [];
      const idx = acc.gifFavorites.findIndex((f) => f.url === gif.url || f.id === gif.id);
      if (idx !== -1) {
        acc.gifFavorites.splice(idx, 1);
      } else {
        acc.gifFavorites.unshift(gif);
        if (acc.gifFavorites.length > MAX_GIF_FAVORITES) acc.gifFavorites.length = MAX_GIF_FAVORITES;
      }
      saveState();
      for (const c of wss.clients) {
        if (c.meta && c.meta.status === 'approved' && c.meta.deviceId === acc.accountId) {
          safeSend(c, { type: 'gif_favorites_sync', favorites: acc.gifFavorites });
        }
      }
      return;
    }

    // Instant live Display Name / color update (keeps permanent accountId & @handle intact, blocks impersonation!)
    if (msg.type === 'update_profile') {
      const nc = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : ws.meta.color;
      if (typeof msg.user === 'string' && msg.user.trim()) {
        const chk = validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin' || ws.meta.isAdminAccount);
        if (!chk.ok) {
          safeSend(ws, {
            type: 'profile_rejected',
            error: chk.error,
            user: ws.meta.user,
            color: ws.meta.color
          });
          return;
        }
        ws.meta.user = chk.name;
      }
      ws.meta.color = nc;
      if (ws.meta.deviceId && state.accounts[ws.meta.deviceId]) {
        state.accounts[ws.meta.deviceId].displayName = ws.meta.user;
        state.accounts[ws.meta.deviceId].color = ws.meta.color;
      }
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].user = ws.meta.user;
        state.knownDevices[ws.meta.deviceId].color = ws.meta.color;
      }
      saveState();
      broadcastSocialStates();
      broadcastAdminState();
      return;
    }

    // Live Typing indicator (with automatic cleanup on switch/send/disconnect)
    if (msg.type === 'typing') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      const active = !!msg.active;
      if (!active) {
        clearTypingFor(ws);
        return;
      }
      if (scope === 'dm') {
        const toId = String(msg.toDeviceId || '').trim();
        if (!toId || toId === ws.meta.deviceId) return;
        if (ws.meta.typingTarget && (ws.meta.typingTarget.scope !== 'dm' || ws.meta.typingTarget.toDeviceId !== toId)) {
          clearTypingFor(ws);
        }
        ws.meta.typingTarget = { scope: 'dm', toDeviceId: toId };
        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && c.meta.deviceId === toId) {
            safeSend(c, {
              type: 'typing',
              scope: 'dm',
              fromDeviceId: ws.meta.deviceId,
              user: ws.meta.user,
              handle: ws.meta.handle || '',
              active: true
            });
          }
        }
      } else {
        const ch = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32).toLowerCase() : '#general-1';
        if (!canAccessChannel(ws.meta, ch)) return;
        if (ws.meta.typingTarget && (ws.meta.typingTarget.scope !== 'channel' || ws.meta.typingTarget.channel !== ch)) {
          clearTypingFor(ws);
        }
        ws.meta.typingTarget = { scope: 'channel', channel: ch };
        for (const c of wss.clients) {
          if (c === ws || !c.meta || c.meta.status !== 'approved') continue;
          if (!canAccessChannel(c.meta, ch)) continue;
          safeSend(c, {
            type: 'typing',
            scope: 'channel',
            channel: ch,
            fromDeviceId: ws.meta.deviceId,
            user: ws.meta.user,
            handle: ws.meta.handle || '',
            active: true
          });
        }
      }
      return;
    }

    // Delete message (Author can delete own; Admin can delete ANY message!)
    if (msg.type === 'delete_message') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      const msgId = String(msg.msgId || '').trim();
      if (!msgId) return;

      if (scope === 'channel') {
        const ch = String(msg.channel || '').trim().toLowerCase();
        if (!canAccessChannel(ws.meta, ch)) return;
        const arr = channelHistory.get(ch) || [];
        const idx = arr.findIndex((m) => m.msgId === msgId);
        if (idx === -1) return;
        const target = arr[idx];
        if (target.deviceId !== ws.meta.deviceId && ws.meta.role !== 'admin') return;
        arr.splice(idx, 1);
        channelHistory.set(ch, arr);

        appendVaultRecord({
          seq: nextSeq++,
          type: 'delete',
          scope: 'channel',
          channel: ch,
          msgId,
          user: ws.meta.user,
          handle: ws.meta.handle || '',
          deviceId: ws.meta.deviceId,
          text: `[Slettet melding av ${target.user}: ${String(target.text || '').slice(0, 80)}]`,
          time: formatShortTime(),
          isoTime: formatIsoNow()
        });

        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, { type: 'message_deleted', scope: 'channel', channel: ch, msgId });
          }
        }
        return;
      }

      if (scope === 'dm') {
        const peerId = String(msg.peerDeviceId || '').trim();
        if (!peerId) return;
        const rk = dmRoomKey(ws.meta.deviceId, peerId);
        const arr = dmHistory.get(rk) || [];
        const idx = arr.findIndex((m) => m.msgId === msgId);
        if (idx === -1) return;
        const target = arr[idx];
        if (target.fromDeviceId !== ws.meta.deviceId && ws.meta.role !== 'admin') return;
        arr.splice(idx, 1);
        dmHistory.set(rk, arr);

        appendVaultRecord({
          seq: nextSeq++,
          type: 'delete',
          scope: 'dm',
          channel: `@DM`,
          msgId,
          user: ws.meta.user,
          handle: ws.meta.handle || '',
          deviceId: ws.meta.deviceId,
          text: `[Slettet DM-melding: ${String(target.text || '').slice(0, 80)}]`,
          time: formatShortTime(),
          isoTime: formatIsoNow()
        });

        for (const c of wss.clients) {
          if (!c.meta || c.meta.status !== 'approved') continue;
          if (c.meta.deviceId === target.fromDeviceId || c.meta.deviceId === target.toDeviceId) {
            safeSend(c, {
              type: 'message_deleted',
              scope: 'dm',
              fromDeviceId: target.fromDeviceId,
              toDeviceId: target.toDeviceId,
              msgId
            });
          }
        }
        return;
      }
    }

    // Edit own message
    if (msg.type === 'edit_message') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      const msgId = String(msg.msgId || '').trim();
      const newText = typeof msg.text === 'string' ? msg.text.trim().slice(0, 1000) : '';
      if (!msgId || !newText) return;

      if (scope === 'channel') {
        const ch = String(msg.channel || '').trim().toLowerCase();
        if (!canAccessChannel(ws.meta, ch)) return;
        const arr = channelHistory.get(ch) || [];
        const target = arr.find((m) => m.msgId === msgId);
        if (!target || target.deviceId !== ws.meta.deviceId) return;
        target.text = newText;
        target.edited = true;
        target.editedAt = formatShortTime();

        appendVaultRecord({
          seq: nextSeq++,
          type: 'edit',
          scope: 'channel',
          channel: ch,
          msgId,
          user: ws.meta.user,
          handle: ws.meta.handle || '',
          deviceId: ws.meta.deviceId,
          text: newText,
          time: target.editedAt,
          isoTime: formatIsoNow()
        });

        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, {
              type: 'message_edited',
              scope: 'channel',
              channel: ch,
              msgId,
              text: newText,
              editedAt: target.editedAt
            });
          }
        }
        return;
      }

      if (scope === 'dm') {
        const peerId = String(msg.peerDeviceId || '').trim();
        if (!peerId) return;
        const rk = dmRoomKey(ws.meta.deviceId, peerId);
        const arr = dmHistory.get(rk) || [];
        const target = arr.find((m) => m.msgId === msgId);
        if (!target || target.fromDeviceId !== ws.meta.deviceId) return;
        target.text = newText;
        target.edited = true;
        target.editedAt = formatShortTime();

        for (const c of wss.clients) {
          if (!c.meta || c.meta.status !== 'approved') continue;
          if (c.meta.deviceId === target.fromDeviceId || c.meta.deviceId === target.toDeviceId) {
            safeSend(c, {
              type: 'message_edited',
              scope: 'dm',
              fromDeviceId: target.fromDeviceId,
              toDeviceId: target.toDeviceId,
              msgId,
              text: newText,
              editedAt: target.editedAt
            });
          }
        }
        return;
      }
    }

    // Emoji reactions
    if (msg.type === 'toggle_reaction') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      const msgId = String(msg.msgId || '').trim();
      const emoji = String(msg.emoji || '').trim();
      if (!msgId || !ALLOWED_REACTIONS.has(emoji)) return;

      let target = null;
      let ch = '';
      if (scope === 'channel') {
        ch = String(msg.channel || '').trim().toLowerCase();
        if (!canAccessChannel(ws.meta, ch)) return;
        target = (channelHistory.get(ch) || []).find((m) => m.msgId === msgId);
      } else {
        const peerId = String(msg.peerDeviceId || '').trim();
        if (!peerId) return;
        const rk = dmRoomKey(ws.meta.deviceId, peerId);
        target = (dmHistory.get(rk) || []).find((m) => m.msgId === msgId);
      }
      if (!target) return;

      if (!target.reactions || typeof target.reactions !== 'object') target.reactions = {};
      const list = Array.isArray(target.reactions[emoji]) ? target.reactions[emoji] : [];
      const myId = ws.meta.deviceId;
      if (list.includes(myId)) {
        target.reactions[emoji] = list.filter((id) => id !== myId);
        if (target.reactions[emoji].length === 0) delete target.reactions[emoji];
      } else {
        list.push(myId);
        target.reactions[emoji] = list;
      }

      if (scope === 'channel') {
        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, { type: 'message_reactions', scope: 'channel', channel: ch, msgId, reactions: target.reactions });
          }
        }
      } else {
        for (const c of wss.clients) {
          if (!c.meta || c.meta.status !== 'approved') continue;
          if (c.meta.deviceId === target.fromDeviceId || c.meta.deviceId === target.toDeviceId) {
            safeSend(c, {
              type: 'message_reactions',
              scope: 'dm',
              fromDeviceId: target.fromDeviceId,
              toDeviceId: target.toDeviceId,
              msgId,
              reactions: target.reactions
            });
          }
        }
      }
      return;
    }

    // Custom Private Channels (up to 5 per user!)
    if (msg.type === 'create_channel') {
      const myId = ws.meta.deviceId;
      const ownedCount = Object.values(state.customChannels).filter((c) => c.ownerDeviceId === myId).length;
      if (ownedCount >= MAX_CUSTOM_CHANNELS_PER_USER && ws.meta.role !== 'admin') {
        safeSend(ws, { type: 'social_notice', text: `Du kan maks ha ${MAX_CUSTOM_CHANNELS_PER_USER} egne kanaler samtidig.` });
        return;
      }
      const slug = sanitizeChannelSlug(msg.name);
      if (!slug || slug.length < 2) {
        safeSend(ws, { type: 'social_notice', text: 'Ugyldig kanalnavn.' });
        return;
      }
      if (DEFAULT_CHANNELS.includes(slug) || state.customChannels[slug]) {
        safeSend(ws, { type: 'social_notice', text: `Kanalen ${slug} finnes allerede.` });
        return;
      }
      const nowMs = Date.now();
      state.customChannels[slug] = {
        name: slug,
        ownerDeviceId: myId,
        ownerName: ws.meta.user,
        members: [myId],
        memberJoinedMs: { [myId]: nowMs },
        createdAt: formatIsoNow()
      };
      saveState();
      safeSend(ws, { type: 'channel_created', channel: slug });
      broadcastSocialStates();
      broadcastAdminState();
      return;
    }

    if (msg.type === 'delete_channel') {
      const slug = String(msg.channel || '').trim().toLowerCase();
      const ch = state.customChannels[slug];
      if (!ch) return;
      if (ch.ownerDeviceId !== ws.meta.deviceId && ws.meta.role !== 'admin') {
        safeSend(ws, { type: 'social_notice', text: 'Bare eieren kan slette denne kanalen.' });
        return;
      }
      delete state.customChannels[slug];
      channelHistory.delete(slug);
      if (state.cooldowns.channels) delete state.cooldowns.channels[slug];
      saveState();
      broadcastSocialStates();
      broadcastAdminState();
      return;
    }

    if (msg.type === 'channel_invite') {
      const slug = String(msg.channel || '').trim().toLowerCase();
      const ch = state.customChannels[slug];
      if (!ch || ch.ownerDeviceId !== ws.meta.deviceId) return;

      let targetId = String(msg.targetDeviceId || '').trim();
      if (!targetId && msg.targetUser) {
        targetId = resolveUserDeviceId(msg.targetUser, ws.meta.deviceId);
      }
      if (!targetId) {
        safeSend(ws, { type: 'social_notice', text: 'Fant ingen bruker med det brukernavnet/@handle.' });
        return;
      }
      if (!Array.isArray(ch.members)) ch.members = [ch.ownerDeviceId];
      if (!ch.memberJoinedMs || typeof ch.memberJoinedMs !== 'object') ch.memberJoinedMs = {};
      if (!ch.members.includes(targetId)) {
        ch.members.push(targetId);
        // Record join timestamp so newly invited members CANNOT see messages sent before they joined!
        ch.memberJoinedMs[targetId] = Date.now();
        saveState();
        broadcastSocialStates();
        broadcastAdminState();
      }
      safeSend(ws, { type: 'social_notice', text: `Bruker lagt til i ${slug}!` });
      return;
    }

    if (msg.type === 'channel_kick') {
      const slug = String(msg.channel || '').trim().toLowerCase();
      const ch = state.customChannels[slug];
      const targetId = String(msg.targetDeviceId || '').trim();
      if (!ch || ch.ownerDeviceId !== ws.meta.deviceId || targetId === ch.ownerDeviceId) return;
      ch.members = (ch.members || []).filter((id) => id !== targetId);
      saveState();
      broadcastSocialStates();
      broadcastAdminState();
      return;
    }

    if (msg.type === 'chat') {
      if (ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId] && ws.meta.role !== 'admin' && !ws.meta.isAdminAccount) {
        safeSend(ws, { type: 'system', channel: ws.meta.channel, text: 'Du kan ikke sende meldinger akkurat nå (dempet).' });
        return;
      }

      if (String(ws.meta.clientVersion || '').startsWith('2.') && !ws.meta.handle) {
        safeSend(ws, { type: 'social_notice', text: 'Velg ditt faste @brukernavn først.' });
        return;
      }

      const channel = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32).toLowerCase() : '#general-1';
      if (!canAccessChannel(ws.meta, channel)) return;

      // Enforce slowmode/cooldown for non-admins (Admin is ALWAYS exempt!)
      const cdSec = effectiveCooldownSec(channel);
      if (cdSec > 0 && ws.meta.role !== 'admin' && !ws.meta.isAdminAccount) {
        const key = `${ws.meta.deviceId}|${channel}`;
        const last = lastMsgByDeviceChannel.get(key) || 0;
        const elapsedMs = Date.now() - last;
        if (elapsedMs < cdSec * 1000) {
          const remainingSec = Math.max(1, Math.ceil((cdSec * 1000 - elapsedMs) / 1000));
          safeSend(ws, { type: 'cooldown_wait', channel, remainingSec });
          return;
        }
        lastMsgByDeviceChannel.set(key, Date.now());
      }

      const text = typeof msg.text === 'string' ? msg.text.trim().slice(0, 1000) : '';
      const liveFile = sanitizeLiveAttachment(msg.file);
      const gifObj = sanitizeGifObj(msg.gif);
      if (!text && !liveFile && !gifObj) return;

      const nameCheck = msg.user ? validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin' || ws.meta.isAdminAccount) : { ok: false };
      const user = nameCheck.ok ? nameCheck.name : (ws.meta.user || 'Ukjent');
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : ws.meta.color;
      const nameChanged = ws.meta.user !== user || ws.meta.color !== color;
      ws.meta.user = user;
      ws.meta.color = color;
      ws.meta.channel = channel;
      if (ws.meta.deviceId && state.accounts[ws.meta.deviceId]) {
        state.accounts[ws.meta.deviceId].displayName = user;
        state.accounts[ws.meta.deviceId].color = color;
      }
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].user = user;
        state.knownDevices[ws.meta.deviceId].color = color;
      }

      clearTypingFor(ws);

      const arr = channelHistory.get(channel) || [];
      const seq = nextSeq++;
      const metaFile = stripFileData(liveFile);
      const rec = {
        seq,
        msgId: `${Date.now()}-${seq}`,
        type: 'chat',
        channel,
        user,
        handle: ws.meta.handle || '',
        deviceTag: deviceTagFor(ws.meta.deviceId),
        color,
        role: ws.meta.role,
        deviceId: ws.meta.deviceId,
        fingerprint: ws.meta.fingerprint,
        ip: ws.meta.ip,
        host: ws.meta.host,
        text: text || (gifObj ? '' : (metaFile ? `[Fil: ${metaFile.name} (${Math.round(metaFile.size / 1024)} KB)]` : '')),
        replyTo: resolveAuthoritativeReply(msg.replyTo, arr),
        reactions: {},
        edited: false,
        editedAt: '',
        gif: gifObj,
        file: metaFile, // NEVER store base64 image/file data on server!
        time: formatShortTime(),
        isoTime: formatIsoNow(),
        unixMs: Date.now()
      };

      arr.push(rec);
      if (arr.length > MAX_CHANNEL_HISTORY) arr.shift();
      channelHistory.set(channel, arr);

      appendVaultRecord(rec);
      broadcastChatOrSystem(rec, liveFile);
      if (nameChanged) { saveState(); broadcastSocialStates(); }
      broadcastAdminState();
      return;
    }

    if (msg.type === 'dm') {
      if (ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId] && ws.meta.role !== 'admin' && !ws.meta.isAdminAccount) return;
      const toDeviceId = String(msg.toDeviceId || '').trim();
      if (!toDeviceId || toDeviceId === ws.meta.deviceId) return;

      const text = typeof msg.text === 'string' ? msg.text.trim().slice(0, 1000) : '';
      const liveFile = sanitizeLiveAttachment(msg.file);
      const gifObj = sanitizeGifObj(msg.gif);
      if (!text && !liveFile && !gifObj) return;

      const nameCheck = msg.user ? validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin' || ws.meta.isAdminAccount) : { ok: false };
      const user = nameCheck.ok ? nameCheck.name : (ws.meta.user || 'Ukjent');
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : ws.meta.color;
      ws.meta.user = user;
      ws.meta.color = color;

      clearTypingFor(ws);

      const rk = dmRoomKey(ws.meta.deviceId, toDeviceId);
      const arr = dmHistory.get(rk) || [];
      const targetInfo = state.knownDevices[toDeviceId] || { user: 'Bruker' };
      const seq = nextSeq++;
      const metaFile = stripFileData(liveFile);
      const dmRec = {
        seq,
        msgId: `DM-${Date.now()}-${seq}`,
        type: 'dm',
        channel: `@DM:${user}->${targetInfo.user || toDeviceId.slice(0, 8)}`,
        fromDeviceId: ws.meta.deviceId,
        toDeviceId,
        user,
        handle: ws.meta.handle || '',
        deviceTag: deviceTagFor(ws.meta.deviceId),
        color,
        role: ws.meta.role,
        deviceId: ws.meta.deviceId,
        fingerprint: ws.meta.fingerprint,
        ip: ws.meta.ip,
        host: ws.meta.host,
        text: text || (gifObj ? '' : (metaFile ? `[Fil: ${metaFile.name} (${Math.round(metaFile.size / 1024)} KB)]` : '')),
        replyTo: resolveAuthoritativeReply(msg.replyTo, arr),
        reactions: {},
        edited: false,
        editedAt: '',
        gif: gifObj,
        file: metaFile, // NEVER store base64 data!
        time: formatShortTime(),
        isoTime: formatIsoNow(),
        unixMs: Date.now()
      };

      arr.push(dmRec);
      if (arr.length > MAX_DM_HISTORY) arr.shift();
      dmHistory.set(rk, arr);

      appendVaultRecord(dmRec);

      for (const c of wss.clients) {
        if (!c.meta || c.meta.status !== 'approved') continue;
        if (c.meta.deviceId === ws.meta.deviceId || c.meta.deviceId === toDeviceId) {
          safeSend(c, formatDmPayload(dmRec, c.meta.role === 'admin', liveFile || null));
        }
      }
      broadcastAdminState();
      return;
    }

    if (msg.type === 'dm_history_req') {
      const peerId = String(msg.peerDeviceId || '').trim();
      if (!peerId) return;
      const rk = dmRoomKey(ws.meta.deviceId, peerId);
      const arr = dmHistory.get(rk) || [];
      for (const m of arr) {
        safeSend(ws, formatDmPayload(m, ws.meta.role === 'admin', undefined));
      }
      return;
    }

    if (msg.type === 'friend_req') {
      const myId = ws.meta.deviceId;
      let targetId = String(msg.targetDeviceId || '').trim();
      if (!targetId && msg.targetUser) {
        targetId = resolveUserDeviceId(msg.targetUser, myId);
      }
      if (!targetId || targetId === myId) {
        safeSend(ws, { type: 'social_notice', text: 'Fant ingen bruker med det brukernavnet/@handle.' });
        return;
      }
      state.friends[myId] = Array.isArray(state.friends[myId]) ? state.friends[myId] : [];
      state.friends[targetId] = Array.isArray(state.friends[targetId]) ? state.friends[targetId] : [];
      if (state.friends[myId].includes(targetId)) {
        safeSend(ws, { type: 'social_notice', text: 'Dere er allerede venner!' });
        return;
      }
      const myIncoming = Array.isArray(state.friendRequests[myId]) ? state.friendRequests[myId] : [];
      if (myIncoming.some((r) => r.fromDeviceId === targetId)) {
        state.friendRequests[myId] = myIncoming.filter((r) => r.fromDeviceId !== targetId);
        state.friends[myId].push(targetId);
        if (!state.friends[targetId].includes(myId)) state.friends[targetId].push(myId);
        saveState();
        broadcastSocialStates();
        return;
      }
      state.friendRequests[targetId] = Array.isArray(state.friendRequests[targetId]) ? state.friendRequests[targetId] : [];
      if (!state.friendRequests[targetId].some((r) => r.fromDeviceId === myId)) {
        state.friendRequests[targetId].push({
          fromDeviceId: myId,
          fromUser: ws.meta.user,
          fromHandle: ws.meta.handle || '',
          fromColor: ws.meta.color,
          at: formatIsoNow()
        });
      }
      saveState();
      safeSend(ws, { type: 'social_notice', text: 'Venneforespørsel sendt!' });
      broadcastSocialStates();
      return;
    }

    if (msg.type === 'friend_accept') {
      const myId = ws.meta.deviceId;
      const fromId = String(msg.fromDeviceId || '').trim();
      if (!fromId || fromId === myId) return;
      state.friendRequests[myId] = (Array.isArray(state.friendRequests[myId]) ? state.friendRequests[myId] : []).filter((r) => r.fromDeviceId !== fromId);
      state.friends[myId] = Array.isArray(state.friends[myId]) ? state.friends[myId] : [];
      state.friends[fromId] = Array.isArray(state.friends[fromId]) ? state.friends[fromId] : [];
      if (!state.friends[myId].includes(fromId)) state.friends[myId].push(fromId);
      if (!state.friends[fromId].includes(myId)) state.friends[fromId].push(myId);
      saveState();
      broadcastSocialStates();
      return;
    }

    if (msg.type === 'friend_decline') {
      const myId = ws.meta.deviceId;
      const fromId = String(msg.fromDeviceId || '').trim();
      state.friendRequests[myId] = (Array.isArray(state.friendRequests[myId]) ? state.friendRequests[myId] : []).filter((r) => r.fromDeviceId !== fromId);
      saveState();
      broadcastSocialStates();
      return;
    }

    if (msg.type === 'friend_remove') {
      const myId = ws.meta.deviceId;
      const peerId = String(msg.peerDeviceId || '').trim();
      if (Array.isArray(state.friends[myId])) state.friends[myId] = state.friends[myId].filter((id) => id !== peerId);
      if (Array.isArray(state.friends[peerId])) state.friends[peerId] = state.friends[peerId].filter((id) => id !== myId);
      saveState();
      broadcastSocialStates();
      return;
    }
  });

  ws.on('close', () => {
    clearTypingFor(ws);
    if (ws.meta && ws.meta.status === 'approved') {
      const nowIso = formatIsoNow();
      if (ws.meta.deviceId && state.accounts[ws.meta.deviceId]) {
        state.accounts[ws.meta.deviceId].lastSeenIso = nowIso;
      }
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].lastSeenIso = nowIso;
      }
    }
    broadcastSocialStates();
    broadcastAdminState();
  });
});

function findDeviceIdByQuery(rawQuery) {
  const q = String(rawQuery || '').trim();
  if (!q) return '';
  if (state.accounts[q] || state.knownDevices[q] || state.handles[q]) return q;
  const cleanHandle = q.replace(/^@+/, '').toLowerCase();
  if (state.handleOwners[cleanHandle]) return state.handleOwners[cleanHandle];
  const lower = q.toLowerCase();
  for (const devId of Object.keys(state.knownDevices)) {
    if (devId.toLowerCase().startsWith(lower) && lower.length >= 6) return devId;
    const info = state.knownDevices[devId];
    if (info && String(info.user || '').toLowerCase() === lower) return devId;
  }
  for (const c of wss.clients) {
    if (c.meta && c.meta.deviceId) {
      if (c.meta.deviceId.toLowerCase().startsWith(lower) && lower.length >= 6) return c.meta.deviceId;
      if (String(c.meta.user || '').toLowerCase() === lower) return c.meta.deviceId;
    }
  }
  return '';
}

function renameUserPermanentHandle(targetDev, rawNewHandle, actorLabel) {
  if (!targetDev) return { ok: false, error: 'Ingen bruker valgt.' };
  const oldHandle = state.handles[targetDev] || (state.accounts[targetDev] && state.accounts[targetDev].handle) || '';
  if (oldHandle === ADMIN_HANDLE) {
    return { ok: false, error: `Admin-brukernavnet @${ADMIN_HANDLE} er låst og kan ikke endres.` };
  }
  const clean = sanitizeHandle(rawNewHandle, false);
  if (!clean) {
    return { ok: false, error: `Ugyldig @brukernavn. Bruk 3–20 tegn (a-å, 0-9, . _ -) og ikke @${ADMIN_HANDLE}.` };
  }
  if (state.handleOwners[clean] && state.handleOwners[clean] !== targetDev) {
    return { ok: false, error: `Brukernavnet @${clean} er allerede tatt av en annen bruker.` };
  }
  if (oldHandle && state.handleOwners[oldHandle] === targetDev) {
    delete state.handleOwners[oldHandle];
  }
  state.handles[targetDev] = clean;
  state.handleOwners[clean] = targetDev;
  if (state.accounts[targetDev]) {
    state.accounts[targetDev].handle = clean;
  }
  if (state.knownDevices[targetDev]) {
    state.knownDevices[targetDev].handle = clean;
  }
  for (const c of wss.clients) {
    if (c.meta && c.meta.deviceId === targetDev) {
      c.meta.handle = clean;
      safeSend(c, {
        type: 'handle_changed_by_admin',
        handle: clean,
        text: `Ditt faste brukernavn ble endret til @${clean}.`
      });
    }
  }
  appendVaultRecord({
    seq: nextSeq++,
    type: 'system',
    channel: '#general-1',
    user: actorLabel || 'ADMIN',
    handle: ADMIN_HANDLE,
    deviceId: targetDev,
    text: `[Fast @brukernavn endret: ${oldHandle ? '@' + oldHandle : '(ingen)'} -> @${clean}]`,
    time: formatShortTime(),
    isoTime: formatIsoNow(),
    unixMs: Date.now()
  });
  saveState();
  broadcastSocialStates();
  broadcastAdminState();
  return { ok: true, oldHandle, newHandle: clean };
}

function buildFullBackupObject() {
  const chObj = {};
  for (const [k, arr] of channelHistory.entries()) {
    chObj[k] = (arr || []).slice(-MAX_CHANNEL_HISTORY).map((m) => ({
      ...m,
      file: m.file ? stripFileData(m.file) : null
    }));
  }
  const dmObj = {};
  for (const [k, arr] of dmHistory.entries()) {
    dmObj[k] = (arr || []).slice(-MAX_DM_HISTORY).map((m) => ({
      ...m,
      file: m.file ? stripFileData(m.file) : null
    }));
  }
  return {
    version: SERVER_VERSION,
    epoch: STATE_EPOCH,
    exportedAt: formatIsoNow(),
    state,
    channelHistory: chObj,
    dmHistory: dmObj
  };
}

function restoreFullBackupObject(backup, adminDevId) {
  if (!backup || typeof backup !== 'object' || !backup.state || typeof backup.state !== 'object') {
    return { ok: false, error: 'Ugyldig backup-fil.' };
  }
  const src = backup.state;
  const copyObj = (v, fallback) => (v && typeof v === 'object' && !Array.isArray(v)) ? JSON.parse(JSON.stringify(v)) : fallback;

  // Keep current active admin account & session alive across restore!
  const currentAdminAcc = adminDevId && state.accounts[adminDevId] ? JSON.parse(JSON.stringify(state.accounts[adminDevId])) : null;
  const currentAdminSessions = {};
  if (adminDevId) {
    for (const [tk, s] of Object.entries(state.sessions)) {
      if (s && s.accountId === adminDevId) currentAdminSessions[tk] = s;
    }
  }

  state.epoch = STATE_EPOCH;
  state.settings = { ...state.settings, ...copyObj(src.settings, {}) };
  state.updater = { ...state.updater, ...copyObj(src.updater, {}) };
  state.announcement = src.announcement && typeof src.announcement === 'object' ? JSON.parse(JSON.stringify(src.announcement)) : null;
  state.cooldowns = {
    global: Number(src.cooldowns && src.cooldowns.global) || 0,
    channels: copyObj(src.cooldowns && src.cooldowns.channels, {})
  };
  state.accounts = copyObj(src.accounts, {});
  state.sessions = { ...copyObj(src.sessions, {}), ...currentAdminSessions };
  state.handles = copyObj(src.handles, {});
  state.handleOwners = {};
  for (const [devId, h] of Object.entries(state.handles)) {
    if (typeof h === 'string' && h) state.handleOwners[h] = devId;
  }
  for (const [accId, acc] of Object.entries(state.accounts)) {
    if (acc && acc.handle) {
      state.handles[accId] = acc.handle;
      state.handleOwners[acc.handle] = accId;
    }
  }
  state.trustedDevices = copyObj(src.trustedDevices, {});
  state.verifiedDevices = copyObj(src.verifiedDevices, {});
  state.bannedDevices = copyObj(src.bannedDevices, {});
  state.mutedDevices = copyObj(src.mutedDevices, {});
  state.heartbeatOffDevices = copyObj(src.heartbeatOffDevices, {});
  state.knownDevices = copyObj(src.knownDevices, {});
  state.invites = copyObj(src.invites, {});
  state.friends = copyObj(src.friends, {});
  state.friendRequests = copyObj(src.friendRequests, {});
  state.customChannels = copyObj(src.customChannels, {});

  // Always guarantee verified Admin account & @kvartsbuen survive restore
  if (adminDevId && currentAdminAcc) {
    const prevOwner = state.handleOwners[ADMIN_HANDLE];
    if (prevOwner && prevOwner !== adminDevId && !state.accounts[adminDevId]) {
      // If backup already has @kvartsbuen under another accountId, keep backup's admin account AND remap current session
      for (const tk of Object.keys(currentAdminSessions)) {
        state.sessions[tk] = { ...currentAdminSessions[tk], accountId: prevOwner };
      }
    } else {
      if (prevOwner && prevOwner !== adminDevId) delete state.handles[prevOwner];
      state.accounts[adminDevId] = currentAdminAcc;
      state.handles[adminDevId] = ADMIN_HANDLE;
      state.handleOwners[ADMIN_HANDLE] = adminDevId;
      syncKnownDeviceFromAccount(currentAdminAcc);
    }
  }

  if (backup.channelHistory && typeof backup.channelHistory === 'object') {
    channelHistory.clear();
    for (const [ch, arr] of Object.entries(backup.channelHistory)) {
      if (Array.isArray(arr)) {
        channelHistory.set(ch, arr.slice(-MAX_CHANNEL_HISTORY).map((m) => ({
          ...m,
          file: m && m.file ? stripFileData(m.file) : null
        })));
      }
    }
  }
  if (backup.dmHistory && typeof backup.dmHistory === 'object') {
    dmHistory.clear();
    for (const [rk, arr] of Object.entries(backup.dmHistory)) {
      if (Array.isArray(arr)) {
        dmHistory.set(rk, arr.slice(-MAX_DM_HISTORY).map((m) => ({
          ...m,
          file: m && m.file ? stripFileData(m.file) : null
        })));
      }
    }
  }

  // Sync handles to currently connected clients
  for (const c of wss.clients) {
    if (c.meta && c.meta.deviceId && state.handles[c.meta.deviceId]) {
      c.meta.handle = state.handles[c.meta.deviceId];
    }
  }

  saveState();
  broadcastCooldowns();
  broadcastUpdaterAndAnnouncement();
  broadcastSocialStates();
  broadcastAdminState();

  const userCount = Object.keys(state.accounts).length || Object.keys(state.knownDevices).length;
  const chCount = Object.keys(state.customChannels).length;
  return { ok: true, userCount, chCount };
}

// Shared Console Command Runner (used by BOTH local server stdin AND Admin Panel Console!)
function executeConsoleCommand(rawLine) {
  const line = String(rawLine || '').trim();
  if (!line) return '';
  const parts = line.split(/\s+/);
  const cmd = parts[0].toLowerCase();
  const rest = line.slice(parts[0].length).trim();

  if (cmd === 'help' || cmd === '?') {
    return [
      'Kommandoer:',
      '  broadcast <melding>           - Send global kunngjøring til alle',
      '  warn <melding>                - Send rød/gul advarsel til alle',
      '  clear-banner                  - Fjern aktiv kunngjøring',
      '  update <versjon> [notater]    - Publiser ny versjon & varsle alle om oppdatering',
      '  minver <versjon>              - Sett minimumsversjon (eldre klienter får utdatert-popup)',
      '  force-update <on|off>         - Tving oppdaterings-popup for eldre versjoner',
      '  cooldown <kanal|global> <sek> - Sett slowmode/cooldown i sekunder (0 = av)',
      '  rename <@gammel|id> <@ny>     - Endre fast @brukernavn for en bruker',
      '  setpass <@bruker> <passord>   - Sett nytt passord for en bruker',
      '  deluser <@bruker|id>          - Slett en brukerkonto permanent',
      '  clear <kanal|*>               - Tøm meldingshistorikk i kanal',
      '  reload-all                    - Last inn nettsiden på nytt for alle',
      '  status                        - Vis serverstatus, online brukere og versjon'
    ].join('\n');
  }

  if (cmd === 'status') {
    const online = Array.from(wss.clients).filter((c) => c.meta && c.meta.status === 'approved');
    const names = online.map((c) => `${c.meta.user}${c.meta.handle ? '(@' + c.meta.handle + ')' : ''}[v${c.meta.clientVersion}]`).join(', ');
    return `Server v${SERVER_VERSION} | Online: ${online.length} (${names || 'ingen'}) | Kontoer: ${Object.keys(state.accounts).length} | Global cooldown: ${state.cooldowns.global}s`;
  }

  if (cmd === 'rename') {
    const targetQuery = (parts[1] || '').trim();
    const newHandle = (parts[2] || '').trim();
    if (!targetQuery || !newHandle) return 'Bruk: rename <@gammelt|deviceId> <@nytt>';
    const targetDev = findDeviceIdByQuery(targetQuery);
    if (!targetDev) return `Fant ingen bruker for "${targetQuery}".`;
    const res = renameUserPermanentHandle(targetDev, newHandle, 'KONSOLLE');
    return res.ok ? `Endret fast brukernavn: ${res.oldHandle ? '@' + res.oldHandle : '(ingen)'} -> @${res.newHandle}` : `Feil: ${res.error}`;
  }

  if (cmd === 'setpass') {
    const targetQuery = (parts[1] || '').trim();
    const newPass = parts.slice(2).join(' ').trim();
    if (!targetQuery || newPass.length < 6) return 'Bruk: setpass <@brukernavn> <nytt_passord_min_6_tegn>';
    const targetDev = findDeviceIdByQuery(targetQuery);
    const acc = targetDev ? state.accounts[targetDev] : null;
    if (!acc) return `Fant ingen konto for "${targetQuery}".`;
    const { salt, hash } = hashPassword(newPass);
    acc.passwordSalt = salt;
    acc.passwordHash = hash;
    saveState();
    return `Passord oppdatert for @${acc.handle}!`;
  }

  if (cmd === 'deluser') {
    const targetQuery = (parts[1] || '').trim();
    if (!targetQuery) return 'Bruk: deluser <@brukernavn|deviceId>';
    const targetDev = findDeviceIdByQuery(targetQuery);
    if (!targetDev) return `Fant ingen bruker for "${targetQuery}".`;
    const ok = purgeUserAccount(targetDev, 'KONSOLLE', true);
    return ok ? `Slettet bruker (${targetQuery}).` : 'Kan ikke slette denne kontoen (f.eks. Admin).';
  }

  if (cmd === 'broadcast' || cmd === 'say' || cmd === 'warn') {
    if (!rest) return 'Bruk: broadcast <melding>';
    state.announcement = {
      id: `ann-${Date.now()}`,
      text: rest.slice(0, 400),
      level: cmd === 'warn' ? 'warn' : 'info',
      createdAt: formatIsoNow()
    };
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return `Kunngjøring sendt til alle: "${state.announcement.text}"`;
  }

  if (cmd === 'clear-banner' || cmd === 'clearbanner') {
    state.announcement = null;
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return 'Aktiv kunngjøring fjernet.';
  }

  if (cmd === 'update') {
    const ver = (parts[1] || '').trim().replace(/^v/i, '');
    if (!ver) return 'Bruk: update <versjon> [endringslogg]  (f.eks. update 2.1.0 Nye emojis og fiks!)';
    const notes = line.slice(line.indexOf(parts[1]) + parts[1].length).trim();
    state.updater.latestVersion = ver.slice(0, 20);
    if (notes) state.updater.notes = notes.slice(0, 400);
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return `Oppdatering satt til v${state.updater.latestVersion}. Alle eldre klienter får nå oppdateringsvarsel!`;
  }

  if (cmd === 'minver') {
    const ver = (parts[1] || '').trim().replace(/^v/i, '');
    if (!ver) return 'Bruk: minver <versjon>  (f.eks. minver 2.0.0)';
    state.updater.minVersion = ver.slice(0, 20);
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return `Minimumsversjon satt til v${state.updater.minVersion}.`;
  }

  if (cmd === 'force-update') {
    const val = (parts[1] || '').toLowerCase();
    state.updater.forceModal = val === 'on' || val === 'true' || val === '1';
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return `Tvunget oppdateringsvindu: ${state.updater.forceModal ? 'PÅ' : 'AV'}.`;
  }

  if (cmd === 'cooldown' || cmd === 'slowmode') {
    const target = (parts[1] || '').trim().toLowerCase();
    const sec = Math.max(0, Math.min(300, parseInt(parts[2], 10) || 0));
    if (!target) return 'Bruk: cooldown <global|#general-1> <sekunder>';
    if (target === 'global' || target === 'all' || target === '*') {
      state.cooldowns.global = sec;
    } else {
      const slug = target.startsWith('#') ? target : '#' + target;
      if (sec === 0) delete state.cooldowns.channels[slug];
      else state.cooldowns.channels[slug] = sec;
    }
    saveState();
    broadcastCooldowns();
    broadcastAdminState();
    return `Cooldown for ${target} satt til ${sec}s.`;
  }

  if (cmd === 'clear') {
    const ch = (parts[1] || '*').trim().toLowerCase();
    if (ch === '*') {
      channelHistory.clear();
      for (let i = vault.length - 1; i >= 0; i--) {
        if (vault[i].type === 'chat' || (vault[i].scope === 'channel' && (vault[i].type === 'edit' || vault[i].type === 'delete'))) {
          vault.splice(i, 1);
        }
      }
      rewriteVaultFile();
    } else {
      channelHistory.delete(ch);
      for (let i = vault.length - 1; i >= 0; i--) {
        if (vault[i].channel === ch && (vault[i].type === 'chat' || vault[i].type === 'edit' || vault[i].type === 'delete')) {
          vault.splice(i, 1);
        }
      }
      rewriteVaultFile();
    }
    broadcastToAllApproved({ type: 'admin_notice', action: 'clear_chat', channel: ch });
    broadcastAdminState();
    return `Tømte historikk for ${ch}.`;
  }

  if (cmd === 'clear-all' || cmd === 'wipe-chats') {
    clearAllChatsAndDms();
    return 'Slettet ALLE meldinger i ALLE kanaler (offentlige + private) OG ALLE DM-er!';
  }

  if (cmd === 'reload-all' || cmd === 'reload') {
    broadcastToAllApproved({ type: 'reload_page', serverVersion: SERVER_VERSION });
    return 'Sendte oppdaterings-/reload-signal til alle tilkoblede nettlesere.';
  }

  return `Ukjent kommando: "${cmd}". Skriv "help" for liste.`;
}

function clearAllChatsAndDms() {
  channelHistory.clear();
  dmHistory.clear();
  for (let i = vault.length - 1; i >= 0; i--) {
    const t = vault[i] && vault[i].type;
    if (t === 'chat' || t === 'dm' || t === 'edit' || t === 'delete') {
      vault.splice(i, 1);
    }
  }
  rewriteVaultFile();
  broadcastToAllApproved({ type: 'admin_notice', action: 'clear_all_chats_and_dms' });
  sendToAdmins({ type: 'admin_vault_sync', records: vault.slice(-300) });
  broadcastAdminState();
}

function handleAdminCommand(adminWs, cmd) {
  const action = String(cmd.action || '');
  const targetDev = String(cmd.deviceId || '');
  const targetConn = String(cmd.connId || '');

  const findTargetSockets = () => {
    const list = [];
    for (const c of wss.clients) {
      if (!c.meta) continue;
      if ((targetConn && c.meta.connId === targetConn) || (targetDev && c.meta.deviceId === targetDev)) {
        list.push(c);
      }
    }
    return list;
  };

  if (action === 'request_state') {
    safeSend(adminWs, buildAdminStateSnapshot());
    return;
  }

  if (action === 'export_state') {
    safeSend(adminWs, {
      type: 'admin_state_backup',
      quiet: !!cmd.quiet,
      backup: buildFullBackupObject()
    });
    return;
  }

  if (action === 'restore_state') {
    const res = restoreFullBackupObject(cmd.backup, adminWs.meta.deviceId);
    if (res.ok) {
      safeSend(adminWs, {
        type: 'social_notice',
        text: `Server-data gjenopprettet (${res.userCount} brukere, ${res.chCount} kanaler)!`
      });
    } else {
      safeSend(adminWs, { type: 'social_notice', text: res.error });
    }
    return;
  }

  if (action === 'delete_user') {
    if (!targetDev || targetDev === adminWs.meta.deviceId) {
      safeSend(adminWs, { type: 'social_notice', text: 'Du kan ikke slette din egen Admin-konto.' });
      return;
    }
    const ok = purgeUserAccount(targetDev, adminWs.meta.user || ADMIN_HANDLE, true);
    safeSend(adminWs, {
      type: 'social_notice',
      text: ok ? 'Brukerkontoen ble slettet.' : 'Kunne ikke slette denne brukeren.'
    });
    return;
  }

  if (action === 'set_user_handle') {
    const res = renameUserPermanentHandle(targetDev, cmd.newHandle, adminWs.meta.user || ADMIN_HANDLE);
    safeSend(adminWs, {
      type: 'social_notice',
      text: res.ok
        ? `Endret fast brukernavn til @${res.newHandle}!`
        : res.error
    });
    return;
  }

  if (action === 'admin_set_password') {
    const acc = targetDev ? state.accounts[targetDev] : null;
    const nextPass = String(cmd.newPassword || '').trim();
    if (!acc) {
      safeSend(adminWs, { type: 'social_notice', text: 'Fant ingen konto for denne brukeren.' });
      return;
    }
    if (nextPass.length < 6 || nextPass.length > 128) {
      safeSend(adminWs, { type: 'social_notice', text: 'Passordet må være minst 6 tegn.' });
      return;
    }
    const { salt, hash } = hashPassword(nextPass);
    acc.passwordSalt = salt;
    acc.passwordHash = hash;
    saveState();
    safeSend(adminWs, { type: 'social_notice', text: `Nytt passord lagret for @${acc.handle}!` });
    return;
  }

  if (action === 'reload_all') {
    broadcastToAllApproved({ type: 'reload_page', serverVersion: SERVER_VERSION });
    return;
  }

  if (action === 'console_cmd') {
    const out = executeConsoleCommand(cmd.command || '');
    safeSend(adminWs, { type: 'admin_console_out', command: String(cmd.command || ''), text: out });
    return;
  }

  if (action === 'set_cooldown') {
    const target = String(cmd.channel || 'global').trim().toLowerCase();
    const sec = Math.max(0, Math.min(300, Math.round(Number(cmd.seconds) || 0)));
    if (target === 'global' || target === '*' || target === 'all') {
      state.cooldowns.global = sec;
    } else {
      const slug = target.startsWith('#') ? target : '#' + target;
      if (sec === 0) delete state.cooldowns.channels[slug];
      else state.cooldowns.channels[slug] = sec;
    }
    saveState();
    broadcastCooldowns();
    broadcastAdminState();
    return;
  }

  if (action === 'set_announcement') {
    const text = String(cmd.text || '').trim().slice(0, 400);
    const level = ['info', 'warn', 'update'].includes(cmd.level) ? cmd.level : 'info';
    if (!text) {
      state.announcement = null;
    } else {
      state.announcement = {
        id: `ann-${Date.now()}`,
        text,
        level,
        createdAt: formatIsoNow()
      };
    }
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return;
  }

  if (action === 'set_updater') {
    if (typeof cmd.latestVersion === 'string' && cmd.latestVersion.trim()) {
      state.updater.latestVersion = cmd.latestVersion.trim().replace(/^v/i, '').slice(0, 20);
    }
    if (typeof cmd.minVersion === 'string' && cmd.minVersion.trim()) {
      state.updater.minVersion = cmd.minVersion.trim().replace(/^v/i, '').slice(0, 20);
    }
    if (typeof cmd.notes === 'string') {
      state.updater.notes = cmd.notes.trim().slice(0, 400);
    }
    if (typeof cmd.downloadUrl === 'string' && cmd.downloadUrl.trim()) {
      state.updater.downloadUrl = cmd.downloadUrl.trim().slice(0, 300);
    }
    if (typeof cmd.driveUrl === 'string' && cmd.driveUrl.trim()) {
      state.updater.driveUrl = cmd.driveUrl.trim().slice(0, 300);
    }
    if (typeof cmd.forceModal === 'boolean') {
      state.updater.forceModal = cmd.forceModal;
    }
    saveState();
    broadcastUpdaterAndAnnouncement();
    broadcastAdminState();
    return;
  }

  if (action === 'reset_handle') {
    if (targetDev && state.handles[targetDev] && state.handles[targetDev] !== ADMIN_HANDLE) {
      const oldHandle = state.handles[targetDev];
      delete state.handles[targetDev];
      if (state.handleOwners[oldHandle] === targetDev) delete state.handleOwners[oldHandle];
      if (state.knownDevices[targetDev]) state.knownDevices[targetDev].handle = '';
      for (const sock of findTargetSockets()) {
        sock.meta.handle = '';
        safeSend(sock, { type: 'handle_reset', text: 'Brukernavnet ditt ble tilbakestilt. Velg et nytt @brukernavn.' });
      }
      saveState();
      broadcastSocialStates();
      broadcastAdminState();
    }
    return;
  }

  if (action === 'inspect_channel') {
    const slug = String(cmd.channel || '').trim().toLowerCase();
    const msgs = channelHistory.get(slug) || [];
    safeSend(adminWs, { type: 'admin_channel_msgs', channel: slug, messages: msgs });
    return;
  }

  if (action === 'inspect_dm') {
    const key = String(cmd.key || '').trim() || dmRoomKey(cmd.devA, cmd.devB);
    const msgs = dmHistory.get(key) || [];
    safeSend(adminWs, { type: 'admin_dm_msgs', key, messages: msgs });
    return;
  }

  if (action === 'delete_channel') {
    const slug = String(cmd.channel || '').trim().toLowerCase();
    if (state.customChannels[slug]) {
      delete state.customChannels[slug];
      channelHistory.delete(slug);
      if (state.cooldowns.channels) delete state.cooldowns.channels[slug];
      saveState();
      broadcastSocialStates();
      broadcastAdminState();
    }
    return;
  }

  if (action === 'approve_user') {
    if (targetDev) {
      const known = state.knownDevices[targetDev] || {};
      state.verifiedDevices[targetDev] = { deviceId: targetDev, fingerprint: known.fingerprint || targetDev.slice(0, 8), user: known.user || 'Bruker', addedAt: formatIsoNow() };
      delete state.bannedDevices[targetDev];
    }
    for (const sock of findTargetSockets()) {
      if (sock.meta.role === 'admin') continue;
      const newRole = state.trustedDevices[sock.meta.deviceId] ? 'trusted' : 'verified';
      admitClientSession(sock, newRole, '');
    }
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'trust_user') {
    const makeTrusted = cmd.trusted !== false;
    if (targetDev) {
      const known = state.knownDevices[targetDev] || {};
      if (makeTrusted) {
        state.trustedDevices[targetDev] = { deviceId: targetDev, fingerprint: known.fingerprint || targetDev.slice(0, 8), user: known.user || 'Bruker', addedAt: formatIsoNow() };
        delete state.bannedDevices[targetDev];
      } else {
        delete state.trustedDevices[targetDev];
        state.verifiedDevices[targetDev] = { deviceId: targetDev, fingerprint: known.fingerprint || targetDev.slice(0, 8), user: known.user || 'Bruker', addedAt: formatIsoNow() };
      }
    }
    for (const sock of findTargetSockets()) {
      if (sock.meta.role === 'admin') continue;
      if (sock.meta.status !== 'approved' && makeTrusted) {
        admitClientSession(sock, 'trusted', '');
      } else {
        sock.meta.role = makeTrusted ? 'trusted' : 'verified';
        pushConfigToClient(sock);
      }
    }
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'disconnect_user') {
    for (const sock of findTargetSockets()) {
      if (sock === adminWs) continue;
      safeSend(sock, { type: 'admin_notice', action: 'disconnect', text: 'Tilkoblingen ble avsluttet.' });
      sock.close();
    }
    broadcastAdminState();
    return;
  }

  if (action === 'ban_device') {
    const makeBanned = cmd.banned !== false;
    if (targetDev) {
      const known = state.knownDevices[targetDev] || {};
      if (makeBanned) {
        state.bannedDevices[targetDev] = { deviceId: targetDev, fingerprint: known.fingerprint || targetDev.slice(0, 8), user: known.user || 'Ukjent', addedAt: formatIsoNow() };
        delete state.trustedDevices[targetDev];
        delete state.verifiedDevices[targetDev];
        for (const [tk, s] of Object.entries(state.sessions)) {
          if (s && s.accountId === targetDev) delete state.sessions[tk];
        }
      } else {
        delete state.bannedDevices[targetDev];
      }
    }
    if (makeBanned) {
      for (const sock of findTargetSockets()) {
        if (sock === adminWs) continue;
        safeSend(sock, { type: 'auth_status', status: 'banned', text: 'Denne enheten har ikke tilgang.' });
        sock.close();
      }
    }
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'mute_device') {
    if (targetDev) {
      if (cmd.muted) state.mutedDevices[targetDev] = true;
      else delete state.mutedDevices[targetDev];
      for (const sock of findTargetSockets()) pushConfigToClient(sock);
      saveState();
      broadcastAdminState();
    }
    return;
  }

  if (action === 'set_user_heartbeat') {
    if (targetDev) {
      if (cmd.enabled === false) state.heartbeatOffDevices[targetDev] = true;
      else delete state.heartbeatOffDevices[targetDev];
      for (const sock of findTargetSockets()) pushConfigToClient(sock);
      saveState();
      broadcastAdminState();
    }
    return;
  }

  if (action === 'set_server_settings') {
    if (typeof cmd.heartbeatEnabled === 'boolean') state.settings.heartbeatEnabled = cmd.heartbeatEnabled;
    if (typeof cmd.heartbeatSec === 'number' && cmd.heartbeatSec >= 5 && cmd.heartbeatSec <= 600) state.settings.heartbeatSec = Math.round(cmd.heartbeatSec);
    if (['approval', 'invite', 'trusted_only', 'open'].includes(cmd.accessMode)) state.settings.accessMode = cmd.accessMode;
    if (typeof cmd.gifApiKey === 'string') {
      state.settings.gifApiKey = cmd.gifApiKey.trim().slice(0, 120);
      gifSearchCache.clear();
    }
    if (typeof cmd.webOnlyMode === 'boolean') {
      state.settings.webOnlyMode = cmd.webOnlyMode;
    }
    saveState();
    for (const c of wss.clients) pushConfigToClient(c);
    broadcastAdminState();
    return;
  }

  if (action === 'create_invite') {
    const rand = crypto.randomInt(1000, 9999);
    const prefix = cmd.autoTrust ? 'STJERNE' : 'CHAT';
    const code = `${prefix}-${rand}`;
    state.invites[code] = {
      code,
      label: cmd.autoTrust ? 'Klarert' : 'Standard',
      autoTrust: !!cmd.autoTrust,
      usesLeft: typeof cmd.maxUses === 'number' && cmd.maxUses > 0 ? Math.min(999, Math.round(cmd.maxUses)) : 1,
      createdAt: formatIsoNow()
    };
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'revoke_invite') {
    delete state.invites[String(cmd.code || '').toUpperCase()];
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'probe_ping') {
    const targets = (targetConn || targetDev) ? findTargetSockets() : Array.from(wss.clients);
    for (const sock of targets) {
      if (sock.meta && sock.meta.status === 'approved') safeSend(sock, { type: 'admin_notice', action: 'probe_ping' });
    }
    return;
  }

  if (action === 'clear_history') {
    const ch = String(cmd.channel || '*');
    if (ch === '*') {
      channelHistory.clear();
      for (let i = vault.length - 1; i >= 0; i--) {
        if (vault[i].type === 'chat' || (vault[i].scope === 'channel' && (vault[i].type === 'edit' || vault[i].type === 'delete'))) {
          vault.splice(i, 1);
        }
      }
      rewriteVaultFile();
    } else {
      channelHistory.delete(ch);
      for (let i = vault.length - 1; i >= 0; i--) {
        if (vault[i].channel === ch && (vault[i].type === 'chat' || vault[i].type === 'edit' || vault[i].type === 'delete')) {
          vault.splice(i, 1);
        }
      }
      rewriteVaultFile();
    }
    for (const c of wss.clients) {
      if (c.meta && c.meta.status === 'approved') safeSend(c, { type: 'admin_notice', action: 'clear_chat', channel: ch });
    }
    broadcastAdminState();
    return;
  }

  if (action === 'clear_all_chats_and_dms') {
    clearAllChatsAndDms();
    safeSend(adminWs, { type: 'social_notice', text: 'Slettet ALLE meldinger i ALLE kanaler og DM-er!' });
    return;
  }
}

setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    ws.ping();
  }
}, 40000);

// Interactive Server Console when running in a terminal (stdin)
if (process.stdin && process.stdin.isTTY) {
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout, prompt: 'chat-server> ' });
  rl.prompt();
  rl.on('line', (line) => {
    const out = executeConsoleCommand(line);
    if (out) console.log(out);
    rl.prompt();
  });
}

server.listen(PORT, () => {
  console.log(`Chat Smart Relay v${SERVER_VERSION} (v5) lytter på port ${PORT}`);
});
