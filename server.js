const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.1.0';
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
        } else if (rec.type === 'delete' && rec.msgId) {
          if (rec.scope === 'channel' && rec.channel) {
            const arr = channelHistory.get(rec.channel) || [];
            channelHistory.set(rec.channel, arr.filter((m) => m.msgId !== rec.msgId));
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
      const seen = new Set();
      let m;
      while ((m = urlRe.exec(normalized)) !== null && results.length < 24) {
        const fullUrl = m[0];
        const gifId = m[1];
        const fileSlug = m[2].replace(/\.gif$/i, '').replace(/[-_]+/g, ' ').trim();
        if (seen.has(gifId)) continue;
        seen.add(gifId);
        results.push({
          id: gifId,
          title: (fileSlug || q || 'Tenor GIF').slice(0, 60),
          preview: fullUrl,
          url: fullUrl
        });
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
