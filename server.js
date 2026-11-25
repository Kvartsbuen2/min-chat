const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.4.3';
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
const HISTORY_PAGE_SIZE = 20;  // Discord-style on-demand pagination (20 msgs/page!)
const VAULT_PAGE_SIZE = 40;    // Admin live log pagination (40 lines/page!)
const MAX_VAULT_MEMORY = 6000;
const MAX_CUSTOM_CHANNELS_PER_USER = 5;
const MAX_FILE_BYTES = 6 * 1024 * 1024; // Default 6 MB live relay only (admin configurable 1–50 MB!)
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

// v3.4.3: Canonical server master timestamp (Unix ms) so clients always render local time.
function msgUnixMs(m) {
  if (!m) return 0;
  const n = Number(m.unixMs);
  if (Number.isFinite(n) && n > 0) return Math.floor(n);
  if (m.isoTime) {
    const raw = String(m.isoTime).trim();
    const iso = raw.includes('T') ? raw : (raw.replace(' ', 'T') + 'Z');
    const parsed = Date.parse(iso);
    if (Number.isFinite(parsed) && parsed > 0) return parsed;
  }
  return 0;
}

function deviceTagFor(deviceId) {
  const clean = String(deviceId || '').toUpperCase().replace(/[^A-F0-9]/g, '');
  return clean ? '#' + clean.slice(0, 4) : '';
}

// v3.4.1: Per-IP registration throttle (in-memory; resets on restart).
const REGISTER_WINDOW_MS = 60 * 60 * 1000;
const REGISTER_MAX_PER_WINDOW = 20;
const registerHitsByIp = new Map();
function getRequestIp(req) {
  const forwarded = req.headers['x-forwarded-for'];
  const rawIp = (typeof forwarded === 'string' ? forwarded.split(',')[0].trim() : (req.socket && req.socket.remoteAddress)) || 'ukjent';
  return rawIp.replace(/^::ffff:/, '');
}
setInterval(() => {
  const now = Date.now();
  for (const [ip, hits] of registerHitsByIp) {
    if (!hits.some(t => now - t < REGISTER_WINDOW_MS)) registerHitsByIp.delete(ip);
  }
}, 10 * 60 * 1000).unref();

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
      error: `Visningsnavnet «${stripped}» er allerede @brukernavnet til en annen konto (@${norm}). Velg et annet visningsnavn — eller logg inn hvis @${norm} er din konto.`
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
  const isKnownGifHost = /(^|\.)(tenor\.com|giphy\.com|klipy\.com|imgur\.com|discordapp\.net|discordapp\.com|wikimedia\.org|redd\.it|ifunny\.co|getfn\.io|imgflip\.com)$/i.test(host);
  const isGifPath = /\.(gif|webp|mp4|webm)(\?.*)?$/i.test(parsedUrl.pathname);
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

function getMaxFileSizeMb() {
  const n = Number(state && state.settings && state.settings.maxFileSizeMb);
  if (Number.isFinite(n) && n >= 1 && n <= 50) return Math.round(n);
  return 6;
}
function getMaxFileBytes() {
  return getMaxFileSizeMb() * 1024 * 1024;
}

// Validates live file/image/video/audio attachment for transit ONLY
function sanitizeLiveAttachment(fileObj) {
  if (!fileObj || typeof fileObj !== 'object') return null;
  const maxBytes = getMaxFileBytes();
  const maxB64Len = Math.ceil(maxBytes * 1.45) + 4096;
  const data = typeof fileObj.data === 'string' ? fileObj.data : '';
  if (!data || data.length > maxB64Len) return null;
  const name = String(fileObj.name || 'fil').replace(/[<>:"/\\|?*\x00-\x1F]/g, '_').slice(0, 80) || 'fil';
  const size = typeof fileObj.size === 'number' && fileObj.size >= 0
    ? Math.min(maxBytes, Math.round(fileObj.size))
    : Math.round((data.length * 3) / 4);
  const mime = typeof fileObj.mime === 'string' ? fileObj.mime.slice(0, 64).toLowerCase() : '';
  const isImage = !!fileObj.isImage || mime.startsWith('image/') || /\.(png|jpe?g|gif|bmp|webp)$/i.test(name);
  const isVideo = !isImage && (!!fileObj.isVideo || mime.startsWith('video/') || /\.(mp4|webm|mov|m4v)$/i.test(name));
  const isAudio = !isImage && !isVideo && (!!fileObj.isAudio || mime.startsWith('audio/') || /\.(mp3|wav|ogg|m4a|flac|aac|opus)$/i.test(name));
  const hash = crypto.createHash('sha1').update(data).digest('hex').slice(0, 16);
  return { name, size, isImage, isVideo, isAudio, mime, hash, data };
}

// Strips binary data so server/DB NEVER stores images/videos/audio — ONLY lightweight reference!
function stripFileData(fileObj) {
  if (!fileObj) return null;
  const out = {
    name: fileObj.name,
    size: fileObj.size,
    isImage: !!fileObj.isImage,
    isVideo: !!fileObj.isVideo,
    isAudio: !!fileObj.isAudio
  };
  if (fileObj.mime) out.mime = String(fileObj.mime).slice(0, 64);
  if (fileObj.hash) out.hash = String(fileObj.hash).slice(0, 24);
  return out;
}

function sanitizeAvatarDataUrl(raw) {
  if (raw === '' || raw === null) return '';
  if (typeof raw !== 'string') return null;
  const s = raw.trim();
  if (!s) return '';
  if (s.length > 28 * 1024) return null; // Client downscales to 128x128 WebP/JPEG (~4-12 KB)
  if (!/^data:image\/(webp|jpeg|png);base64,[A-Za-z0-9+/=]+$/.test(s)) return null;
  return s;
}

const RANDOM_USER_COLORS = [
  '#FF6B6B', '#FF8E53', '#FFA726', '#FFD54F', '#AED581', '#4DB6AC',
  '#26C6DA', '#42A5F5', '#5C6BC0', '#7E57C2', '#AB47BC', '#EC407A',
  '#F06292', '#2ECC71', '#1ABC9C', '#E67E22', '#E74C3C', '#9B59B6',
  '#3498DB', '#00B894', '#FD79A8', '#6C5CE7', '#00CEC9', '#FDCB6E'
];
function randomUserColor() {
  return RANDOM_USER_COLORS[crypto.randomInt(0, RANDOM_USER_COLORS.length)];
}

function dmRoomKey(devA, devB) {
  return [String(devA || ''), String(devB || '')].sort().join('|');
}

function sanitizePoll(raw) {
  if (!raw || typeof raw !== 'object') return null;
  const question = String(raw.question || '').trim().slice(0, 160);
  if (!question) return null;
  const rawOpts = Array.isArray(raw.options) ? raw.options : [];
  const options = [];
  for (const o of rawOpts) {
    const txt = typeof o === 'string' ? o.trim() : (o && typeof o.text === 'string' ? o.text.trim() : '');
    if (txt) options.push({ text: txt.slice(0, 80), votes: [] });
    if (options.length >= 6) break;
  }
  if (options.length < 2) return null;
  return { question, options };
}

const state = {
  epoch: STATE_EPOCH,
  settings: {
    heartbeatEnabled: true,
    heartbeatSec: 30,
    accessMode: 'open', // open | approval | invite | trusted_only
    secretTrustedOnly: false,
    webOnlyMode: true,
    gifApiKey: '', // Optional KLIPY API key (Tenor web search works automatically without any key!)
    maxMsgsPerChannel: 0, // 0 = unlimited; >0 trims each channel/DM to latest N messages
    retentionDays: 0,     // 0 = never auto-delete; >0 deletes messages older than N days
    maxFileSizeMb: 6      // Admin-configurable global max live attachment size (1–50 MB)
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
  pins: {},           // scopeKey (#channel or dm:<rk>) -> [msgId, ...] (max 25)
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
const gifResolveCache = new Map();   // url -> { expiresAt, payload }
let nextSeq = 1;
let nextConnNum = 1;

// =============================================================================
// Permanent Cloud Storage (Upstash Redis REST — 100% Free, Zero Data Loss on Render!)
// Architecture: User -> Server RAM -> Users (instant live relay).
// Cloud DB is strictly separated into 3 clearly marked keys:
//   - minchat:v3:users  -> Accounts (scrypt-hashed passwords ONLY!), sessions, handles, friends, bans/mutes
//   - minchat:v3:config -> Settings, cooldowns, customChannels, invites, announcements, metrics
//   - minchat:v3:chats  -> Chat & DM messages, links, lightweight image hash references (0 B image bytes!)
// Free tier limits: 250 MB storage, 10 GB/month bandwidth.
// =============================================================================
const UPSTASH_URL = (process.env.UPSTASH_REDIS_REST_URL || process.env.KV_REST_API_URL || '').trim().replace(/\/+$/, '');
const UPSTASH_TOKEN = (process.env.UPSTASH_REDIS_REST_TOKEN || process.env.KV_REST_API_TOKEN || '').trim();
const CLOUD_USERS_KEY = 'minchat:v3:users';
const CLOUD_CONFIG_KEY = 'minchat:v3:config';
const CLOUD_CHATS_KEY = 'minchat:v3:chats';
const LEGACY_CLOUD_STATE_KEY = 'minchat:v3:state';
const LEGACY_CLOUD_HISTORY_KEY = 'minchat:v3:history';
const CLOUD_LIMIT_STORAGE_BYTES = 250 * 1024 * 1024;           // 250 MB
const CLOUD_LIMIT_MONTHLY_BW_BYTES = 10 * 1024 * 1024 * 1024;  // 10 GB / month
const CLOUD_SAVE_DEBOUNCE_MS = 10000;                          // 10s batching for minimal bandwidth!

function currentMonthKey() {
  const d = new Date();
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}`;
}

function ensureCloudMetrics() {
  const mk = currentMonthKey();
  const prev = (state.cloudMetrics && typeof state.cloudMetrics === 'object') ? state.cloudMetrics : {};
  if (!state.cloudMetrics || typeof state.cloudMetrics !== 'object' || state.cloudMetrics.monthKey !== mk) {
    state.cloudMetrics = {
      monthKey: mk,
      monthBytesSent: 0,
      monthBytesRecv: 0,
      monthCommands: 0,
      monthSyncs: 0,
      allTimeBytesSent: Number(prev.allTimeBytesSent) || Number(prev.monthBytesSent) || 0,
      allTimeBytesRecv: Number(prev.allTimeBytesRecv) || Number(prev.monthBytesRecv) || 0,
      allTimeCommands: Number(prev.allTimeCommands) || Number(prev.monthCommands) || 0,
      allTimeWsBytesOut: Number(prev.allTimeWsBytesOut) || 0,
      allTimeWsBytesIn: Number(prev.allTimeWsBytesIn) || 0,
      lastUsersBytes: Number(prev.lastUsersBytes) || 0,
      lastConfigBytes: Number(prev.lastConfigBytes) || 0,
      lastChatsBytes: Number(prev.lastChatsBytes) || Number(prev.lastHistoryBytes) || 0,
      lastRawUsersBytes: Number(prev.lastRawUsersBytes) || 0,
      lastRawConfigBytes: Number(prev.lastRawConfigBytes) || 0,
      lastRawChatsBytes: Number(prev.lastRawChatsBytes) || Number(prev.lastRawHistoryBytes) || 0
    };
  } else {
    if (typeof state.cloudMetrics.allTimeBytesSent !== 'number') state.cloudMetrics.allTimeBytesSent = Number(prev.monthBytesSent) || 0;
    if (typeof state.cloudMetrics.allTimeBytesRecv !== 'number') state.cloudMetrics.allTimeBytesRecv = Number(prev.monthBytesRecv) || 0;
    if (typeof state.cloudMetrics.allTimeCommands !== 'number') state.cloudMetrics.allTimeCommands = Number(prev.monthCommands) || 0;
    if (typeof state.cloudMetrics.allTimeWsBytesOut !== 'number') state.cloudMetrics.allTimeWsBytesOut = 0;
    if (typeof state.cloudMetrics.allTimeWsBytesIn !== 'number') state.cloudMetrics.allTimeWsBytesIn = 0;
    if (typeof state.cloudMetrics.lastUsersBytes !== 'number') state.cloudMetrics.lastUsersBytes = 0;
    if (typeof state.cloudMetrics.lastConfigBytes !== 'number') state.cloudMetrics.lastConfigBytes = 0;
    if (typeof state.cloudMetrics.lastChatsBytes !== 'number') state.cloudMetrics.lastChatsBytes = Number(prev.lastHistoryBytes) || 0;
  }
  return state.cloudMetrics;
}

const cloudStorage = {
  enabled: !!(UPSTASH_URL && UPSTASH_TOKEN),
  connected: false,
  provider: 'upstash-redis',
  lastLoadedIso: '',
  lastSavedIso: '',
  lastError: ''
};
let cloudSaveTimer = null;
let cloudSaveInFlight = null;
let cloudStateDirty = false;
let cloudHistoryDirty = false;
let cloudBootReady = false;

function encodeCloudPayload(obj) {
  const rawStr = JSON.stringify(obj);
  const rawBytes = Buffer.byteLength(rawStr, 'utf8');
  const gz = zlib.gzipSync(Buffer.from(rawStr, 'utf8'), { level: 6 });
  const encoded = 'gz:' + gz.toString('base64');
  return { encoded, storedBytes: Buffer.byteLength(encoded, 'utf8'), rawBytes };
}

function decodeCloudPayload(str) {
  if (typeof str !== 'string' || !str) return null;
  if (str.startsWith('gz:')) {
    const buf = zlib.gunzipSync(Buffer.from(str.slice(3), 'base64'));
    return JSON.parse(buf.toString('utf8'));
  }
  return JSON.parse(str);
}

function upstashPost(endpointPath, bodyObj, cmdCount = 1) {
  return new Promise((resolve, reject) => {
    if (!UPSTASH_URL || !UPSTASH_TOKEN) return reject(new Error('Upstash not configured'));
    let parsed;
    try { parsed = new URL(UPSTASH_URL + endpointPath); } catch (e) { return reject(e); }
    const data = JSON.stringify(bodyObj);
    const reqBytes = Buffer.byteLength(data, 'utf8');
    const mod = parsed.protocol === 'http:' ? http : https;
    const req = mod.request({
      hostname: parsed.hostname,
      port: parsed.port || (parsed.protocol === 'http:' ? 80 : 443),
      path: parsed.pathname + parsed.search,
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${UPSTASH_TOKEN}`,
        'Content-Type': 'application/json',
        'Content-Length': reqBytes
      },
      timeout: 8000
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        const respBuf = Buffer.concat(chunks);
        const txt = respBuf.toString('utf8');
        const m = ensureCloudMetrics();
        m.monthBytesSent += reqBytes;
        m.monthBytesRecv += respBuf.length;
        m.monthCommands += cmdCount;
        m.allTimeBytesSent += reqBytes;
        m.allTimeBytesRecv += respBuf.length;
        m.allTimeCommands += cmdCount;
        if (res.statusCode >= 400) return reject(new Error(`Upstash HTTP ${res.statusCode}: ${txt.slice(0, 160)}`));
        try { resolve(JSON.parse(txt)); } catch (e) { reject(e); }
      });
    });
    req.on('timeout', () => { req.destroy(); reject(new Error('Upstash timeout')); });
    req.on('error', reject);
    req.write(data);
    req.end();
  });
}

// Separate Users & scrypt-hashed credentials payload (isolated from chat messages!)
function buildUsersSnapshot() {
  return {
    section: 'users_auth_hashed',
    passwordHashAlgo: 'scrypt-64byte-random-salt',
    epoch: STATE_EPOCH,
    accounts: state.accounts,
    sessions: state.sessions,
    handles: state.handles,
    handleOwners: state.handleOwners,
    trustedDevices: state.trustedDevices,
    verifiedDevices: state.verifiedDevices,
    bannedDevices: state.bannedDevices,
    mutedDevices: state.mutedDevices,
    heartbeatOffDevices: state.heartbeatOffDevices,
    knownDevices: state.knownDevices,
    friends: state.friends,
    friendRequests: state.friendRequests
  };
}

// Separate Server Config & Channels payload
function buildConfigSnapshot() {
  return {
    section: 'server_config',
    epoch: STATE_EPOCH,
    settings: state.settings,
    updater: state.updater,
    announcement: state.announcement,
    cooldowns: state.cooldowns,
    pins: state.pins,
    invites: state.invites,
    customChannels: state.customChannels,
    cloudMetrics: ensureCloudMetrics()
  };
}

// Separate Chat Messages & Links payload (ZERO passwords, ZERO image bytes!)
function buildCompactHistorySnapshot() {
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
  const compactVault = vault.slice(-400).map((r) => (r && r.file ? { ...r, file: stripFileData(r.file) } : r));
  return {
    section: 'chats_and_links_only',
    epoch: STATE_EPOCH,
    nextSeq,
    channelHistory: chObj,
    dmHistory: dmObj,
    vault: compactVault
  };
}

function buildCloudStatusForAdmin() {
  const m = ensureCloudMetrics();
  const usersBytes = m.lastUsersBytes || 0;
  const configBytes = m.lastConfigBytes || 0;
  const chatsBytes = m.lastChatsBytes || 0;
  const totalStoredBytes = usersBytes + configBytes + chatsBytes;
  const totalRawBytes = (m.lastRawUsersBytes || usersBytes) + (m.lastRawConfigBytes || configBytes) + (m.lastRawChatsBytes || chatsBytes);
  const monthTotalBytes = (m.monthBytesSent || 0) + (m.monthBytesRecv || 0);
  const allTimeTotalBytes = (m.allTimeBytesSent || 0) + (m.allTimeBytesRecv || 0);
  const allTimeWsTotalBytes = (m.allTimeWsBytesOut || 0) + (m.allTimeWsBytesIn || 0);
  let totalMessages = 0;
  let totalImageRefs = 0;
  for (const arr of channelHistory.values()) {
    totalMessages += arr.length;
    for (const msg of arr) if (msg && msg.file && msg.file.isImage) totalImageRefs++;
  }
  for (const arr of dmHistory.values()) {
    totalMessages += arr.length;
    for (const msg of arr) if (msg && msg.file && msg.file.isImage) totalImageRefs++;
  }
  return {
    ...cloudStorage,
    monthKey: m.monthKey,
    storageLimitBytes: CLOUD_LIMIT_STORAGE_BYTES,
    monthlyBwLimitBytes: CLOUD_LIMIT_MONTHLY_BW_BYTES,
    keys: { users: CLOUD_USERS_KEY, config: CLOUD_CONFIG_KEY, chats: CLOUD_CHATS_KEY },
    usersBytes,
    configBytes,
    chatsBytes,
    totalStoredBytes,
    totalRawBytes,
    monthBytesSent: m.monthBytesSent || 0,
    monthBytesRecv: m.monthBytesRecv || 0,
    monthTotalBytes,
    monthCommands: m.monthCommands || 0,
    monthSyncs: m.monthSyncs || 0,
    allTimeBytesSent: m.allTimeBytesSent || 0,
    allTimeBytesRecv: m.allTimeBytesRecv || 0,
    allTimeTotalBytes,
    allTimeCommands: m.allTimeCommands || 0,
    allTimeWsBytesOut: m.allTimeWsBytesOut || 0,
    allTimeWsBytesIn: m.allTimeWsBytesIn || 0,
    allTimeWsTotalBytes,
    totalAccounts: Object.keys(state.accounts).length,
    totalMessages,
    totalImageRefs,
    passwordHashAlgo: 'scrypt (salted)',
    debounceSec: Math.round(CLOUD_SAVE_DEBOUNCE_MS / 1000)
  };
}

async function flushCloudSaveNow(forceAll = false) {
  if (!cloudStorage.enabled) return;
  if (cloudSaveTimer) { clearTimeout(cloudSaveTimer); cloudSaveTimer = null; }
  if (forceAll) { cloudStateDirty = true; cloudHistoryDirty = true; }
  if (!cloudStateDirty && !cloudHistoryDirty) return;
  if (cloudSaveInFlight) return cloudSaveInFlight;

  const saveStateNow = cloudStateDirty;
  const saveHistoryNow = cloudHistoryDirty;
  cloudStateDirty = false;
  cloudHistoryDirty = false;

  cloudSaveInFlight = (async () => {
    try {
      const m = ensureCloudMetrics();
      const cmds = [];
      if (saveHistoryNow) {
        const chatsEnc = encodeCloudPayload(buildCompactHistorySnapshot());
        m.lastChatsBytes = chatsEnc.storedBytes;
        m.lastRawChatsBytes = chatsEnc.rawBytes;
        cmds.push(['SET', CLOUD_CHATS_KEY, chatsEnc.encoded]);
      }
      if (saveStateNow) {
        const usersEnc = encodeCloudPayload(buildUsersSnapshot());
        m.lastUsersBytes = usersEnc.storedBytes;
        m.lastRawUsersBytes = usersEnc.rawBytes;
        cmds.push(['SET', CLOUD_USERS_KEY, usersEnc.encoded]);

        const cfgEnc = encodeCloudPayload(buildConfigSnapshot());
        m.lastConfigBytes = cfgEnc.storedBytes;
        m.lastRawConfigBytes = cfgEnc.rawBytes;
        cmds.push(['SET', CLOUD_CONFIG_KEY, cfgEnc.encoded]);
      }
      if (cmds.length > 0) {
        await upstashPost('/pipeline', cmds, cmds.length);
        m.monthSyncs += 1;
        cloudStorage.connected = true;
        cloudStorage.lastSavedIso = formatIsoNow();
        cloudStorage.lastError = '';
      }
    } catch (err) {
      cloudStorage.lastError = String((err && err.message) || err || 'Ukjent feil').slice(0, 180);
      if (saveStateNow) cloudStateDirty = true;
      if (saveHistoryNow) cloudHistoryDirty = true;
    } finally {
      cloudSaveInFlight = null;
      if (cloudStateDirty || cloudHistoryDirty) {
        scheduleCloudSave(cloudStateDirty, cloudHistoryDirty, CLOUD_SAVE_DEBOUNCE_MS);
      }
    }
  })();
  return cloudSaveInFlight;
}

function scheduleCloudSave(markState = true, markHistory = false, delayMs = CLOUD_SAVE_DEBOUNCE_MS) {
  if (markState) cloudStateDirty = true;
  if (markHistory) cloudHistoryDirty = true;
  if (!cloudStorage.enabled || !cloudBootReady) return;
  if (cloudSaveTimer) return; // Keep existing batch timer so active chat flushes every 10s!
  cloudSaveTimer = setTimeout(() => {
    cloudSaveTimer = null;
    flushCloudSaveNow(false);
  }, delayMs);
}

function applySavedStateFields(saved) {
  if (!saved || typeof saved !== 'object') return;
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
  if (saved.pins && typeof saved.pins === 'object') Object.assign(state.pins, saved.pins);
  if (saved.friends) Object.assign(state.friends, saved.friends);
  if (saved.friendRequests) Object.assign(state.friendRequests, saved.friendRequests);
  if (saved.customChannels) Object.assign(state.customChannels, saved.customChannels);
  if (saved.cloudMetrics && typeof saved.cloudMetrics === 'object') {
    const curM = ensureCloudMetrics();
    const sameMonth = saved.cloudMetrics.monthKey === currentMonthKey();
    state.cloudMetrics = {
      ...curM,
      ...saved.cloudMetrics,
      monthKey: currentMonthKey(),
      monthBytesSent: (sameMonth ? (Number(saved.cloudMetrics.monthBytesSent) || 0) : 0) + curM.monthBytesSent,
      monthBytesRecv: (sameMonth ? (Number(saved.cloudMetrics.monthBytesRecv) || 0) : 0) + curM.monthBytesRecv,
      monthCommands: (sameMonth ? (Number(saved.cloudMetrics.monthCommands) || 0) : 0) + curM.monthCommands,
      allTimeBytesSent: (Number(saved.cloudMetrics.allTimeBytesSent) || Number(saved.cloudMetrics.monthBytesSent) || 0) + curM.allTimeBytesSent,
      allTimeBytesRecv: (Number(saved.cloudMetrics.allTimeBytesRecv) || Number(saved.cloudMetrics.monthBytesRecv) || 0) + curM.allTimeBytesRecv,
      allTimeCommands: (Number(saved.cloudMetrics.allTimeCommands) || Number(saved.cloudMetrics.monthCommands) || 0) + curM.allTimeCommands,
      allTimeWsBytesOut: (Number(saved.cloudMetrics.allTimeWsBytesOut) || 0) + curM.allTimeWsBytesOut,
      allTimeWsBytesIn: (Number(saved.cloudMetrics.allTimeWsBytesIn) || 0) + curM.allTimeWsBytesIn
    };
  }
}

function applySavedChatsPayload(h) {
  if (!h || h.epoch !== STATE_EPOCH) return;
  if (typeof h.nextSeq === 'number' && h.nextSeq > nextSeq) nextSeq = h.nextSeq;
  if (h.channelHistory && typeof h.channelHistory === 'object') {
    channelHistory.clear();
    for (const [ch, arr] of Object.entries(h.channelHistory)) {
      if (Array.isArray(arr)) channelHistory.set(ch, arr.slice(-MAX_CHANNEL_HISTORY));
    }
  }
  if (h.dmHistory && typeof h.dmHistory === 'object') {
    dmHistory.clear();
    for (const [rk, arr] of Object.entries(h.dmHistory)) {
      if (Array.isArray(arr)) dmHistory.set(rk, arr.slice(-MAX_DM_HISTORY));
    }
  }
  if (Array.isArray(h.vault)) {
    vault.length = 0;
    for (const r of h.vault.slice(-MAX_VAULT_MEMORY)) {
      vault.push(r);
      if (typeof r.seq === 'number' && r.seq >= nextSeq) nextSeq = r.seq + 1;
    }
  }
}

async function loadCloudStateOnBoot() {
  ensureCloudMetrics();
  if (!cloudStorage.enabled) {
    cloudBootReady = true;
    return;
  }
  try {
    // Read separated keys (users, config, chats) + legacy keys for seamless zero-data-loss migration!
    const res = await upstashPost('/pipeline', [
      ['GET', CLOUD_USERS_KEY],
      ['GET', CLOUD_CONFIG_KEY],
      ['GET', CLOUD_CHATS_KEY],
      ['GET', LEGACY_CLOUD_STATE_KEY],
      ['GET', LEGACY_CLOUD_HISTORY_KEY]
    ], 5);
    cloudStorage.connected = true;
    cloudStorage.lastError = '';
    const getStr = (i) => (Array.isArray(res) && res[i] && typeof res[i].result === 'string' ? res[i].result : '');
    const rawUsers = getStr(0);
    const rawConfig = getStr(1);
    const rawChats = getStr(2);
    const rawLegacyState = getStr(3);
    const rawLegacyHist = getStr(4);

    let loadedAny = false;
    let needsMigrationToSplitKeys = false;

    if (rawUsers || rawConfig) {
      if (rawUsers) {
        const u = decodeCloudPayload(rawUsers);
        if (u && u.epoch === STATE_EPOCH) { applySavedStateFields(u); loadedAny = true; }
      }
      if (rawConfig) {
        const c = decodeCloudPayload(rawConfig);
        if (c && c.epoch === STATE_EPOCH) { applySavedStateFields(c); loadedAny = true; }
      }
      const m = ensureCloudMetrics();
      if (rawUsers) m.lastUsersBytes = Buffer.byteLength(rawUsers, 'utf8');
      if (rawConfig) m.lastConfigBytes = Buffer.byteLength(rawConfig, 'utf8');
    } else if (rawLegacyState) {
      const legacy = decodeCloudPayload(rawLegacyState);
      if (legacy && legacy.epoch === STATE_EPOCH) {
        applySavedStateFields(legacy);
        loadedAny = true;
        needsMigrationToSplitKeys = true;
      }
    }

    const chatsRawToLoad = rawChats || rawLegacyHist;
    if (loadedAny && chatsRawToLoad) {
      const h = decodeCloudPayload(chatsRawToLoad);
      applySavedChatsPayload(h);
      const m = ensureCloudMetrics();
      m.lastChatsBytes = Buffer.byteLength(chatsRawToLoad, 'utf8');
      if (!rawChats && rawLegacyHist) needsMigrationToSplitKeys = true;
    }

    if (compareVersions(SERVER_VERSION, state.updater.latestVersion) > 0) {
      state.updater.latestVersion = SERVER_VERSION;
    }
    if (loadedAny) cloudStorage.lastLoadedIso = formatIsoNow();

    cloudBootReady = true;
    if (loadedAny) {
      try {
        fs.mkdirSync(DATA_DIR, { recursive: true });
        fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8');
        const content = vault.length ? vault.map((r) => JSON.stringify(r)).join('\n') + '\n' : '';
        fs.writeFileSync(VAULT_FILE, content, 'utf8');
      } catch { }
      if (needsMigrationToSplitKeys) {
        await flushCloudSaveNow(true);
        console.log('Migrerte sky-lagring sømløst til adskilte nøkler (users / config / chats).');
      }
      console.log(`Sky-lagring (Upstash Redis) lastet: ${Object.keys(state.accounts).length} kontoer, ${Object.keys(state.customChannels).length} private kanaler.`);
    } else if (Object.keys(state.accounts).length > 0) {
      await flushCloudSaveNow(true);
      console.log('Sky-lagring (Upstash Redis) initialisert fra lokal tilstand.');
    } else {
      console.log('Sky-lagring (Upstash Redis) tilkoblet (klar for ny data).');
    }
  } catch (err) {
    cloudStorage.connected = false;
    cloudStorage.lastError = String((err && err.message) || err || 'Tilkoblingsfeil').slice(0, 180);
    cloudBootReady = true;
    console.error('Sky-lagring (Upstash Redis) feilet ved oppstart:', cloudStorage.lastError);
  }
}

function saveState() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8');
  } catch { }
  scheduleCloudSave(true, false);
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

function getAvatarFor(accountId) {
  if (!accountId || !state.accounts[accountId]) return '';
  return typeof state.accounts[accountId].avatar === 'string' ? state.accounts[accountId].avatar : '';
}

function getBioFor(accountId) {
  if (!accountId || !state.accounts[accountId]) return '';
  return typeof state.accounts[accountId].bio === 'string' ? state.accounts[accountId].bio : '';
}

function publicAccountSummary(acc) {
  if (!acc) return null;
  return {
    accountId: acc.accountId,
    deviceTag: deviceTagFor(acc.accountId),
    handle: acc.handle,
    user: acc.displayName,
    color: acc.color || '#3498DB',
    avatar: typeof acc.avatar === 'string' ? acc.avatar : '',
    bio: typeof acc.bio === 'string' ? acc.bio : '',
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
    color: /^#[0-9A-Fa-f]{6}$/.test(color) ? color : randomUserColor(),
    avatar: '',
    bio: '',
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
  if (saved.pins && typeof saved.pins === 'object') Object.assign(state.pins, saved.pins);
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

// Optional Render env var: pre-seed @kvartsbuen with ADMIN_PASSWORD if configured (runs after cloud load!)
function ensureAdminPasswordSeed() {
  if (process.env.ADMIN_PASSWORD && process.env.ADMIN_PASSWORD.length >= 6 && !state.handleOwners[ADMIN_HANDLE]) {
    createAccount({
      handle: ADMIN_HANDLE,
      displayName: 'Kvartsbuen',
      password: process.env.ADMIN_PASSWORD,
      color: '#2ECC71',
      role: 'admin'
    });
  }
}

function appendVaultRecord(rec) {
  const metaRec = rec.file ? { ...rec, file: stripFileData(rec.file) } : rec;
  vault.push(metaRec);
  if (vault.length > MAX_VAULT_MEMORY) vault.shift();
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    fs.appendFileSync(VAULT_FILE, JSON.stringify(metaRec) + '\n', 'utf8');
  } catch { }
  scheduleCloudSave(false, true);
  sendToAdmins({ type: 'admin_log', record: metaRec });
}

function rewriteVaultFile() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const content = vault.length ? vault.map((r) => JSON.stringify(r)).join('\n') + '\n' : '';
    fs.writeFileSync(VAULT_FILE, content, 'utf8');
  } catch { }
  scheduleCloudSave(false, true);
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

function isSafeExternalGifUrl(rawUrl) {
  if (typeof rawUrl !== 'string') return null;
  let parsed;
  try { parsed = new URL(rawUrl.trim()); } catch { return null; }
  if (parsed.protocol !== 'https:') return null;
  const h = parsed.hostname.toLowerCase();
  if (!h || h === 'localhost' || h.endsWith('.local') || h.endsWith('.internal')) return null;
  if (/^(127\.|10\.|192\.168\.|169\.254\.|0\.|172\.(1[6-9]|2\d|3[0-1])\.)/.test(h)) return null;
  if (h.startsWith('[') || h.includes(':')) return null;
  return parsed;
}

function extractMetaContent(html, propOrName) {
  const re1 = new RegExp(`<meta[^>]+(?:property|name)=["']${propOrName}["'][^>]+content=["']([^"']+)["']`, 'i');
  const m1 = html.match(re1);
  if (m1) return m1[1];
  const re2 = new RegExp(`<meta[^>]+content=["']([^"']+)["'][^>]+(?:property|name)=["']${propOrName}["']`, 'i');
  const m2 = html.match(re2);
  return m2 ? m2[1] : '';
}

async function resolveGifUrl(rawUrl) {
  const parsed = isSafeExternalGifUrl(rawUrl);
  if (!parsed) return { ok: false, error: 'Ugyldig https:// lenke.' };
  const cleanUrl = parsed.toString().slice(0, 500);

  const cached = gifResolveCache.get(cleanUrl);
  if (cached && cached.expiresAt > Date.now()) return cached.payload;

  // Direct GIF/WebP/MP4/WebM URL
  if (/\.(gif|webp|mp4|webm)$/i.test(parsed.pathname)) {
    const fileSlug = parsed.pathname.split('/').pop().replace(/\.(gif|webp|mp4|webm)$/i, '').replace(/[-_]+/g, ' ').trim();
    const gif = sanitizeGifObj({ url: cleanUrl, preview: cleanUrl, title: fileSlug || 'GIF' });
    if (!gif) return { ok: false, error: 'Lenken støttes ikke.' };
    const payload = { ok: true, gif };
    if (gifResolveCache.size > 150) gifResolveCache.clear();
    gifResolveCache.set(cleanUrl, { expiresAt: Date.now() + 10 * 60 * 1000, payload });
    return payload;
  }

  // Page URL (iFunny, Tenor, Giphy, Imgur, etc.) — extract real animated media URL!
  try {
    const html = await httpsGetText(cleanUrl);
    const normalized = html.replace(/\\u002F/gi, '/').replace(/\\\//g, '/').replace(/&amp;/g, '&');
    const titleRaw = extractMetaContent(normalized, 'og:title')
      || (normalized.match(/<title[^>]*>([^<]+)<\/title>/i)?.[1] || '')
      || 'GIF';
    const title = titleRaw.replace(/\s*[-|]\s*(iFunny|Tenor|GIPHY|Imgur).*$/i, '').trim().slice(0, 80) || 'GIF';

    const ogVideo = extractMetaContent(normalized, 'og:video:secure_url')
      || extractMetaContent(normalized, 'og:video:url')
      || extractMetaContent(normalized, 'og:video')
      || extractMetaContent(normalized, 'twitter:player:stream');
    const ogImage = extractMetaContent(normalized, 'og:image:secure_url')
      || extractMetaContent(normalized, 'og:image')
      || extractMetaContent(normalized, 'twitter:image');

    let mediaUrl = '';
    if (ogVideo && /^https:\/\/.+\.(mp4|webm|gif)(\?.*)?$/i.test(ogVideo)) {
      mediaUrl = ogVideo;
    }
    if (!mediaUrl) {
      // Check for direct animated GIF/MP4/WebM links in page body (e.g. iFunny img.getfn.io/*.mp4, Tenor media*.tenor.com/*.gif)
      const candidates = [
        normalized.match(/https:\/\/img\.getfn\.io\/images\/[A-Za-z0-9_.-]+\.(?:mp4|gif)/i)?.[0],
        normalized.match(/https:\/\/media[0-9]?\.tenor\.com\/(?:m\/)?[A-Za-z0-9_-]{8,30}\/[A-Za-z0-9_.-]+\.gif/i)?.[0],
        normalized.match(/https:\/\/media[0-9]?\.giphy\.com\/media\/[^\s"'<>\\]+\.gif/i)?.[0],
        normalized.match(/https:\/\/i\.imgur\.com\/[A-Za-z0-9]+\.(?:mp4|gif)/i)?.[0],
        normalized.match(/https:\/\/[^\s"'<>\\]+\.(?:gif|mp4|webm)(?:\?[^\s"'<>\\]*)?/i)?.[0]
      ].filter(Boolean);
      mediaUrl = candidates[0] || '';
    }
    if (!mediaUrl && ogImage && /^https:\/\//i.test(ogImage)) {
      mediaUrl = ogImage;
    }

    const previewUrl = (ogImage && /^https:\/\//i.test(ogImage)) ? ogImage : mediaUrl;
    const gif = sanitizeGifObj({ url: mediaUrl, preview: previewUrl, title });
    if (!gif) {
      return { ok: false, error: 'Fant ingen GIF eller video på denne lenken.' };
    }
    const payload = { ok: true, gif };
    if (gifResolveCache.size > 150) gifResolveCache.clear();
    gifResolveCache.set(cleanUrl, { expiresAt: Date.now() + 10 * 60 * 1000, payload });
    return payload;
  } catch {
    return { ok: false, error: 'Kunne ikke hente GIF fra denne lenken.' };
  }
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

    // v3.4.1: Safety net against accidental / spam account creation (per IP).
    const regIp = getRequestIp(req);
    const regNow = Date.now();
    const regHits = (registerHitsByIp.get(regIp) || []).filter(t => regNow - t < REGISTER_WINDOW_MS);
    const regIsAdminClaim = sanitizeHandle(body.username, true) === ADMIN_HANDLE;
    if (!regIsAdminClaim && regHits.length >= REGISTER_MAX_PER_WINDOW) {
      const waitMin = Math.max(1, Math.ceil((REGISTER_WINDOW_MS - (regNow - regHits[0])) / 60000));
      sendJsonRes(res, 429, {
        ok: false,
        error: `Det er laget ${regHits.length} nye kontoer fra denne tilkoblingen nylig. Logg inn på en konto du allerede har, eller vent ca. ${waitMin} min.`
      });
      return;
    }

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
    regHits.push(regNow);
    registerHitsByIp.set(regIp, regHits);
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

  // --- Tenor / Klipy GIF Search Proxy & Page-Link Resolver ---
  if (reqPath === '/api/gifs' && req.method === 'GET') {
    const q = parsedUrl.searchParams.get('q') || '';
    const data = await searchTenorOrKlipyGifs(q);
    sendJsonRes(res, 200, data);
    return;
  }

  if (reqPath === '/api/gif-resolve' && req.method === 'GET') {
    const targetUrl = parsedUrl.searchParams.get('url') || '';
    const data = await resolveGifUrl(targetUrl);
    sendJsonRes(res, data.ok ? 200 : 400, data);
    return;
  }

  if (reqPath === '/api/link-preview' && req.method === 'GET') {
    const targetUrl = parsedUrl.searchParams.get('url') || '';
    const data = await fetchLinkPreview(targetUrl);
    sendJsonRes(res, data.ok ? 200 : 400, data);
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

const linkPreviewCache = new Map(); // url -> { ts, data }
function isBlockedPreviewHost(hostname) {
  const h = String(hostname || '').toLowerCase().trim();
  if (!h || h === 'localhost' || h === '::1' || h.endsWith('.local') || h.endsWith('.internal')) return true;
  if (/^127\.|^10\.|^192\.168\.|^169\.254\.|^0\./.test(h)) return true;
  if (/^172\.(1[6-9]|2\d|3[01])\./.test(h)) return true;
  return false;
}
function decodeHtmlEntities(s) {
  return String(s || '')
    .replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&#x27;/g, "'")
    .replace(/\s+/g, ' ').trim();
}
function extractYouTubeId(u) {
  try {
    const host = u.hostname.toLowerCase().replace(/^www\./, '');
    if (host === 'youtu.be') {
      const id = u.pathname.replace(/^\/+/, '').split('/')[0];
      return /^[A-Za-z0-9_-]{11}$/.test(id) ? id : '';
    }
    if (host === 'youtube.com' || host === 'm.youtube.com') {
      if (u.pathname === '/watch') {
        const id = u.searchParams.get('v') || '';
        return /^[A-Za-z0-9_-]{11}$/.test(id) ? id : '';
      }
      const m = u.pathname.match(/^\/(shorts|embed|live)\/([A-Za-z0-9_-]{11})/);
      if (m) return m[2];
    }
  } catch {}
  return '';
}
async function fetchLinkPreview(rawUrl) {
  const clean = String(rawUrl || '').trim();
  if (!clean || clean.length > 1024) return { ok: false, error: 'Ugyldig URL' };
  let u;
  try { u = new URL(clean); } catch { return { ok: false, error: 'Ugyldig URL' }; }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') return { ok: false, error: 'Kun http/https' };
  if (isBlockedPreviewHost(u.hostname)) return { ok: false, error: 'Blokkert vert' };

  const cached = linkPreviewCache.get(clean);
  if (cached && Date.now() - cached.ts < 30 * 60 * 1000) return cached.data;

  const cacheSet = (data) => {
    linkPreviewCache.set(clean, { ts: Date.now(), data });
    if (linkPreviewCache.size > 200) {
      const firstKey = linkPreviewCache.keys().next().value;
      if (firstKey) linkPreviewCache.delete(firstKey);
    }
    return data;
  };

  const ytId = extractYouTubeId(u);
  if (ytId) {
    let title = 'YouTube-video';
    try {
      const oembed = await fetchTextUrl(`https://www.youtube.com/oembed?url=${encodeURIComponent('https://www.youtube.com/watch?v=' + ytId)}&format=json`, 3500);
      const parsed = JSON.parse(oembed);
      if (parsed && parsed.title) title = String(parsed.title).slice(0, 140);
    } catch {}
    return cacheSet({
      ok: true,
      kind: 'youtube',
      videoId: ytId,
      url: clean,
      siteName: 'YouTube',
      title,
      image: `https://i.ytimg.com/vi/${ytId}/hqdefault.jpg`
    });
  }

  if (/\.(mp4|webm|mov|m4v)(\?.*)?$/i.test(u.pathname)) {
    return cacheSet({ ok: true, kind: 'video', url: clean, siteName: u.hostname });
  }
  if (/\.(mp3|wav|ogg|m4a|opus|aac)(\?.*)?$/i.test(u.pathname)) {
    return cacheSet({ ok: true, kind: 'audio', url: clean, siteName: u.hostname });
  }

  try {
    const html = await new Promise((resolve, reject) => {
      const lib = u.protocol === 'https:' ? https : http;
      const req = lib.get(clean, {
        headers: { 'User-Agent': 'Mozilla/5.0 (compatible; MinChatPreview/1.0)', 'Accept': 'text/html,application/xhtml+xml' },
        timeout: 4500
      }, (resp) => {
        if (resp.statusCode >= 300 && resp.statusCode < 400 && resp.headers.location) {
          resp.resume();
          resolve('');
          return;
        }
        const ct = String(resp.headers['content-type'] || '').toLowerCase();
        if (!ct.includes('text/html') && !ct.includes('application/xhtml')) {
          resp.resume();
          resolve('');
          return;
        }
        let buf = '';
        resp.setEncoding('utf8');
        resp.on('data', (chunk) => {
          buf += chunk;
          if (buf.length > 180 * 1024) { try { resp.destroy(); } catch {} resolve(buf); }
        });
        resp.on('end', () => resolve(buf));
      });
      req.on('timeout', () => { req.destroy(); reject(new Error('timeout')); });
      req.on('error', reject);
    });
    if (!html) return cacheSet({ ok: false });

    const pickMeta = (names) => {
      for (const n of names) {
        const rx1 = new RegExp(`<meta[^>]+(?:property|name)=["']${n}["'][^>]+content=["']([^"']+)["']`, 'i');
        const rx2 = new RegExp(`<meta[^>]+content=["']([^"']+)["'][^>]+(?:property|name)=["']${n}["']`, 'i');
        const m = html.match(rx1) || html.match(rx2);
        if (m && m[1]) return decodeHtmlEntities(m[1]);
      }
      return '';
    };
    let title = pickMeta(['og:title', 'twitter:title']);
    if (!title) {
      const tm = html.match(/<title[^>]*>([\s\S]*?)<\/title>/i);
      if (tm && tm[1]) title = decodeHtmlEntities(tm[1]);
    }
    const description = pickMeta(['og:description', 'twitter:description', 'description']).slice(0, 220);
    let image = pickMeta(['og:image', 'twitter:image']);
    if (image && !/^https?:\/\//i.test(image)) {
      try { image = new URL(image, clean).toString(); } catch { image = ''; }
    }
    const siteName = pickMeta(['og:site_name']) || u.hostname.replace(/^www\./, '');
    if (!title && !description && !image) return cacheSet({ ok: false });
    return cacheSet({
      ok: true,
      kind: 'card',
      url: clean,
      title: title.slice(0, 140),
      description,
      image: image.slice(0, 500),
      siteName: siteName.slice(0, 60)
    });
  } catch {
    return cacheSet({ ok: false });
  }
}

const wss = new WebSocketServer({ server, maxPayload: 75 * 1024 * 1024 });

function safeSend(ws, obj) {
  if (ws.readyState === WebSocket.OPEN) {
    try {
      const payload = typeof obj === 'string' ? obj : JSON.stringify(obj);
      ws.send(payload);
      ensureCloudMetrics().allTimeWsBytesOut += Buffer.byteLength(payload, 'utf8');
    } catch { }
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
    maxFileSizeMb: getMaxFileSizeMb(),
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
      avatar: getAvatarFor(devId),
      bio: getBioFor(devId),
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
        avatar: getAvatarFor(fId),
        bio: getBioFor(fId),
        role: 'verified',
        online: false
      });
    }
  }
  // Include all other registered accounts in mention/avatar lookup without leaking private data
  const avatars = {};
  for (const [accId, acc] of Object.entries(state.accounts)) {
    if (acc && typeof acc.avatar === 'string' && acc.avatar) avatars[accId] = acc.avatar;
    if (!seen.has(accId) && acc && acc.handle && !state.bannedDevices[accId]) {
      seen.add(accId);
      users.push({
        deviceId: accId,
        deviceTag: deviceTagFor(accId),
        user: acc.displayName || acc.handle,
        handle: acc.handle,
        color: acc.color || '#949BA4',
        avatar: acc.avatar || '',
        bio: typeof acc.bio === 'string' ? acc.bio : '',
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
    avatars,
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
    seq: Number(m.seq) || 0,
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
    poll: m.poll || null,
    file: liveFile !== undefined ? liveFile : (m.file ? stripFileData(m.file) : null),
    time: m.time,
    isoTime: m.isoTime,
    unixMs: msgUnixMs(m)
  };
}

function formatDmPayload(m, viewerIsAdmin, liveFile) {
  return {
    type: 'dm',
    seq: Number(m.seq) || 0,
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
    poll: m.poll || null,
    file: liveFile !== undefined ? liveFile : (m.file ? stripFileData(m.file) : null),
    time: m.time,
    isoTime: m.isoTime,
    unixMs: msgUnixMs(m)
  };
}

function canPinInScope(meta, scope, targetKey) {
  if (!meta || meta.status !== 'approved') return false;
  if (meta.role === 'admin' || meta.isAdminAccount) return true;
  if (scope === 'dm') return !!targetKey;
  const ch = String(targetKey || '').toLowerCase();
  if (DEFAULT_CHANNELS.includes(ch)) return false; // Public channels: admin-only pinning
  const custom = state.customChannels[ch];
  if (!custom) return false;
  return custom.ownerDeviceId === meta.deviceId || (Array.isArray(custom.members) && custom.members.includes(meta.deviceId));
}

function resolvePinsForScope(scope, key, list) {
  const scopeKey = scope === 'dm' ? ('dm:' + key) : key;
  const ids = Array.isArray(state.pins[scopeKey]) ? state.pins[scopeKey] : [];
  if (!ids.length) return [];
  const byId = new Map();
  for (const m of (list || [])) { if (m && m.msgId) byId.set(m.msgId, m); }
  const out = [];
  for (const id of ids) {
    const m = byId.get(id);
    if (!m) continue;
    out.push({
      msgId: m.msgId,
      seq: Number(m.seq) || 0,
      user: m.user || 'Bruker',
      handle: m.handle || getHandleFor(m.deviceId || m.fromDeviceId),
      color: m.color || '#dbdee1',
      text: m.poll ? `📊 ${m.poll.question}` : (m.text || (m.gif ? '[GIF]' : (m.file ? `[Fil: ${m.file.name}]` : ''))),
      time: m.time || '',
      unixMs: msgUnixMs(m)
    });
  }
  return out;
}

// Discord-style on-demand history pagination: ONLY sends the requested slice (default 20 msgs)!
function sendHistoryPage(ws, { scope, channel, peerDeviceId, beforeSeq = 0, limit = HISTORY_PAGE_SIZE }) {
  if (!ws.meta || ws.meta.status !== 'approved') return;
  const isAdmin = ws.meta.role === 'admin';
  const myId = ws.meta.deviceId;
  const pageLimit = Math.max(1, Math.min(25, Number(limit) || HISTORY_PAGE_SIZE));
  const cursor = Number(beforeSeq) || 0;

  if (scope === 'dm') {
    const peerId = String(peerDeviceId || '').trim();
    if (!peerId) return;
    const rk = dmRoomKey(myId, peerId);
    const all = dmHistory.get(rk) || [];
    const eligible = cursor > 0 ? all.filter((m) => (Number(m.seq) || 0) < cursor) : all;
    const startIdx = Math.max(0, eligible.length - pageLimit);
    const slice = eligible.slice(startIdx);
    const hasMore = startIdx > 0;
    const oldestSeq = slice.length ? (Number(slice[0].seq) || 0) : cursor;
    safeSend(ws, {
      type: 'history_page',
      scope: 'dm',
      peerDeviceId: peerId,
      prepend: cursor > 0,
      hasMore,
      oldestSeq,
      messages: slice.map((m) => formatDmPayload(m, isAdmin, undefined))
    });
    return;
  }

  const ch = typeof channel === 'string' && channel.startsWith('#') ? channel.slice(0, 32).toLowerCase() : '#general-1';
  if (!canAccessChannel(ws.meta, ch)) return;
  const all = channelHistory.get(ch) || [];
  let cutoffMs = ws.meta.firstJoinedMs || Date.now();
  const custom = state.customChannels[ch];
  if (custom && custom.memberJoinedMs && typeof custom.memberJoinedMs[myId] === 'number') {
    cutoffMs = Math.max(cutoffMs, custom.memberJoinedMs[myId]);
  }
  const visible = isAdmin
    ? all
    : all.filter((m) => (typeof m.unixMs === 'number' ? m.unixMs : 0) >= cutoffMs);
  const eligible = cursor > 0 ? visible.filter((m) => (Number(m.seq) || 0) < cursor) : visible;
  const startIdx = Math.max(0, eligible.length - pageLimit);
  const slice = eligible.slice(startIdx);
  const hasMore = startIdx > 0;
  const oldestSeq = slice.length ? (Number(slice[0].seq) || 0) : cursor;

  safeSend(ws, {
    type: 'history_page',
    scope: 'channel',
    channel: ch,
    prepend: cursor > 0,
    hasMore,
    oldestSeq,
    messages: slice.map((m) => formatChatPayload(m, isAdmin, undefined))
  });
}

function replayHistoryToClient(ws) {
  if (!ws.meta || ws.meta.status !== 'approved') return;
  // On boot/connect, ONLY load the latest 20 messages of the user's active channel (other channels load on demand!)
  const activeCh = (ws.meta.channel && canAccessChannel(ws.meta, ws.meta.channel)) ? ws.meta.channel : '#general-1';
  sendHistoryPage(ws, { scope: 'channel', channel: activeCh, beforeSeq: 0, limit: HISTORY_PAGE_SIZE });
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
    cloudStorage: buildCloudStatusForAdmin(),
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
        isoTime: record.isoTime,
        unixMs: msgUnixMs(record)
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
    color: ws.meta.color,
    avatar: getAvatarFor(ws.meta.deviceId),
    bio: getBioFor(ws.meta.deviceId),
    serverVersion: SERVER_VERSION,
    updater: state.updater,
    announcement: state.announcement,
    cooldowns: state.cooldowns,
    heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
    heartbeatSec: state.settings.heartbeatSec,
    maxFileSizeMb: getMaxFileSizeMb(),
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
    maxFileSizeMb: getMaxFileSizeMb(),
    updater: state.updater,
    announcement: state.announcement,
    cooldowns: state.cooldowns
  });

  ws.on('message', (raw) => {
    if (raw) ensureCloudMetrics().allTimeWsBytesIn += (typeof raw === 'string' ? Buffer.byteLength(raw, 'utf8') : (raw.length || 0));
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
      const missing = vault.slice(-VAULT_PAGE_SIZE);
      if (missing.length > 0) {
        safeSend(ws, {
          type: 'admin_vault_sync',
          records: missing,
          hasMore: vault.length > missing.length,
          oldestSeq: missing[0] ? (Number(missing[0].seq) || 0) : 0
        });
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

    // Instant live Display Name / color / avatar update (keeps permanent accountId & @handle intact, blocks impersonation!)
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
      let avatarUpdated = false;
      let newAvatar = getAvatarFor(ws.meta.deviceId);
      if (msg.avatar !== undefined) {
        const cleanAv = sanitizeAvatarDataUrl(msg.avatar);
        if (cleanAv === null) {
          safeSend(ws, {
            type: 'profile_rejected',
            error: 'Profilbildet er for stort eller ugyldig format.',
            user: ws.meta.user,
            color: ws.meta.color
          });
          return;
        }
        newAvatar = cleanAv;
        avatarUpdated = true;
      }
      let newBio = getBioFor(ws.meta.deviceId);
      if (typeof msg.bio === 'string') {
        newBio = msg.bio.replace(/[\r\n]+/g, ' ').trim().slice(0, 140);
      }
      if (ws.meta.deviceId && state.accounts[ws.meta.deviceId]) {
        state.accounts[ws.meta.deviceId].displayName = ws.meta.user;
        state.accounts[ws.meta.deviceId].color = ws.meta.color;
        if (avatarUpdated) state.accounts[ws.meta.deviceId].avatar = newAvatar;
        if (typeof msg.bio === 'string') state.accounts[ws.meta.deviceId].bio = newBio;
      }
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].user = ws.meta.user;
        state.knownDevices[ws.meta.deviceId].color = ws.meta.color;
      }
      // Keep all open tabs of this account in sync
      for (const c of wss.clients) {
        if (c.meta && c.meta.deviceId === ws.meta.deviceId) {
          c.meta.user = ws.meta.user;
          c.meta.color = ws.meta.color;
        }
      }
      saveState();
      safeSend(ws, {
        type: 'profile_updated',
        user: ws.meta.user,
        color: ws.meta.color,
        avatar: newAvatar,
        bio: newBio
      });
      broadcastSocialStates();
      broadcastAdminState();
      return;
    }

    // Self-service password change from User Settings modal
    if (msg.type === 'change_password') {
      const acc = ws.meta.deviceId ? state.accounts[ws.meta.deviceId] : null;
      if (!acc) {
        safeSend(ws, { type: 'password_changed', ok: false, error: 'Fant ikke kontoen din.' });
        return;
      }
      const curPw = String(msg.currentPassword || '');
      const newPw = String(msg.newPassword || '');
      if (!verifyPassword(curPw, acc.passwordSalt, acc.passwordHash)) {
        safeSend(ws, { type: 'password_changed', ok: false, error: 'Nåværende passord er feil.' });
        return;
      }
      if (newPw.length < 6 || newPw.length > 128) {
        safeSend(ws, { type: 'password_changed', ok: false, error: 'Nytt passord må være 6–128 tegn.' });
        return;
      }
      const { salt, hash } = hashPassword(newPw);
      acc.passwordSalt = salt;
      acc.passwordHash = hash;
      saveState();
      safeSend(ws, { type: 'password_changed', ok: true });
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
        let pinsChanged = false;
        if (Array.isArray(state.pins[ch]) && state.pins[ch].includes(msgId)) {
          state.pins[ch] = state.pins[ch].filter((id) => id !== msgId);
          if (!state.pins[ch].length) delete state.pins[ch];
          pinsChanged = true;
          saveState();
        }

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

        const updatedPins = pinsChanged ? resolvePinsForScope('channel', ch, arr) : null;
        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, { type: 'message_deleted', scope: 'channel', channel: ch, msgId });
            if (pinsChanged) safeSend(c, { type: 'pins_update', scope: 'channel', channel: ch, pins: updatedPins });
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
        const dmPinKey = 'dm:' + rk;
        let dmPinsChanged = false;
        if (Array.isArray(state.pins[dmPinKey]) && state.pins[dmPinKey].includes(msgId)) {
          state.pins[dmPinKey] = state.pins[dmPinKey].filter((id) => id !== msgId);
          if (!state.pins[dmPinKey].length) delete state.pins[dmPinKey];
          dmPinsChanged = true;
          saveState();
        }

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

        const updatedDmPins = dmPinsChanged ? resolvePinsForScope('dm', rk, arr) : null;
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
            if (dmPinsChanged) {
              const peerForC = c.meta.deviceId === target.fromDeviceId ? target.toDeviceId : target.fromDeviceId;
              safeSend(c, { type: 'pins_update', scope: 'dm', peerDeviceId: peerForC, pins: updatedDmPins });
            }
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
      const pollObj = sanitizePoll(msg.poll);
      if (!text && !liveFile && !gifObj && !pollObj) return;

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
        text: text || (gifObj || pollObj ? '' : (metaFile ? `[Fil: ${metaFile.name} (${Math.round(metaFile.size / 1024)} KB)]` : '')),
        replyTo: resolveAuthoritativeReply(msg.replyTo, arr),
        reactions: {},
        edited: false,
        editedAt: '',
        gif: gifObj,
        poll: pollObj,
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
      const pollObj = sanitizePoll(msg.poll);
      if (!text && !liveFile && !gifObj && !pollObj) return;

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
        text: text || (gifObj || pollObj ? '' : (metaFile ? `[Fil: ${metaFile.name} (${Math.round(metaFile.size / 1024)} KB)]` : '')),
        replyTo: resolveAuthoritativeReply(msg.replyTo, arr),
        reactions: {},
        edited: false,
        editedAt: '',
        gif: gifObj,
        poll: pollObj,
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

    if (msg.type === 'poll_vote') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      const msgId = String(msg.msgId || '');
      const optIdx = Number(msg.optionIndex);
      if (!msgId || !Number.isInteger(optIdx) || optIdx < 0) return;

      if (scope === 'dm') {
        const peerId = String(msg.peerDeviceId || '').trim();
        if (!peerId) return;
        const rk = dmRoomKey(ws.meta.deviceId, peerId);
        const list = dmHistory.get(rk) || [];
        const target = list.find((m) => m.msgId === msgId && m.poll);
        if (!target || !target.poll.options[optIdx]) return;
        const myId = ws.meta.deviceId;
        const already = target.poll.options[optIdx].votes.includes(myId);
        for (const o of target.poll.options) o.votes = o.votes.filter((id) => id !== myId);
        if (!already) target.poll.options[optIdx].votes.push(myId);
        rewriteVaultFile();
        for (const c of wss.clients) {
          if (!c.meta || c.meta.status !== 'approved') continue;
          if (c.meta.deviceId === ws.meta.deviceId || c.meta.deviceId === peerId) {
            safeSend(c, { type: 'poll_update', scope: 'dm', peerDeviceId: c.meta.deviceId === ws.meta.deviceId ? peerId : ws.meta.deviceId, msgId, poll: target.poll });
          }
        }
      } else {
        const ch = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32).toLowerCase() : '#general-1';
        if (!canAccessChannel(ws.meta, ch)) return;
        const list = channelHistory.get(ch) || [];
        const target = list.find((m) => m.msgId === msgId && m.poll);
        if (!target || !target.poll.options[optIdx]) return;
        const myId = ws.meta.deviceId;
        const already = target.poll.options[optIdx].votes.includes(myId);
        for (const o of target.poll.options) o.votes = o.votes.filter((id) => id !== myId);
        if (!already) target.poll.options[optIdx].votes.push(myId);
        rewriteVaultFile();
        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, { type: 'poll_update', scope: 'channel', channel: ch, msgId, poll: target.poll });
          }
        }
      }
      return;
    }

    if (msg.type === 'toggle_pin') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      const msgId = String(msg.msgId || '');
      if (!msgId) return;

      if (scope === 'dm') {
        const peerId = String(msg.peerDeviceId || '').trim();
        if (!peerId || !canPinInScope(ws.meta, 'dm', peerId)) return;
        const rk = dmRoomKey(ws.meta.deviceId, peerId);
        const list = dmHistory.get(rk) || [];
        if (!list.some((m) => m.msgId === msgId)) return;
        const scopeKey = 'dm:' + rk;
        if (!Array.isArray(state.pins[scopeKey])) state.pins[scopeKey] = [];
        const idx = state.pins[scopeKey].indexOf(msgId);
        if (idx >= 0) state.pins[scopeKey].splice(idx, 1);
        else {
          state.pins[scopeKey].unshift(msgId);
          if (state.pins[scopeKey].length > 25) state.pins[scopeKey].pop();
        }
        saveState();
        const resolved = resolvePinsForScope('dm', rk, list);
        for (const c of wss.clients) {
          if (!c.meta || c.meta.status !== 'approved') continue;
          if (c.meta.deviceId === ws.meta.deviceId || c.meta.deviceId === peerId) {
            safeSend(c, { type: 'pins_update', scope: 'dm', peerDeviceId: c.meta.deviceId === ws.meta.deviceId ? peerId : ws.meta.deviceId, pins: resolved });
          }
        }
      } else {
        const ch = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32).toLowerCase() : '#general-1';
        if (!canPinInScope(ws.meta, 'channel', ch)) {
          safeSend(ws, { type: 'social_notice', text: 'Kun admin kan feste meldinger i offentlige kanaler.' });
          return;
        }
        const list = channelHistory.get(ch) || [];
        if (!list.some((m) => m.msgId === msgId)) return;
        if (!Array.isArray(state.pins[ch])) state.pins[ch] = [];
        const idx = state.pins[ch].indexOf(msgId);
        if (idx >= 0) state.pins[ch].splice(idx, 1);
        else {
          state.pins[ch].unshift(msgId);
          if (state.pins[ch].length > 25) state.pins[ch].pop();
        }
        saveState();
        const resolved = resolvePinsForScope('channel', ch, list);
        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, { type: 'pins_update', scope: 'channel', channel: ch, pins: resolved });
          }
        }
      }
      return;
    }

    if (msg.type === 'pins_req') {
      const scope = msg.scope === 'dm' ? 'dm' : 'channel';
      if (scope === 'dm') {
        const peerId = String(msg.peerDeviceId || '').trim();
        if (!peerId) return;
        const rk = dmRoomKey(ws.meta.deviceId, peerId);
        const list = dmHistory.get(rk) || [];
        safeSend(ws, { type: 'pins_update', scope: 'dm', peerDeviceId: peerId, pins: resolvePinsForScope('dm', rk, list) });
      } else {
        const ch = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32).toLowerCase() : '#general-1';
        if (!canAccessChannel(ws.meta, ch)) return;
        const list = channelHistory.get(ch) || [];
        safeSend(ws, { type: 'pins_update', scope: 'channel', channel: ch, pins: resolvePinsForScope('channel', ch, list) });
      }
      return;
    }

    if (msg.type === 'history_page_req') {
      sendHistoryPage(ws, {
        scope: msg.scope === 'dm' ? 'dm' : 'channel',
        channel: msg.channel,
        peerDeviceId: msg.peerDeviceId,
        beforeSeq: msg.beforeSeq,
        limit: msg.limit
      });
      return;
    }

    if (msg.type === 'dm_history_req') {
      sendHistoryPage(ws, {
        scope: 'dm',
        peerDeviceId: msg.peerDeviceId,
        beforeSeq: msg.beforeSeq || 0,
        limit: msg.limit || HISTORY_PAGE_SIZE
      });
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
  const vSlice = vault.slice(-VAULT_PAGE_SIZE);
  sendToAdmins({
    type: 'admin_vault_sync',
    records: vSlice,
    hasMore: vault.length > vSlice.length,
    oldestSeq: vSlice.length ? (Number(vSlice[0].seq) || 0) : 0
  });
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
    if (typeof cmd.maxMsgsPerChannel === 'number' && cmd.maxMsgsPerChannel >= 0 && cmd.maxMsgsPerChannel <= 50000) {
      state.settings.maxMsgsPerChannel = Math.round(cmd.maxMsgsPerChannel);
    }
    if (typeof cmd.retentionDays === 'number' && cmd.retentionDays >= 0 && cmd.retentionDays <= 3650) {
      state.settings.retentionDays = Math.round(cmd.retentionDays);
    }
    if (typeof cmd.maxFileSizeMb === 'number' && cmd.maxFileSizeMb >= 1 && cmd.maxFileSizeMb <= 50) {
      state.settings.maxFileSizeMb = Math.round(cmd.maxFileSizeMb);
    }
    saveState();
    runAutoPrune();
    for (const c of wss.clients) pushConfigToClient(c);
    broadcastAdminState();
    return;
  }

  if (action === 'run_prune') {
    const res = runAutoPrune(true);
    safeSend(adminWs, {
      type: 'admin_console_out',
      text: `Auto-Prune fullført: fjernet ${res.removedMsgs} meldinger og ${res.removedVault} logglinjer.`
    });
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

  if (action === 'cloud_sync_now') {
    if (!cloudStorage.enabled) {
      safeSend(adminWs, { type: 'social_notice', text: 'Sky-lagring er ikke konfigurert ennå.' });
      return;
    }
    flushCloudSaveNow(true).then(() => {
      safeSend(adminWs, { type: 'social_notice', text: cloudStorage.lastError ? `Sky-lagring feilet: ${cloudStorage.lastError}` : '☁️ Arkivert til skyen nå!' });
      broadcastAdminState();
    });
    return;
  }

  if (action === 'vault_page_req') {
    const cursor = Number(cmd.beforeSeq) || 0;
    const pageLimit = Math.max(1, Math.min(80, Number(cmd.limit) || VAULT_PAGE_SIZE));
    const q = String(cmd.query || '').trim().toLowerCase();
    const evType = String(cmd.eventType || '').trim().toLowerCase();
    let eligible = vault;
    if (evType && evType !== 'all') {
      eligible = eligible.filter((r) => String(r && r.type || '').toLowerCase() === evType);
    }
    if (q) {
      eligible = eligible.filter((r) => {
        if (!r) return false;
        const hay = `${r.text || ''} ${r.user || ''} ${r.handle || ''} ${r.channel || ''} ${r.type || ''}`.toLowerCase();
        return hay.includes(q);
      });
    }
    if (cursor > 0) eligible = eligible.filter((r) => (Number(r.seq) || 0) < cursor);
    const startIdx = Math.max(0, eligible.length - pageLimit);
    const slice = eligible.slice(startIdx);
    safeSend(adminWs, {
      type: 'admin_vault_page',
      prepend: cursor > 0,
      hasMore: startIdx > 0,
      oldestSeq: slice.length ? (Number(slice[0].seq) || 0) : cursor,
      totalMatches: eligible.length,
      records: slice
    });
    return;
  }
}

function runAutoPrune(forceBroadcast = false) {
  const maxMsgs = Math.max(0, Number(state.settings.maxMsgsPerChannel) || 0);
  const retDays = Math.max(0, Number(state.settings.retentionDays) || 0);
  if (!maxMsgs && !retDays) return { removedMsgs: 0, removedVault: 0 };

  const cutoffMs = retDays > 0 ? (Date.now() - retDays * 86400000) : 0;
  let removedMsgs = 0;
  const keptMsgIds = new Set();

  for (const [ch, list] of channelHistory.entries()) {
    let arr = list;
    const before = arr.length;
    if (cutoffMs > 0) arr = arr.filter((m) => (Number(m.unixMs) || 0) >= cutoffMs);
    if (maxMsgs > 0 && arr.length > maxMsgs) arr = arr.slice(-maxMsgs);
    if (arr.length !== before) {
      removedMsgs += (before - arr.length);
      channelHistory.set(ch, arr);
    }
    for (const m of arr) { if (m && m.msgId) keptMsgIds.add(m.msgId); }
  }

  for (const [rk, list] of dmHistory.entries()) {
    let arr = list;
    const before = arr.length;
    if (cutoffMs > 0) arr = arr.filter((m) => (Number(m.unixMs) || 0) >= cutoffMs);
    if (maxMsgs > 0 && arr.length > maxMsgs) arr = arr.slice(-maxMsgs);
    if (arr.length !== before) {
      removedMsgs += (before - arr.length);
      dmHistory.set(rk, arr);
    }
    for (const m of arr) { if (m && m.msgId) keptMsgIds.add(m.msgId); }
  }

  let removedVault = 0;
  if (removedMsgs > 0 || cutoffMs > 0) {
    for (let i = vault.length - 1; i >= 0; i--) {
      const r = vault[i];
      if (!r) continue;
      const isChatOrDm = r.type === 'chat' || r.type === 'dm';
      if (isChatOrDm && r.msgId && !keptMsgIds.has(r.msgId)) {
        vault.splice(i, 1);
        removedVault++;
      } else if (cutoffMs > 0 && isChatOrDm && (Number(r.unixMs) || 0) > 0 && Number(r.unixMs) < cutoffMs) {
        vault.splice(i, 1);
        removedVault++;
      }
    }
  }

  if (removedMsgs > 0 || removedVault > 0) {
    rewriteVaultFile();
    saveState();
    broadcastAdminState();
  } else if (forceBroadcast) {
    broadcastAdminState();
  }
  return { removedMsgs, removedVault };
}

setInterval(() => runAutoPrune(), 30 * 60 * 1000);

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

let shuttingDown = false;
async function gracefulShutdown(sig) {
  if (shuttingDown) return;
  shuttingDown = true;
  if (cloudStorage.enabled) {
    try {
      await Promise.race([
        flushCloudSaveNow(true),
        new Promise((r) => setTimeout(r, 4000))
      ]);
    } catch { }
  }
  process.exit(0);
}
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));
process.on('SIGINT', () => gracefulShutdown('SIGINT'));

(async () => {
  await loadCloudStateOnBoot();
  ensureAdminPasswordSeed();
  runAutoPrune();
  server.listen(PORT, () => {
    console.log(`Chat Smart Relay v${SERVER_VERSION} (v5) lytter på port ${PORT}${cloudStorage.enabled ? ` | Sky-lagring: ${cloudStorage.connected ? 'TILKOBLET' : 'FEIL'}` : ''}`);
  });
})();
