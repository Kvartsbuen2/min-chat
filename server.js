const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.4.2';
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
    isoTime: m.isoTime
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
    isoTime: m.isoTime
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
      time: m.time || ''
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
