const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.4.1';
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
