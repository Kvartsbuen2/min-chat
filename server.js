const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.4.0';
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
