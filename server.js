const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.3.1';
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

function publicAccountSummary(acc) {
  if (!acc) return null;
  return {
    accountId: acc.accountId,
    deviceTag: deviceTagFor(acc.accountId),
    handle: acc.handle,
    user: acc.displayName,
    color: acc.color || '#3498DB',
    avatar: typeof acc.avatar === 'string' ? acc.avatar : '',
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
    file: liveFile !== undefined ? liveFile : (m.file ? stripFileData(m.file) : null),
    time: m.time,
    isoTime: m.isoTime
  };
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
      if (ws.meta.deviceId && state.accounts[ws.meta.deviceId]) {
        state.accounts[ws.meta.deviceId].displayName = ws.meta.user;
        state.accounts[ws.meta.deviceId].color = ws.meta.color;
        if (avatarUpdated) state.accounts[ws.meta.deviceId].avatar = newAvatar;
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
        avatar: newAvatar
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
    const pageLimit = Math.max(1, Math.min(60, Number(cmd.limit) || VAULT_PAGE_SIZE));
    const eligible = cursor > 0 ? vault.filter((r) => (Number(r.seq) || 0) < cursor) : vault;
    const startIdx = Math.max(0, eligible.length - pageLimit);
    const slice = eligible.slice(startIdx);
    safeSend(adminWs, {
      type: 'admin_vault_page',
      prepend: cursor > 0,
      hasMore: startIdx > 0,
      oldestSeq: slice.length ? (Number(slice[0].seq) || 0) : cursor,
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
