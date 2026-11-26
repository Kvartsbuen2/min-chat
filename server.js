const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.5.0';
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
  const isAudio = !isImage && (!!fileObj.isAudio || mime.startsWith('audio/') || /\.(mp3|wav|ogg|m4a|flac|aac|opus)$/i.test(name));
  const isVideo = !isImage && !isAudio && (!!fileObj.isVideo || mime.startsWith('video/') || /\.(mp4|webm|mov|m4v)$/i.test(name));
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
    maxFileSizeMb: 6,     // Admin-configurable global max live attachment size (1–50 MB)
    adminAppearOffline: false // v3.5.0: Stealth invisible mode for admin (NEVER exposed to non-admins)
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
  publicChannels: [...DEFAULT_CHANNELS], // v3.5.0: Admin-managed official public channels (#general-1 always kept)
  customChannels: {}
};

function getPublicChannels() {
  const raw = Array.isArray(state.publicChannels) ? state.publicChannels : DEFAULT_CHANNELS;
  const out = ['#general-1'];
  for (const ch of raw) {
    const slug = sanitizeChannelSlug(ch);
    if (slug && !out.includes(slug)) out.push(slug);
  }
  return out;
}

function isAdminInvisible() {
  return !!(state.settings && state.settings.adminAppearOffline);
}

function describeUserAgent(uaRaw) {
  const ua = String(uaRaw || '');
  if (!ua) return 'Ukjent enhet';
  let os = 'Ukjent OS';
  if (/Windows NT 10/i.test(ua)) os = 'Windows 10/11';
  else if (/Windows/i.test(ua)) os = 'Windows';
  else if (/CrOS/i.test(ua)) os = 'Chromebook';
  else if (/iPhone/i.test(ua)) os = 'iPhone';
  else if (/iPad/i.test(ua)) os = 'iPad';
  else if (/Android/i.test(ua)) os = 'Android';
  else if (/Mac OS X|Macintosh/i.test(ua)) os = 'macOS';
  else if (/Linux/i.test(ua)) os = 'Linux';

  let br = 'Nettleser';
  if (/Edg\//i.test(ua)) br = 'Edge';
  else if (/OPR\/|Opera/i.test(ua)) br = 'Opera';
  else if (/Firefox\//i.test(ua)) br = 'Firefox';
  else if (/Chrome\//i.test(ua)) br = 'Chrome';
  else if (/Safari\//i.test(ua)) br = 'Safari';
  return `${os} · ${br}`;
}

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
    publicChannels: getPublicChannels(),
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
  if (Array.isArray(saved.publicChannels) && saved.publicChannels.length) state.publicChannels = saved.publicChannels;
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
      if (Array.isArray(saved.publicChannels) && saved.publicChannels.length) state.publicChannels = saved.publicChannels;
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
  if (getPublicChannels().includes(channel)) return true;
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

  const hideAdminOnline = isAdminInvisible() && !isAdmin;
  const users = [];
  const seen = new Set();
  for (const [devId, m] of onlineMap.entries()) {
    seen.add(devId);
    const isThisAdmin = !!(m.isAdminAccount || m.handle === ADMIN_HANDLE);
    users.push({
      deviceId: devId,
      deviceTag: deviceTagFor(devId),
      user: m.user,
      handle: getHandleFor(devId, onlineMap),
      color: m.color,
      avatar: getAvatarFor(devId),
      bio: getBioFor(devId),
      role: publicRoleFor(m.role, isAdmin),
      online: (hideAdminOnline && isThisAdmin) ? false : true
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
    publicChannels: getPublicChannels(),
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
  if (getPublicChannels().includes(ch)) return false; // Public channels: admin-only pinning
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
    publicChannels: getPublicChannels(),
    adminAppearOffline: isAdminInvisible(),
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
  const uaDeviceInfo = describeUserAgent(req.headers['user-agent'] || '');

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
    host: uaDeviceInfo,
    deviceInfo: uaDeviceInfo,
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
      const rawHost = String(msg.host || '').trim().slice(0, 40);
      const host = (rawHost && rawHost.toLowerCase() !== 'web') ? `${rawHost} (${ws.meta.deviceInfo || 'Web'})`.slice(0, 64) : (ws.meta.deviceInfo || 'Web');

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
      if (ws.meta.isAdminAccount && isAdminInvisible()) { clearTypingFor(ws); return; }
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
      if (getPublicChannels().includes(slug) || state.customChannels[slug]) {
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
  if (Array.isArray(src.publicChannels) && src.publicChannels.length) state.publicChannels = [...src.publicChannels];
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

  if (action === 'set_appear_offline') {
    state.settings.adminAppearOffline = !!cmd.enabled;
    if (state.settings.adminAppearOffline) clearTypingFor(adminWs);
    saveState();
    broadcastSocialStates();
    broadcastAdminState();
    return;
  }

  if (action === 'create_public_channel') {
    const slug = sanitizeChannelSlug(cmd.name || cmd.channel || '');
    if (!slug) {
      safeSend(adminWs, { type: 'admin_notice', action: 'info', text: 'Ugyldig kanalnavn (bruk bokstaver, tall, - eller _).' });
      return;
    }
    const pub = getPublicChannels();
    if (pub.length >= 20) {
      safeSend(adminWs, { type: 'admin_notice', action: 'info', text: 'Maks 20 offisielle kanaler.' });
      return;
    }
    if (pub.includes(slug) || state.customChannels[slug]) {
      safeSend(adminWs, { type: 'admin_notice', action: 'info', text: `Kanalen ${slug} finnes allerede.` });
      return;
    }
    state.publicChannels = [...pub, slug];
    saveState();
    broadcastSocialStates();
    broadcastAdminState();
    return;
  }

  if (action === 'delete_public_channel') {
    const slug = sanitizeChannelSlug(cmd.channel || '');
    if (!slug || slug === '#general-1') return;
    const pub = getPublicChannels();
    if (!pub.includes(slug)) return;
    state.publicChannels = pub.filter((c) => c !== slug);
    channelHistory.delete(slug);
    if (state.cooldowns.channels) delete state.cooldowns.channels[slug];
    if (state.pins[slug]) delete state.pins[slug];
    for (const c of wss.clients) {
      if (c.meta && c.meta.channel === slug) c.meta.channel = '#general-1';
    }
    saveState();
    broadcastSocialStates();
    broadcastAdminState();
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
