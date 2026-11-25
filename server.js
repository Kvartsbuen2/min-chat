const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.3.0';
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
const MAX_FILE_BYTES = 6 * 1024 * 1024; // 6 MB live relay only (never stored in DB!)
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

// Validates live file/image/video/audio attachment for transit ONLY
function sanitizeLiveAttachment(fileObj) {
  if (!fileObj || typeof fileObj !== 'object') return null;
  const data = typeof fileObj.data === 'string' ? fileObj.data : '';
  if (!data || data.length > 9 * 1024 * 1024) return null;
  const name = String(fileObj.name || 'fil').replace(/[<>:"/\\|?*\x00-\x1F]/g, '_').slice(0, 80) || 'fil';
  const size = typeof fileObj.size === 'number' && fileObj.size >= 0
    ? Math.min(MAX_FILE_BYTES, Math.round(fileObj.size))
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
    retentionDays: 0      // 0 = never auto-delete; >0 deletes messages older than N days
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

const wss = new WebSocketServer({ server, maxPayload: 9 * 1024 * 1024 });

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
