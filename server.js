const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.2.3';
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
  const hash = crypto.createHash('sha1').update(data).digest('hex').slice(0, 16);
  return { name, size, isImage, hash, data };
}

// Strips binary data so server/DB NEVER stores images or file contents — ONLY lightweight reference (name, size, isImage, hash)!
function stripFileData(fileObj) {
  if (!fileObj) return null;
  const out = { name: fileObj.name, size: fileObj.size, isImage: !!fileObj.isImage };
  if (fileObj.hash) out.hash = String(fileObj.hash).slice(0, 24);
  return out;
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
  server.listen(PORT, () => {
    console.log(`Chat Smart Relay v${SERVER_VERSION} (v5) lytter på port ${PORT}${cloudStorage.enabled ? ` | Sky-lagring: ${cloudStorage.connected ? 'TILKOBLET' : 'FEIL'}` : ''}`);
  });
})();
