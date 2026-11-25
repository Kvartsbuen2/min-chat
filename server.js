const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.2.2';
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
