const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.2.1';
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
// Cloud DB is ONLY used for boot restore + compressed background archiving (10s batching)!
// Free tier limits: 250 MB storage, 10 GB/month bandwidth.
// =============================================================================
const UPSTASH_URL = (process.env.UPSTASH_REDIS_REST_URL || process.env.KV_REST_API_URL || '').trim().replace(/\/+$/, '');
const UPSTASH_TOKEN = (process.env.UPSTASH_REDIS_REST_TOKEN || process.env.KV_REST_API_TOKEN || '').trim();
const CLOUD_STATE_KEY = 'minchat:v3:state';
const CLOUD_HISTORY_KEY = 'minchat:v3:history';
const CLOUD_LIMIT_STORAGE_BYTES = 250 * 1024 * 1024;           // 250 MB
const CLOUD_LIMIT_MONTHLY_BW_BYTES = 10 * 1024 * 1024 * 1024;  // 10 GB / month
const CLOUD_SAVE_DEBOUNCE_MS = 10000;                          // 10s batching for minimal bandwidth!

function currentMonthKey() {
  const d = new Date();
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}`;
}

function ensureCloudMetrics() {
  const mk = currentMonthKey();
  if (!state.cloudMetrics || typeof state.cloudMetrics !== 'object' || state.cloudMetrics.monthKey !== mk) {
    const prev = (state.cloudMetrics && typeof state.cloudMetrics === 'object') ? state.cloudMetrics : {};
    state.cloudMetrics = {
      monthKey: mk,
      monthBytesSent: 0,
      monthBytesRecv: 0,
      monthCommands: 0,
      monthSyncs: 0,
      lastStateBytes: Number(prev.lastStateBytes) || 0,
      lastHistoryBytes: Number(prev.lastHistoryBytes) || 0,
      lastRawStateBytes: Number(prev.lastRawStateBytes) || 0,
      lastRawHistoryBytes: Number(prev.lastRawHistoryBytes) || 0
    };
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
    epoch: STATE_EPOCH,
    nextSeq,
    channelHistory: chObj,
    dmHistory: dmObj,
    vault: compactVault
  };
}

function buildCloudStatusForAdmin() {
  const m = ensureCloudMetrics();
  // Live fallback estimate if cloud hasn't synced yet
  const stateBytes = m.lastStateBytes || Buffer.byteLength(JSON.stringify(state), 'utf8');
  const historyBytes = m.lastHistoryBytes || 0;
  const totalStoredBytes = stateBytes + historyBytes;
  const totalRawBytes = (m.lastRawStateBytes || stateBytes) + (m.lastRawHistoryBytes || historyBytes);
  const monthTotalBytes = (m.monthBytesSent || 0) + (m.monthBytesRecv || 0);
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
    stateBytes,
    historyBytes,
    totalStoredBytes,
    totalRawBytes,
    monthBytesSent: m.monthBytesSent || 0,
    monthBytesRecv: m.monthBytesRecv || 0,
    monthTotalBytes,
    monthCommands: m.monthCommands || 0,
    monthSyncs: m.monthSyncs || 0,
    totalMessages,
    totalImageRefs,
    debounceSec: Math.round(CLOUD_SAVE_DEBOUNCE_MS / 1000)
  };
}

async function flushCloudSaveNow(forceBoth = false) {
  if (!cloudStorage.enabled) return;
  if (cloudSaveTimer) { clearTimeout(cloudSaveTimer); cloudSaveTimer = null; }
  if (forceBoth) { cloudStateDirty = true; cloudHistoryDirty = true; }
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
      let stEnc = null;
      let histEnc = null;
      if (saveHistoryNow) {
        histEnc = encodeCloudPayload(buildCompactHistorySnapshot());
        m.lastHistoryBytes = histEnc.storedBytes;
        m.lastRawHistoryBytes = histEnc.rawBytes;
        cmds.push(['SET', CLOUD_HISTORY_KEY, histEnc.encoded]);
      }
      if (saveStateNow) {
        stEnc = encodeCloudPayload(state);
        m.lastStateBytes = stEnc.storedBytes;
        m.lastRawStateBytes = stEnc.rawBytes;
        cmds.push(['SET', CLOUD_STATE_KEY, stEnc.encoded]);
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

async function loadCloudStateOnBoot() {
  ensureCloudMetrics();
  if (!cloudStorage.enabled) {
    cloudBootReady = true;
    return;
  }
  try {
    const res = await upstashPost('/pipeline', [
      ['GET', CLOUD_STATE_KEY],
      ['GET', CLOUD_HISTORY_KEY]
    ], 2);
    cloudStorage.connected = true;
    cloudStorage.lastError = '';
    const rawState = Array.isArray(res) && res[0] && typeof res[0].result === 'string' ? res[0].result : '';
    const rawHist = Array.isArray(res) && res[1] && typeof res[1].result === 'string' ? res[1].result : '';

    let loadedCloudState = false;
    if (rawState) {
      const saved = decodeCloudPayload(rawState);
      if (saved && saved.epoch === STATE_EPOCH) {
        loadedCloudState = true;
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
        if (saved.cloudMetrics && saved.cloudMetrics.monthKey === currentMonthKey()) {
          const curM = ensureCloudMetrics();
          state.cloudMetrics = {
            ...saved.cloudMetrics,
            monthBytesSent: (Number(saved.cloudMetrics.monthBytesSent) || 0) + curM.monthBytesSent,
            monthBytesRecv: (Number(saved.cloudMetrics.monthBytesRecv) || 0) + curM.monthBytesRecv,
            monthCommands: (Number(saved.cloudMetrics.monthCommands) || 0) + curM.monthCommands,
            lastStateBytes: Buffer.byteLength(rawState, 'utf8'),
            lastHistoryBytes: rawHist ? Buffer.byteLength(rawHist, 'utf8') : (Number(saved.cloudMetrics.lastHistoryBytes) || 0)
          };
        }
        if (compareVersions(SERVER_VERSION, state.updater.latestVersion) > 0) {
          state.updater.latestVersion = SERVER_VERSION;
        }
        cloudStorage.lastLoadedIso = formatIsoNow();
      }
    }

    if (loadedCloudState && rawHist) {
      const h = decodeCloudPayload(rawHist);
      if (h && h.epoch === STATE_EPOCH) {
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
        const m = ensureCloudMetrics();
        m.lastHistoryBytes = Buffer.byteLength(rawHist, 'utf8');
      }
    }

    cloudBootReady = true;
    if (loadedCloudState) {
      try {
        fs.mkdirSync(DATA_DIR, { recursive: true });
        fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8');
        const content = vault.length ? vault.map((r) => JSON.stringify(r)).join('\n') + '\n' : '';
        fs.writeFileSync(VAULT_FILE, content, 'utf8');
      } catch { }
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
