const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.2.0';
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
  return { name, size, isImage, data };
}

// Strips binary data so server NEVER stores images or file contents — ONLY filename & size!
function stripFileData(fileObj) {
  if (!fileObj) return null;
  return { name: fileObj.name, size: fileObj.size, isImage: !!fileObj.isImage };
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
// Set UPSTASH_REDIS_REST_URL and UPSTASH_REDIS_REST_TOKEN in Render -> Environment.
// =============================================================================
const UPSTASH_URL = (process.env.UPSTASH_REDIS_REST_URL || process.env.KV_REST_API_URL || '').trim().replace(/\/+$/, '');
const UPSTASH_TOKEN = (process.env.UPSTASH_REDIS_REST_TOKEN || process.env.KV_REST_API_TOKEN || '').trim();
const CLOUD_STATE_KEY = 'minchat:v3:state';
const CLOUD_HISTORY_KEY = 'minchat:v3:history';
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
let cloudSaveDirty = false;
let cloudBootReady = false;

function upstashPost(endpointPath, bodyObj) {
  return new Promise((resolve, reject) => {
    if (!UPSTASH_URL || !UPSTASH_TOKEN) return reject(new Error('Upstash not configured'));
    let parsed;
    try { parsed = new URL(UPSTASH_URL + endpointPath); } catch (e) { return reject(e); }
    const data = JSON.stringify(bodyObj);
    const mod = parsed.protocol === 'http:' ? http : https;
    const req = mod.request({
      hostname: parsed.hostname,
      port: parsed.port || (parsed.protocol === 'http:' ? 80 : 443),
      path: parsed.pathname + parsed.search,
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${UPSTASH_TOKEN}`,
        'Content-Type': 'application/json',
        'Content-Length': Buffer.byteLength(data)
      },
      timeout: 8000
    }, (res) => {
      const chunks = [];
      res.on('data', (c) => chunks.push(c));
      res.on('end', () => {
        const txt = Buffer.concat(chunks).toString('utf8');
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
  const compactVault = vault.slice(-600).map((r) => (r && r.file ? { ...r, file: stripFileData(r.file) } : r));
  return {
    epoch: STATE_EPOCH,
    nextSeq,
    channelHistory: chObj,
    dmHistory: dmObj,
    vault: compactVault
  };
}

async function flushCloudSaveNow() {
  if (!cloudStorage.enabled) return;
  if (cloudSaveTimer) { clearTimeout(cloudSaveTimer); cloudSaveTimer = null; }
  if (cloudSaveInFlight) {
    cloudSaveDirty = true;
    return cloudSaveInFlight;
  }
  cloudSaveDirty = false;
  cloudSaveInFlight = (async () => {
    try {
      const stateJson = JSON.stringify(state);
      const histJson = JSON.stringify(buildCompactHistorySnapshot());
      await upstashPost('/pipeline', [
        ['SET', CLOUD_STATE_KEY, stateJson],
        ['SET', CLOUD_HISTORY_KEY, histJson]
      ]);
      cloudStorage.connected = true;
      cloudStorage.lastSavedIso = formatIsoNow();
      cloudStorage.lastError = '';
    } catch (err) {
      cloudStorage.lastError = String((err && err.message) || err || 'Ukjent feil').slice(0, 180);
    } finally {
      cloudSaveInFlight = null;
      if (cloudSaveDirty) {
        cloudSaveDirty = false;
        scheduleCloudSave(250);
      }
    }
  })();
  return cloudSaveInFlight;
}

function scheduleCloudSave(delayMs = 800) {
  if (!cloudStorage.enabled || !cloudBootReady) return;
  if (cloudSaveTimer) clearTimeout(cloudSaveTimer);
  cloudSaveTimer = setTimeout(() => {
    cloudSaveTimer = null;
    flushCloudSaveNow();
  }, delayMs);
}

async function loadCloudStateOnBoot() {
  if (!cloudStorage.enabled) {
    cloudBootReady = true;
    return;
  }
  try {
    const res = await upstashPost('/pipeline', [
      ['GET', CLOUD_STATE_KEY],
      ['GET', CLOUD_HISTORY_KEY]
    ]);
    cloudStorage.connected = true;
    cloudStorage.lastError = '';
    const rawState = Array.isArray(res) && res[0] && typeof res[0].result === 'string' ? res[0].result : '';
    const rawHist = Array.isArray(res) && res[1] && typeof res[1].result === 'string' ? res[1].result : '';

    let loadedCloudState = false;
    if (rawState) {
      const saved = JSON.parse(rawState);
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
        // Always ensure server updater latestVersion reflects running code version if newer
        if (compareVersions(SERVER_VERSION, state.updater.latestVersion) > 0) {
          state.updater.latestVersion = SERVER_VERSION;
        }
        cloudStorage.lastLoadedIso = formatIsoNow();
      }
    }

    if (loadedCloudState && rawHist) {
      const h = JSON.parse(rawHist);
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
      }
    }

    cloudBootReady = true;
    // Mirror cloud state locally, or seed cloud if local state already existed
    if (loadedCloudState) {
      try {
        fs.mkdirSync(DATA_DIR, { recursive: true });
        fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8');
        const content = vault.length ? vault.map((r) => JSON.stringify(r)).join('\n') + '\n' : '';
        fs.writeFileSync(VAULT_FILE, content, 'utf8');
      } catch { }
      console.log(`Sky-lagring (Upstash Redis) lastet: ${Object.keys(state.accounts).length} kontoer, ${Object.keys(state.customChannels).length} private kanaler.`);
    } else if (Object.keys(state.accounts).length > 0) {
      await flushCloudSaveNow();
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
  scheduleCloudSave();
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
  scheduleCloudSave();
  sendToAdmins({ type: 'admin_log', record: metaRec });
}

function rewriteVaultFile() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const content = vault.length ? vault.map((r) => JSON.stringify(r)).join('\n') + '\n' : '';
    fs.writeFileSync(VAULT_FILE, content, 'utf8');
  } catch { }
  scheduleCloudSave();
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
    cloudStorage: { ...cloudStorage },
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
        flushCloudSaveNow(),
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
