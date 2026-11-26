const http = require('http');
const https = require('https');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '3.6.0';
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

// v3.6.0: Server-side 256 MB RAM Media Ring-Buffer (NEVER persisted to DB/JSON/Vault!)
// Stores raw binary Buffers keyed by sha1 hash so offline users can fetch recent media into their own local PC cache.
const MEDIA_RAM_LIMIT_BYTES = Math.max(16, Number(process.env.MEDIA_RAM_LIMIT_MB) || 256) * 1024 * 1024;
const ramMediaCache = new Map(); // hash -> { buf, mime, name, size, storedAt, scopes: Set<string>, maxUnixMs: number }
let ramMediaBytes = 0;

function storeMediaInRam(liveFile, scopeKey, unixMs) {
  if (!liveFile || !liveFile.data || !liveFile.hash) return;
  let buf;
  try {
    buf = Buffer.from(liveFile.data, 'base64');
  } catch { return; }
  if (!buf || !buf.length || buf.length > MEDIA_RAM_LIMIT_BYTES) return;
  const hash = String(liveFile.hash);
  const ts = Number(unixMs) || Date.now();
  const existing = ramMediaCache.get(hash);
  if (existing) {
    ramMediaCache.delete(hash);
    if (scopeKey) existing.scopes.add(scopeKey);
    if (ts > existing.maxUnixMs) existing.maxUnixMs = ts;
    existing.storedAt = Date.now();
    ramMediaCache.set(hash, existing);
    return;
  }
  while (ramMediaBytes + buf.length > MEDIA_RAM_LIMIT_BYTES && ramMediaCache.size > 0) {
    const oldestKey = ramMediaCache.keys().next().value;
    const oldestVal = ramMediaCache.get(oldestKey);
    ramMediaCache.delete(oldestKey);
    if (oldestVal && oldestVal.buf) ramMediaBytes = Math.max(0, ramMediaBytes - oldestVal.buf.length);
  }
  const scopes = new Set();
  if (scopeKey) scopes.add(scopeKey);
  ramMediaCache.set(hash, {
    buf,
    mime: String(liveFile.mime || 'application/octet-stream').slice(0, 64),
    name: String(liveFile.name || 'fil').slice(0, 80),
    size: buf.length,
    storedAt: Date.now(),
    scopes,
    maxUnixMs: ts
  });
  ramMediaBytes += buf.length;
}

function clearRamMediaCache() {
  ramMediaCache.clear();
  ramMediaBytes = 0;
}

function canAccountAccessRamMedia(acc, entry) {
  if (!acc || !entry) return false;
  if (acc.handle === ADMIN_HANDLE) return true;
  const myId = acc.accountId;
  if (state.bannedDevices[myId]) return false;
  const firstJoined = Number(acc.firstJoinedMs) || 0;
  for (const sc of entry.scopes) {
    if (sc.startsWith('dm:')) {
      const rk = sc.slice(3);
      const parts = rk.split('|');
      if (parts.includes(myId) && entry.maxUnixMs >= firstJoined) return true;
    } else if (sc.startsWith('#')) {
      const canSeeCh = canAccessChannel({ status: 'approved', deviceId: myId, role: acc.role || 'verified', isAdminAccount: false }, sc);
      if (!canSeeCh) continue;
      let cutoff = firstJoined;
      const custom = state.customChannels[sc];
      if (custom && custom.memberJoinedMs && typeof custom.memberJoinedMs[myId] === 'number') {
        cutoff = Math.max(cutoff, custom.memberJoinedMs[myId]);
      }
      if (entry.maxUnixMs >= cutoff) return true;
    }
  }
  return false;
}

// v3.6.0: Hardware / PC Identifier sanitizer & multi-account detector (LOG-ONLY, zero blocking!)
function sanitizeHwInfo(raw, req) {
  const ip = req ? getRequestIp(req) : '';
  const ua = req ? describeUserAgent(req.headers['user-agent'] || '') : '';
  const obj = (raw && typeof raw === 'object') ? raw : {};
  const cleanStr = (v, max) => String(v || '').replace(/[\r\n\t\x00-\x1F]/g, ' ').trim().slice(0, max);
  const hwHash = cleanStr(obj.hwHash, 32).toLowerCase().replace(/[^a-f0-9]/g, '');
  const installId = cleanStr(obj.installId, 48).replace(/[^a-zA-Z0-9_-]/g, '');
  const gpu = cleanStr(obj.gpu, 100);
  const cores = Math.max(0, Math.min(256, Number(obj.cores) || 0));
  const ramGb = Math.max(0, Math.min(1024, Number(obj.ramGb) || 0));
  const screen = cleanStr(obj.screen, 32);
  const platform = cleanStr(obj.platform, 48);
  const tz = cleanStr(obj.tz, 48);
  let summary = cleanStr(obj.summary, 140);
  if (!summary) {
    const bits = [ua || platform, cores ? `${cores} kjerner` : '', ramGb ? `${ramGb} GB RAM` : '', screen, gpu].filter(Boolean);
    summary = bits.join(' · ').slice(0, 140) || 'Ukjent enhet';
  }
  return {
    hwHash,
    installId,
    gpu,
    cores,
    ramGb,
    screen,
    platform,
    tz,
    ua,
    ip,
    summary,
    at: formatIsoNow()
  };
}

function recordAccountDevice(acc, hwInfo, isCreation = false) {
  if (!acc || !hwInfo) return;
  if (isCreation && !acc.createdDevice) {
    acc.createdDevice = hwInfo;
  }
  if (!Array.isArray(acc.seenDevices)) acc.seenDevices = [];
  const key = `${hwInfo.installId}|${hwInfo.hwHash}`;
  if (key !== '|') {
    const idx = acc.seenDevices.findIndex((d) => d && `${d.installId || ''}|${d.hwHash || ''}` === key);
    if (idx >= 0) {
      acc.seenDevices[idx] = { ...acc.seenDevices[idx], ...hwInfo, at: formatIsoNow() };
    } else {
      acc.seenDevices.unshift(hwInfo);
      if (acc.seenDevices.length > 10) acc.seenDevices.pop();
    }
  }
}

function checkAndLogMultiAccount(newAcc, hwInfo) {
  if (!newAcc || !hwInfo) return;
  const pcMatches = [];
  const hwMatches = [];
  for (const [otherId, other] of Object.entries(state.accounts)) {
    if (!other || otherId === newAcc.accountId) continue;
    const devs = [];
    if (other.createdDevice) devs.push(other.createdDevice);
    if (Array.isArray(other.seenDevices)) devs.push(...other.seenDevices);
    const samePc = !!(hwInfo.installId && devs.some((d) => d && d.installId === hwInfo.installId));
    const sameHw = !!(hwInfo.hwHash && devs.some((d) => d && d.hwHash === hwInfo.hwHash));
    if (samePc) pcMatches.push('@' + other.handle);
    else if (sameHw) hwMatches.push('@' + other.handle);
  }
  if (!pcMatches.length && !hwMatches.length) return;
  if (!Array.isArray(state.multiAccountLogs)) state.multiAccountLogs = [];
  const entry = {
    at: formatIsoNow(),
    unixMs: Date.now(),
    accountId: newAcc.accountId,
    handle: newAcc.handle,
    user: newAcc.displayName,
    pcMatches,
    hwMatches,
    installId: hwInfo.installId || '',
    hwHash: hwInfo.hwHash || '',
    summary: hwInfo.summary || '',
    ip: hwInfo.ip || ''
  };
  state.multiAccountLogs.unshift(entry);
  if (state.multiAccountLogs.length > 150) state.multiAccountLogs.pop();
  const matchDesc = [
    pcMatches.length ? `samme PC-ID som ${pcMatches.join(', ')}` : '',
    hwMatches.length ? `samme maskinvare som ${hwMatches.join(', ')}` : ''
  ].filter(Boolean).join(' + ');
  appendVaultRecord({
    seq: nextSeq++,
    type: 'system',
    channel: '#admin-audit',
    user: 'MULTI-KONTO',
    handle: newAcc.handle,
    deviceId: newAcc.accountId,
    ip: hwInfo.ip || '',
    host: hwInfo.summary || '',
    text: `[Multi-konto logget] @${newAcc.handle} opprettet med ${matchDesc} (${hwInfo.summary || 'ukjent enhet'})`,
    time: formatShortTime(),
    isoTime: formatIsoNow(),
    unixMs: Date.now()
  });
}

function computeMultiAccountReport() {
  const byPc = new Map();
  const byHw = new Map();
  const byIp = new Map();
  const linkedByAcc = new Map();

  for (const [accId, acc] of Object.entries(state.accounts)) {
    if (!acc || !acc.handle) continue;
    const devs = [];
    if (acc.createdDevice) devs.push(acc.createdDevice);
    if (Array.isArray(acc.seenDevices)) devs.push(...acc.seenDevices);
    const kn = state.knownDevices[accId];
    const pcSet = new Set();
    const hwSet = new Set();
    const ipSet = new Set();
    for (const d of devs) {
      if (!d) continue;
      if (d.installId) pcSet.add(d.installId);
      if (d.hwHash) hwSet.add(d.hwHash);
      if (d.ip && d.ip !== 'ukjent') ipSet.add(d.ip);
    }
    if (kn && kn.ip && kn.ip !== 'ukjent') ipSet.add(kn.ip);
    const info = { accountId: accId, handle: acc.handle, user: acc.displayName || acc.handle, summary: (acc.createdDevice && acc.createdDevice.summary) || (devs[0] && devs[0].summary) || '' };
    for (const pc of pcSet) {
      if (!byPc.has(pc)) byPc.set(pc, []);
      byPc.get(pc).push(info);
    }
    for (const hw of hwSet) {
      if (!byHw.has(hw)) byHw.set(hw, []);
      byHw.get(hw).push(info);
    }
    for (const ip of ipSet) {
      if (!byIp.has(ip)) byIp.set(ip, []);
      byIp.get(ip).push(info);
    }
  }

  const groups = [];
  for (const [id, members] of byPc.entries()) {
    if (members.length < 2) continue;
    groups.push({ matchType: 'pc_id', id: id.slice(0, 14), summary: members[0].summary || '', accounts: members });
    for (const a of members) {
      if (!linkedByAcc.has(a.accountId)) linkedByAcc.set(a.accountId, new Set());
      for (const b of members) if (b.accountId !== a.accountId) linkedByAcc.get(a.accountId).add('@' + b.handle);
    }
  }
  for (const [id, members] of byHw.entries()) {
    if (members.length < 2) continue;
    groups.push({ matchType: 'hardware', id: id.slice(0, 12), summary: members[0].summary || '', accounts: members });
    for (const a of members) {
      if (!linkedByAcc.has(a.accountId)) linkedByAcc.set(a.accountId, new Set());
      for (const b of members) if (b.accountId !== a.accountId) linkedByAcc.get(a.accountId).add('@' + b.handle);
    }
  }
  for (const [ip, members] of byIp.entries()) {
    if (members.length < 2) continue;
    groups.push({ matchType: 'ip', id: ip, summary: 'Delt nettverk (f.eks. skole/Wi-Fi)', accounts: members });
  }
  return { groups, linkedByAcc };
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
  chatClearEpoch: 0, // v3.6.0: Incremented when admin wipes all chats so offline clients clear stale local cache
  multiAccountLogs: [], // v3.6.0: Log-only record of multi-account PC/hardware matches for Admin
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
    friendRequests: state.friendRequests,
    multiAccountLogs: Array.isArray(state.multiAccountLogs) ? state.multiAccountLogs.slice(0, 150) : []
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
    chatClearEpoch: Number(state.chatClearEpoch) || 0,
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
    ramMediaBytes,
    ramMediaLimitBytes: MEDIA_RAM_LIMIT_BYTES,
    ramMediaCount: ramMediaCache.size,
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
  if (typeof saved.chatClearEpoch === 'number') state.chatClearEpoch = Math.max(state.chatClearEpoch || 0, saved.chatClearEpoch);
  if (Array.isArray(saved.multiAccountLogs)) state.multiAccountLogs = saved.multiAccountLogs.slice(0, 150);
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
    profileNotes: (acc.profileNotes && typeof acc.profileNotes === 'object') ? acc.profileNotes : {},
    firstJoinedMs: Number(acc.firstJoinedMs) || Date.now(),
    createdAt: acc.createdAt || ''
  };
}

function createAccount({ handle, displayName, password, color, role = 'verified', hwInfo = null }) {
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
    gifFavorites: [],
    profileNotes: {},
    createdDevice: hwInfo || null,
    seenDevices: hwInfo ? [hwInfo] : []
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
      if (typeof saved.chatClearEpoch === 'number') state.chatClearEpoch = Math.max(state.chatClearEpoch || 0, saved.chatClearEpoch);
      if (Array.isArray(saved.multiAccountLogs)) state.multiAccountLogs = saved.multiAccountLogs.slice(0, 150);
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

  // --- v3.6.0: Authenticated RAM Media Ring-Buffer Endpoint (0 B stored in DB!) ---
  if (reqPath.startsWith('/api/media/') && req.method === 'GET') {
    const found = getSessionAccount(extractRequestToken(req));
    if (!found) {
      sendJsonRes(res, 401, { ok: false, error: 'Ikke innlogget.' });
      return;
    }
    const hash = decodeURIComponent(reqPath.slice('/api/media/'.length)).replace(/[^a-fA-F0-9]/g, '').slice(0, 32);
    const entry = hash ? ramMediaCache.get(hash) : null;
    if (!entry || !entry.buf) {
      res.writeHead(404, { 'Content-Type': 'application/json; charset=utf-8' });
      res.end(JSON.stringify({ ok: false, error: 'Media er ikke lenger i serverens RAM-buffer.' }));
      return;
    }
    if (!canAccountAccessRamMedia(found.account, entry)) {
      res.writeHead(403, { 'Content-Type': 'application/json; charset=utf-8' });
      res.end(JSON.stringify({ ok: false, error: 'Ingen tilgang.' }));
      return;
    }
    res.writeHead(200, {
      'Content-Type': entry.mime || 'application/octet-stream',
      'Content-Length': entry.buf.length,
      'Cache-Control': 'private, max-age=86400',
      'X-Content-Type-Options': 'nosniff',
      'X-Media-Name': encodeURIComponent(entry.name || 'fil')
    });
    res.end(entry.buf);
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

    const hwInfo = sanitizeHwInfo(body.hwInfo, req);
    const acc = createAccount({
      handle,
      displayName: dispCheck.name,
      password,
      color: body.color,
      role,
      hwInfo
    });
    checkAndLogMultiAccount(acc, hwInfo);
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
    if (body.hwInfo) {
      recordAccountDevice(acc, sanitizeHwInfo(body.hwInfo, req), false);
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
    file: liveFile !== undefined ? liveFile : (m.file ? { ...stripFileData(m.file), inRam: !!(m.file.hash && ramMediaCache.has(m.file.hash)) } : null),
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
    file: liveFile !== undefined ? liveFile : (m.file ? { ...stripFileData(m.file), inRam: !!(m.file.hash && ramMediaCache.has(m.file.hash)) } : null),
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

function getViewerCutoffMs(meta, scope, ch) {
  if (!meta) return Date.now();
  if (meta.role === 'admin') return 0;
  let cutoff = Number(meta.firstJoinedMs) || Date.now();
  if (scope === 'channel' && ch) {
    const custom = state.customChannels[ch];
    if (custom && custom.memberJoinedMs && typeof custom.memberJoinedMs[meta.deviceId] === 'number') {
      cutoff = Math.max(cutoff, custom.memberJoinedMs[meta.deviceId]);
    }
  }
  return cutoff;
}

function resolvePinsForScope(scope, key, list, cutoffMs = 0) {
  const scopeKey = scope === 'dm' ? ('dm:' + key) : key;
  const ids = Array.isArray(state.pins[scopeKey]) ? state.pins[scopeKey] : [];
  if (!ids.length) return [];
  const byId = new Map();
  for (const m of (list || [])) { if (m && m.msgId) byId.set(m.msgId, m); }
  const out = [];
  for (const id of ids) {
    const m = byId.get(id);
    if (!m) continue;
    if (cutoffMs > 0 && msgUnixMs(m) < cutoffMs) continue;
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
function sendHistoryPage(ws, { scope, channel, peerDeviceId, beforeSeq = 0, afterSeq = 0, oldestCachedSeq = 0, limit = HISTORY_PAGE_SIZE }) {
  if (!ws.meta || ws.meta.status !== 'approved') return;
  const isAdmin = ws.meta.role === 'admin';
  const myId = ws.meta.deviceId;
  const cursorBefore = Number(beforeSeq) || 0;
  const cursorAfter = Number(afterSeq) || 0;
  const pageLimit = Math.max(1, Math.min(cursorAfter > 0 ? 150 : 25, Number(limit) || HISTORY_PAGE_SIZE));

  if (scope === 'dm') {
    const peerId = String(peerDeviceId || '').trim();
    if (!peerId) return;
    const rk = dmRoomKey(myId, peerId);
    const all = dmHistory.get(rk) || [];
    const cutoffMs = getViewerCutoffMs(ws.meta, 'dm', '');
    const visible = isAdmin ? all : all.filter((m) => msgUnixMs(m) >= cutoffMs);
    if (cursorAfter > 0) {
      const newer = visible.filter((m) => (Number(m.seq) || 0) > cursorAfter);
      const slice = newer.slice(-pageLimit);
      const refOldest = Number(oldestCachedSeq) || (slice.length ? (Number(slice[0].seq) || 0) : cursorAfter);
      const hasMore = visible.some((m) => (Number(m.seq) || 0) < refOldest);
      safeSend(ws, {
        type: 'history_page',
        scope: 'dm',
        peerDeviceId: peerId,
        prepend: false,
        delta: true,
        hasMore,
        oldestSeq: refOldest,
        messages: slice.map((m) => formatDmPayload(m, isAdmin, undefined))
      });
      return;
    }
    const eligible = cursorBefore > 0 ? visible.filter((m) => (Number(m.seq) || 0) < cursorBefore) : visible;
    const startIdx = Math.max(0, eligible.length - pageLimit);
    const slice = eligible.slice(startIdx);
    const hasMore = startIdx > 0;
    const oldestSeq = slice.length ? (Number(slice[0].seq) || 0) : cursorBefore;
    safeSend(ws, {
      type: 'history_page',
      scope: 'dm',
      peerDeviceId: peerId,
      prepend: cursorBefore > 0,
      hasMore,
      oldestSeq,
      messages: slice.map((m) => formatDmPayload(m, isAdmin, undefined))
    });
    return;
  }

  const ch = typeof channel === 'string' && channel.startsWith('#') ? channel.slice(0, 32).toLowerCase() : '#general-1';
  if (!canAccessChannel(ws.meta, ch)) return;
  const all = channelHistory.get(ch) || [];
  const cutoffMs = getViewerCutoffMs(ws.meta, 'channel', ch);
  const visible = isAdmin ? all : all.filter((m) => msgUnixMs(m) >= cutoffMs);

  if (cursorAfter > 0) {
    const newer = visible.filter((m) => (Number(m.seq) || 0) > cursorAfter);
    const slice = newer.slice(-pageLimit);
    const refOldest = Number(oldestCachedSeq) || (slice.length ? (Number(slice[0].seq) || 0) : cursorAfter);
    const hasMore = visible.some((m) => (Number(m.seq) || 0) < refOldest);
    safeSend(ws, {
      type: 'history_page',
      scope: 'channel',
      channel: ch,
      prepend: false,
      delta: true,
      hasMore,
      oldestSeq: refOldest,
      messages: slice.map((m) => formatChatPayload(m, isAdmin, undefined))
    });
    return;
  }

  const eligible = cursorBefore > 0 ? visible.filter((m) => (Number(m.seq) || 0) < cursorBefore) : visible;
  const startIdx = Math.max(0, eligible.length - pageLimit);
  const slice = eligible.slice(startIdx);
  const hasMore = startIdx > 0;
  const oldestSeq = slice.length ? (Number(slice[0].seq) || 0) : cursorBefore;

  safeSend(ws, {
    type: 'history_page',
    scope: 'channel',
    channel: ch,
    prepend: cursorBefore > 0,
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
  const multiReport = computeMultiAccountReport();
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
      banned: !!(m.deviceId && state.bannedDevices[m.deviceId]),
      createdDevice: (m.deviceId && state.accounts[m.deviceId] && state.accounts[m.deviceId].createdDevice) || null,
      lastDevice: m.hwInfo || (m.deviceId && state.accounts[m.deviceId] && Array.isArray(state.accounts[m.deviceId].seenDevices) && state.accounts[m.deviceId].seenDevices[0]) || null,
      linkedAccounts: (m.deviceId && multiReport.linkedByAcc.has(m.deviceId)) ? Array.from(multiReport.linkedByAcc.get(m.deviceId)) : []
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
      banned: isBanned,
      createdDevice: (state.accounts[devId] && state.accounts[devId].createdDevice) || null,
      lastDevice: (state.accounts[devId] && Array.isArray(state.accounts[devId].seenDevices) && state.accounts[devId].seenDevices[0]) || null,
      linkedAccounts: multiReport.linkedByAcc.has(devId) ? Array.from(multiReport.linkedByAcc.get(devId)) : []
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
    multiAccountGroups: multiReport.groups,
    multiAccountLogs: Array.isArray(state.multiAccountLogs) ? state.multiAccountLogs.slice(0, 60) : [],
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

function admitClientSession(ws, newRole, announceText, opts = {}) {
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
    profileNotes: (ws.meta.deviceId && state.accounts[ws.meta.deviceId] && state.accounts[ws.meta.deviceId].profileNotes) || {},
    firstJoinedMs: Number(ws.meta.firstJoinedMs) || Date.now(),
    chatClearEpoch: Number(state.chatClearEpoch) || 0,
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
  if (!opts.skipInitialReplay) replayHistoryToClient(ws);
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

      if (msg.hwInfo && typeof msg.hwInfo === 'object') {
        const cleanHw = sanitizeHwInfo(msg.hwInfo, null);
        cleanHw.ip = ws.meta.ip;
        cleanHw.ua = ws.meta.deviceInfo || '';
        ws.meta.hwInfo = cleanHw;
        recordAccountDevice(acc, cleanHw, false);
      }
      acc.lastSeenIso = formatIsoNow();
      syncKnownDeviceFromAccount(acc, { clientVersion, ip: ws.meta.ip, host, lastChannel: channel });
      saveState();

      // Start as normal trusted/verified session — zero admin UI or admin perms until RSA-2048 password file verified!
      const role = (isAdminAcc || state.trustedDevices[acc.accountId]) ? 'trusted' : 'verified';
      admitClientSession(ws, role, '', { skipInitialReplay: !!msg.skipInitialReplay });

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

      if (liveFile) storeMediaInRam(liveFile, channel, rec.unixMs);
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

      if (liveFile) storeMediaInRam(liveFile, 'dm:' + rk, dmRec.unixMs);
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
        for (const c of wss.clients) {
          if (c.meta && c.meta.status === 'approved' && canAccessChannel(c.meta, ch)) {
            safeSend(c, { type: 'pins_update', scope: 'channel', channel: ch, pins: resolvePinsForScope('channel', ch, list, getViewerCutoffMs(c.meta, 'channel', ch)) });
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
        safeSend(ws, { type: 'pins_update', scope: 'dm', peerDeviceId: peerId, pins: resolvePinsForScope('dm', rk, list, getViewerCutoffMs(ws.meta, 'dm', '')) });
      } else {
        const ch = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32).toLowerCase() : '#general-1';
        if (!canAccessChannel(ws.meta, ch)) return;
        const list = channelHistory.get(ch) || [];
        safeSend(ws, { type: 'pins_update', scope: 'channel', channel: ch, pins: resolvePinsForScope('channel', ch, list, getViewerCutoffMs(ws.meta, 'channel', ch)) });
      }
      return;
    }

    if (msg.type === 'history_page_req') {
      sendHistoryPage(ws, {
        scope: msg.scope === 'dm' ? 'dm' : 'channel',
        channel: msg.channel,
        peerDeviceId: msg.peerDeviceId,
        beforeSeq: msg.beforeSeq,
        afterSeq: msg.afterSeq,
        oldestCachedSeq: msg.oldestCachedSeq,
        limit: msg.limit
      });
      return;
    }

    // v3.6.0: Private per-user profile notes (ONLY visible to the owning account!)
    if (msg.type === 'set_profile_note') {
      const myId = ws.meta.deviceId;
      const acc = myId ? state.accounts[myId] : null;
      const targetId = String(msg.targetDeviceId || '').trim().slice(0, 64);
      if (!acc || !targetId) return;
      if (!acc.profileNotes || typeof acc.profileNotes !== 'object') acc.profileNotes = {};
      const cleanNote = String(msg.note || '').replace(/[\r\n]+/g, ' ').trim().slice(0, 200);
      if (!cleanNote) {
        delete acc.profileNotes[targetId];
      } else {
        const keys = Object.keys(acc.profileNotes);
        if (!Object.prototype.hasOwnProperty.call(acc.profileNotes, targetId) && keys.length >= 200) {
          delete acc.profileNotes[keys[0]];
        }
        acc.profileNotes[targetId] = cleanNote;
      }
      saveState();
      for (const c of wss.clients) {
        if (c.meta && c.meta.status === 'approved' && c.meta.deviceId === myId) {
          safeSend(c, { type: 'profile_notes_sync', profileNotes: acc.profileNotes });
        }
      }
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
  clearRamMediaCache();
  state.chatClearEpoch = (Number(state.chatClearEpoch) || 0) + 1;
  saveState();
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
