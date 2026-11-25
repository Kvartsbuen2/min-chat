const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '2.2.2';
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
const DEFAULT_CHANNELS = ['#general-1', '#general-2'];
const ALLOWED_REACTIONS = new Set(['👍', '❤️', '😂', '😮', '😢', '🔥', '🎉', '👀', '💀', '💯']);
const RESERVED_HANDLES = new Set(['system', 'server', 'melding', 'varsel']);

// RSA-2048 Public Key for Admin Challenge-Response (private key stays ONLY on Admin's PC!)
const DEFAULT_ADMIN_PUBKEY_XML = '<RSAKeyValue><Modulus>uCZ/7WUZF48t94dqjt4OwPJBuJRoauq2QnoO5PnayAP3nk6duqdw2jTZqNW644NucJZtTIyreh/9PXvTKOx3KoPOLFcSnyXOKEN8rtaoWZRlOCyTwxCFj6tGAZXukBj/4NkMQLUcX7xTnI9cJBNdJYIXtfmTF1m0+q9oao1/LIa4GeC7OJ3M/n+nWuviC2J3HdpETYuK/IJrmBMg0g74syTBkVhl8sHY5ePNrFzBAvcJRlQo5Izej5aynHdJPgX9t0HgLBWkw5n7GEQt/ceA93ftaWm5RcXefHpQZWJ3tOKH7sHGD3HKPoWJuuL+9VNOr0n4LEtqKIGvsmLpz/V9XQ==</Modulus><Exponent>AQAB</Exponent></RSAKeyValue>';
const ADMIN_PUBKEY_XML = (process.env.ADMIN_PUBKEY_XML || DEFAULT_ADMIN_PUBKEY_XML).trim();

const STATE_FILE = path.join(__dirname, 'chat_relay_state.json');
const VAULT_FILE = path.join(__dirname, 'chat_relay_vault.jsonl');

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

function resolveAuthoritativeReply(replyObj, historyList) {
  if (!replyObj || typeof replyObj !== 'object') return null;
  const msgId = String(replyObj.msgId || '').trim().slice(0, 64);
  if (!msgId) return null;
  // Look up the REAL message in server history so nobody can forge a fake quote!
  if (Array.isArray(historyList)) {
    const orig = historyList.find((m) => m.msgId === msgId);
    if (orig) {
      const origDev = orig.deviceId || orig.fromDeviceId || '';
      return {
        msgId: orig.msgId,
        deviceId: origDev,
        user: orig.user || 'Bruker',
        handle: orig.handle || getHandleFor(origDev),
        deviceTag: deviceTagFor(origDev),
        color: orig.color || '#dbdee1',
        text: String(orig.text || (orig.file ? `[Fil: ${orig.file.name}]` : '')).trim().slice(0, 140)
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
  settings: {
    heartbeatEnabled: true,
    heartbeatSec: 30,
    accessMode: 'open', // open | approval | invite | trusted_only
    secretTrustedOnly: false,
    webOnlyMode: true   // Blocks old downloaded apps (Chat.ps1 / old Chat.html) and redirects everyone to the website!
  },
  updater: {
    latestVersion: SERVER_VERSION,
    minVersion: '2.1.0',
    notes: 'Chat v2.1: Svar på meldinger med hopp-til-original, animert skriveindikator nederst, permanent @brukernavn + #ID med anti-utgivelse, og 1-klikk oppdaterer!',
    downloadUrl: 'https://min-chat-qtl0.onrender.com/download',
    driveUrl: 'https://drive.google.com/drive/folders/1cZmN06B0qVD0M9c1HrgZ8pVAVkNwj_bu',
    forceModal: false
  },
  announcement: null, // { id, text, level: 'info'|'warn'|'update', createdAt }
  cooldowns: {
    global: 0,
    channels: {} // "#general-1": 5
  },
  handles: {},        // deviceId -> lockedHandle
  handleOwners: {},   // lockedHandle -> deviceId
  trustedDevices: {},
  verifiedDevices: {},
  bannedDevices: {},
  mutedDevices: {},
  heartbeatOffDevices: {},
  knownDevices: {},
  invites: {},
  friends: {},        // deviceId -> [friendDeviceId, ...]
  friendRequests: {}, // targetDeviceId -> [{ fromDeviceId, fromUser, fromHandle, fromColor, at }, ...]
  customChannels: {}  // "#slug" -> { name, ownerDeviceId, ownerName, members: [deviceId, ...], createdAt }
};

const channelHistory = new Map(); // channel -> [rec WITHOUT file.data!]
const dmHistory = new Map();      // "devA|devB" -> [rec WITHOUT file.data!]
const lastMsgByDeviceChannel = new Map(); // "deviceId|channel" -> unixMs
const vault = [];
let nextSeq = 1;
let nextConnNum = 1;

try {
  if (fs.existsSync(STATE_FILE)) {
    const saved = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    if (saved.settings) Object.assign(state.settings, saved.settings);
    if (saved.updater) Object.assign(state.updater, saved.updater);
    if (saved.announcement !== undefined) state.announcement = saved.announcement;
    if (saved.cooldowns) {
      state.cooldowns.global = Number(saved.cooldowns.global) || 0;
      if (saved.cooldowns.channels) Object.assign(state.cooldowns.channels, saved.cooldowns.channels);
    }
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
  }
  if (fs.existsSync(VAULT_FILE)) {
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
        } else if (rec.type === 'delete' && rec.msgId) {
          if (rec.scope === 'channel' && rec.channel) {
            const arr = channelHistory.get(rec.channel) || [];
            channelHistory.set(rec.channel, arr.filter((m) => m.msgId !== rec.msgId));
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

function saveState() {
  try { fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8'); } catch { }
}

function appendVaultRecord(rec) {
  const metaRec = rec.file ? { ...rec, file: stripFileData(rec.file) } : rec;
  vault.push(metaRec);
  if (vault.length > MAX_VAULT_MEMORY) vault.shift();
  try { fs.appendFileSync(VAULT_FILE, JSON.stringify(metaRec) + '\n', 'utf8'); } catch { }
  sendToAdmins({ type: 'admin_log', record: metaRec });
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

const server = http.createServer((req, res) => {
  const reqPath = (req.url || '/').split('?')[0];
  if (reqPath === '/health' || reqPath === '/status') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end(`Chat Smart Relay v${SERVER_VERSION} (v5) OK\n`);
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
  if (reqPath === '/download' || reqPath === '/Chat.html' || reqPath === '/Chat-v2.html') {
    res.writeHead(200, {
      'Content-Type': 'text/html; charset=utf-8',
      'Content-Disposition': `attachment; filename="Chat-v${state.updater.latestVersion || SERVER_VERSION}.html"`,
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
    if (c.meta && c.meta.role === 'admin' && c.meta.status === 'approved') {
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
  const oldHandle = state.handles[targetDev] || '';
  if (oldHandle === ADMIN_HANDLE) return false; // Never purge the admin handle!
  const oldUser = (state.knownDevices[targetDev] && state.knownDevices[targetDev].user) || 'Bruker';

  if (oldHandle && state.handleOwners[oldHandle] === targetDev) {
    delete state.handleOwners[oldHandle];
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

  safeSend(ws, {
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
  });

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

  ws.isAlive = true;
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
    clientVersion: '1.0.0',
    color: '#3498DB',
    channel: '#general-1',
    host: '',
    winState: 'Synlig',
    deviceId: '',
    fingerprint: 'VENTER',
    role: 'unverified',
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

    if (msg.type === 'client_auth') {
      if (ws.meta.status !== 'handshaking') return;

      const devVerify = verifyRsaSha256(msg.pubKey, `CLIENT:${ws.meta.nonce}`, msg.sig);
      if (!devVerify) {
        safeSend(ws, { type: 'auth_status', status: 'rejected', text: 'Kunne ikke verifisere enhet.' });
        ws.close();
        return;
      }

      // Check cryptographic RSA-2048 Admin signature FIRST!
      const isVerifiedAdmin = !!(msg.adminSig && verifyRsaSha256(ADMIN_PUBKEY_XML, `ADMIN:${ws.meta.nonce}`, msg.adminSig));

      const clientVersion = String(msg.clientVersion || '1.0.0').trim().slice(0, 20) || '1.0.0';
      const fallbackUser = isVerifiedAdmin ? 'Kvartsbuen' : ('Bruker-' + devVerify.deviceId.slice(0, 4));
      const checkedName = validateDisplayName(devVerify.deviceId, msg.user || fallbackUser, isVerifiedAdmin);
      const user = checkedName.ok ? checkedName.name : fallbackUser;
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : '#3498DB';
      const channel = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32) : '#general-1';
      const host = String(msg.host || '').trim().slice(0, 40);

      const existingKnown = state.knownDevices[devVerify.deviceId];
      const firstJoinedMs = (existingKnown && typeof existingKnown.firstJoinedMs === 'number')
        ? existingKnown.firstJoinedMs
        : Date.now();

      ws.meta.user = user;
      ws.meta.color = color;
      ws.meta.channel = channel;
      ws.meta.host = host;
      ws.meta.clientVersion = clientVersion;
      ws.meta.deviceId = devVerify.deviceId;
      ws.meta.fingerprint = devVerify.fingerprint;
      ws.meta.firstJoinedMs = firstJoinedMs;

      // Exclusively lock @kvartsbuen to verified Admin!
      if (isVerifiedAdmin) {
        const oldHandle = state.handles[devVerify.deviceId];
        if (oldHandle && oldHandle !== ADMIN_HANDLE && state.handleOwners[oldHandle] === devVerify.deviceId) {
          delete state.handleOwners[oldHandle];
        }
        const prevOwner = state.handleOwners[ADMIN_HANDLE];
        if (prevOwner && prevOwner !== devVerify.deviceId) {
          delete state.handles[prevOwner];
        }
        state.handles[devVerify.deviceId] = ADMIN_HANDLE;
        state.handleOwners[ADMIN_HANDLE] = devVerify.deviceId;
      } else {
        // Optional auto-claim handle on first connect if desiredHandle provided & not yet locked
        if (!state.handles[devVerify.deviceId] && msg.desiredHandle) {
          const clean = sanitizeHandle(msg.desiredHandle, false);
          if (clean && !state.handleOwners[clean]) {
            state.handles[devVerify.deviceId] = clean;
            state.handleOwners[clean] = devVerify.deviceId;
          }
        }
        // Legacy non-v2 clients get a permanent deterministic ID handle so nobody is ever unidentified!
        if (!state.handles[devVerify.deviceId] && !clientVersion.startsWith('2.')) {
          const legacyHandle = ('id-' + devVerify.deviceId.slice(0, 6)).toLowerCase();
          if (!state.handleOwners[legacyHandle]) {
            state.handles[devVerify.deviceId] = legacyHandle;
            state.handleOwners[legacyHandle] = devVerify.deviceId;
          }
        }
      }
      ws.meta.handle = state.handles[devVerify.deviceId] || '';

      state.knownDevices[devVerify.deviceId] = {
        deviceId: devVerify.deviceId,
        fingerprint: devVerify.fingerprint,
        user,
        handle: ws.meta.handle,
        clientVersion,
        color,
        ip: ws.meta.ip,
        host,
        lastChannel: channel,
        firstJoinedMs,
        lastSeenIso: formatIsoNow()
      };

      // Strictly PC/Device-ID based ban (NEVER IP-based!)
      if (state.bannedDevices[devVerify.deviceId] && !isVerifiedAdmin) {
        saveState();
        safeSend(ws, {
          type: 'auth_status',
          status: 'banned',
          text: 'Denne enheten har ikke tilgang.'
        });
        ws.close();
        broadcastAdminState();
        return;
      }

      if (isVerifiedAdmin) {
        state.trustedDevices[devVerify.deviceId] = {
          deviceId: devVerify.deviceId,
          fingerprint: devVerify.fingerprint,
          user,
          addedAt: formatIsoNow()
        };
        saveState();
        // Stealth join message: identical to any normal user!
        const label = ws.meta.handle ? `${user} (@${ws.meta.handle})` : user;
        admitClientSession(ws, 'admin', `${label} logget på`);

        // Deliver privileged Admin Panel UI ONLY to cryptographically verified @kvartsbuen Admin!
        if (ADMIN_BUNDLE_OBJ) {
          safeSend(ws, { type: 'admin_ui_bundle', ...ADMIN_BUNDLE_OBJ });
        }

        const lastSeq = typeof msg.lastVaultSeq === 'number' ? msg.lastVaultSeq : 0;
        const missing = vault.filter((r) => r.seq > lastSeq);
        if (missing.length > 0) {
          safeSend(ws, { type: 'admin_vault_sync', records: missing.slice(-300) });
        }
        broadcastAdminState();
        return;
      }

      // Block ALL old downloaded apps (Chat.ps1, Start Chat.vbs, local file:// Chat.html) when webOnlyMode is ON!
      if (state.settings.webOnlyMode) {
        const isWebOrigin = /^https?:\/\//i.test(ws.meta.origin);
        const isCurrentWeb = isWebOrigin && compareVersions(clientVersion, '2.2.0') >= 0;
        if (!isCurrentWeb) {
          ws.meta.status = 'rejected';
          safeSend(ws, {
            type: 'updater_push',
            serverVersion: SERVER_VERSION,
            updater: {
              latestVersion: SERVER_VERSION,
              minVersion: '9.9.9',
              notes: `Den gamle app-filen er nå stengt! Slett den gamle filen og bruk den nye nettsiden isteden: ${PUBLIC_WEB_URL}`,
              downloadUrl: PUBLIC_WEB_URL,
              driveUrl: PUBLIC_WEB_URL,
              forceModal: true
            },
            announcement: {
              id: 'web-only-notice',
              level: 'warn',
              text: `Gammel app er stengt! Åpne nettsiden isteden: ${PUBLIC_WEB_URL}`,
              createdAt: formatIsoNow()
            }
          });
          safeSend(ws, {
            type: 'auth_status',
            status: 'rejected',
            text: `Den gamle appen brukes ikke lenger! Åpne nettsiden isteden: ${PUBLIC_WEB_URL}`
          });
          setTimeout(() => { try { ws.close(); } catch { } }, 150);
          return;
        }
      }

      const joinLabel = ws.meta.handle ? `${user} (@${ws.meta.handle})` : user;

      if (state.trustedDevices[devVerify.deviceId]) {
        state.trustedDevices[devVerify.deviceId].user = user;
        saveState();
        admitClientSession(ws, 'trusted', `${joinLabel} logget på`);
        broadcastAdminState();
        return;
      }

      const code = String(msg.inviteCode || '').trim().toUpperCase();
      if (code && state.invites[code]) {
        const inv = state.invites[code];
        if (inv.usesLeft > 0) {
          inv.usesLeft -= 1;
          if (inv.usesLeft <= 0) delete state.invites[code];
          if (inv.autoTrust) {
            state.trustedDevices[devVerify.deviceId] = { deviceId: devVerify.deviceId, fingerprint: devVerify.fingerprint, user, addedAt: formatIsoNow() };
            saveState();
            admitClientSession(ws, 'trusted', `${joinLabel} logget på`);
          } else {
            state.verifiedDevices[devVerify.deviceId] = { deviceId: devVerify.deviceId, fingerprint: devVerify.fingerprint, user, addedAt: formatIsoNow() };
            saveState();
            admitClientSession(ws, 'verified', `${joinLabel} logget på`);
          }
          broadcastAdminState();
          return;
        }
      }

      if (state.verifiedDevices[devVerify.deviceId] && (state.settings.accessMode === 'approval' || state.settings.accessMode === 'open')) {
        saveState();
        admitClientSession(ws, 'verified', `${joinLabel} logget på`);
        broadcastAdminState();
        return;
      }

      if (state.settings.accessMode === 'open') {
        state.verifiedDevices[devVerify.deviceId] = { deviceId: devVerify.deviceId, fingerprint: devVerify.fingerprint, user, addedAt: formatIsoNow() };
        saveState();
        admitClientSession(ws, 'verified', `${joinLabel} logget på`);
        broadcastAdminState();
        return;
      }

      if (state.settings.accessMode === 'trusted_only') {
        saveState();
        safeSend(ws, { type: 'auth_status', status: 'rejected', text: 'Serveren er låst akkurat nå.' });
        ws.close();
        broadcastAdminState();
        return;
      }

      ws.meta.role = 'pending';
      ws.meta.status = 'pending';
      saveState();
      safeSend(ws, { type: 'auth_status', status: 'pending', text: 'Venter på tilgang...' });
      broadcastAdminState();
      return;
    }

    if (msg.type === 'heartbeat') {
      ws.meta.lastHeartbeatMs = Date.now();
      ws.meta.lastHeartbeatIso = formatIsoNow();
      let changed = false;
      if (typeof msg.user === 'string' && msg.user.trim()) {
        const chk = validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin');
        if (chk.ok && chk.name !== ws.meta.user) { ws.meta.user = chk.name; changed = true; }
      }
      if (/^#[0-9A-Fa-f]{6}$/.test(msg.color) && msg.color !== ws.meta.color) {
        ws.meta.color = msg.color; changed = true;
      }
      if (typeof msg.channel === 'string' && msg.channel.startsWith('#')) ws.meta.channel = msg.channel.slice(0, 32);
      if (typeof msg.winState === 'string') ws.meta.winState = msg.winState.slice(0, 20);
      if (typeof msg.rttMs === 'number' && msg.rttMs >= 0) ws.meta.rttMs = Math.round(msg.rttMs);

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
      if (ws.meta.role !== 'admin' || ws.meta.status !== 'approved') return;
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

    // Check permanent @handle availability
    if (msg.type === 'check_handle') {
      const rawClean = String(msg.handle || '').trim().replace(/^@+/, '').toLowerCase();
      if (rawClean === ADMIN_HANDLE && ws.meta.role !== 'admin') {
        safeSend(ws, { type: 'handle_check', handle: rawClean, available: false, reason: `@${ADMIN_HANDLE} er allerede tatt.` });
        return;
      }
      const clean = sanitizeHandle(msg.handle, ws.meta.role === 'admin');
      if (!clean) {
        safeSend(ws, { type: 'handle_check', handle: '', available: false, reason: 'Må være 3–20 tegn (bokstaver, tall, . _ -)' });
        return;
      }
      const owner = state.handleOwners[clean];
      const available = !owner || owner === ws.meta.deviceId;
      safeSend(ws, {
        type: 'handle_check',
        handle: clean,
        available,
        reason: available ? `@${clean} er ledig!` : `@${clean} er allerede tatt.`
      });
      return;
    }

    // Permanently claim & lock @handle to this deviceId (ONE TIME ONLY!)
    if (msg.type === 'claim_handle') {
      const myId = ws.meta.deviceId;
      if (state.handles[myId]) {
        safeSend(ws, {
          type: 'handle_result',
          ok: false,
          lockedHandle: state.handles[myId],
          error: `Brukernavnet ditt er allerede låst til @${state.handles[myId]} og kan ikke endres.`
        });
        return;
      }
      const rawClean = String(msg.handle || '').trim().replace(/^@+/, '').toLowerCase();
      if (rawClean === ADMIN_HANDLE && ws.meta.role !== 'admin') {
        safeSend(ws, { type: 'handle_result', ok: false, error: `Brukernavnet @${ADMIN_HANDLE} er allerede tatt. Velg et annet.` });
        return;
      }
      const clean = sanitizeHandle(msg.handle, ws.meta.role === 'admin');
      if (!clean) {
        safeSend(ws, { type: 'handle_result', ok: false, error: 'Ugyldig brukernavn. Bruk 3–20 tegn (a-å, 0-9, ., _, -).' });
        return;
      }
      if (state.handleOwners[clean] && state.handleOwners[clean] !== myId) {
        safeSend(ws, { type: 'handle_result', ok: false, error: `Brukernavnet @${clean} er allerede tatt. Velg et annet.` });
        return;
      }

      state.handles[myId] = clean;
      state.handleOwners[clean] = myId;
      ws.meta.handle = clean;

      const chk = validateDisplayName(myId, msg.user || clean, ws.meta.role === 'admin');
      if (chk.ok) ws.meta.user = chk.name;
      else ws.meta.user = clean;
      if (/^#[0-9A-Fa-f]{6}$/.test(msg.color)) ws.meta.color = msg.color;

      if (state.knownDevices[myId]) {
        state.knownDevices[myId].handle = clean;
        state.knownDevices[myId].user = ws.meta.user;
        state.knownDevices[myId].color = ws.meta.color;
      }
      saveState();

      safeSend(ws, {
        type: 'handle_result',
        ok: true,
        handle: clean,
        deviceTag: deviceTagFor(myId),
        user: ws.meta.user,
        color: ws.meta.color
      });
      broadcastSocialStates();
      broadcastAdminState();
      return;
    }

    // Instant live Display Name / color update (keeps PC-locked deviceId & @handle intact, blocks impersonation!)
    if (msg.type === 'update_profile') {
      const nc = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : ws.meta.color;
      if (typeof msg.user === 'string' && msg.user.trim()) {
        const chk = validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin');
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
      if (ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId] && ws.meta.role !== 'admin') {
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
      if (cdSec > 0 && ws.meta.role !== 'admin') {
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
      if (!text && !liveFile) return;

      const nameCheck = msg.user ? validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin') : { ok: false };
      const user = nameCheck.ok ? nameCheck.name : (ws.meta.user || 'Ukjent');
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : ws.meta.color;
      const nameChanged = ws.meta.user !== user || ws.meta.color !== color;
      ws.meta.user = user;
      ws.meta.color = color;
      ws.meta.channel = channel;
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
        text: text || (metaFile ? `[Fil: ${metaFile.name} (${Math.round(metaFile.size / 1024)} KB)]` : ''),
        replyTo: resolveAuthoritativeReply(msg.replyTo, arr),
        reactions: {},
        edited: false,
        editedAt: '',
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
      if (ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId] && ws.meta.role !== 'admin') return;
      if (String(ws.meta.clientVersion || '').startsWith('2.') && !ws.meta.handle) {
        safeSend(ws, { type: 'social_notice', text: 'Velg ditt faste @brukernavn først.' });
        return;
      }
      const toDeviceId = String(msg.toDeviceId || '').trim();
      if (!toDeviceId || toDeviceId === ws.meta.deviceId) return;

      const text = typeof msg.text === 'string' ? msg.text.trim().slice(0, 1000) : '';
      const liveFile = sanitizeLiveAttachment(msg.file);
      if (!text && !liveFile) return;

      const nameCheck = msg.user ? validateDisplayName(ws.meta.deviceId, msg.user, ws.meta.role === 'admin') : { ok: false };
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
        text: text || (metaFile ? `[Fil: ${metaFile.name} (${Math.round(metaFile.size / 1024)} KB)]` : ''),
        replyTo: resolveAuthoritativeReply(msg.replyTo, arr),
        reactions: {},
        edited: false,
        editedAt: '',
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
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].lastSeenIso = formatIsoNow();
      }
      const label = ws.meta.handle ? `${ws.meta.user} (@${ws.meta.handle})` : ws.meta.user;
      recordAndBroadcastSystem('#general-1', `${label} logget av`, ws.meta);
    }
    broadcastSocialStates();
    broadcastAdminState();
  });
});

function findDeviceIdByQuery(rawQuery) {
  const q = String(rawQuery || '').trim();
  if (!q) return '';
  if (state.knownDevices[q] || state.handles[q]) return q;
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
  const oldHandle = state.handles[targetDev] || '';
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

  state.settings = { ...state.settings, ...copyObj(src.settings, {}) };
  state.updater = { ...state.updater, ...copyObj(src.updater, {}) };
  state.announcement = src.announcement && typeof src.announcement === 'object' ? JSON.parse(JSON.stringify(src.announcement)) : null;
  state.cooldowns = {
    global: Number(src.cooldowns && src.cooldowns.global) || 0,
    channels: copyObj(src.cooldowns && src.cooldowns.channels, {})
  };
  state.handles = copyObj(src.handles, {});
  state.handleOwners = {};
  for (const [devId, h] of Object.entries(state.handles)) {
    if (typeof h === 'string' && h) state.handleOwners[h] = devId;
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

  // Always guarantee verified Admin owns @kvartsbuen
  if (adminDevId) {
    const prevOwner = state.handleOwners[ADMIN_HANDLE];
    if (prevOwner && prevOwner !== adminDevId) delete state.handles[prevOwner];
    state.handles[adminDevId] = ADMIN_HANDLE;
    state.handleOwners[ADMIN_HANDLE] = adminDevId;
    if (state.knownDevices[adminDevId]) state.knownDevices[adminDevId].handle = ADMIN_HANDLE;
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

  const userCount = Object.keys(state.knownDevices).length;
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
      '  deluser <@bruker|id>          - Slett en brukerkonto permanent',
      '  clear <kanal|*>               - Tøm meldingshistorikk i kanal',
      '  reload-all                    - Last inn nettsiden på nytt for alle',
      '  status                        - Vis serverstatus, online brukere og versjon'
    ].join('\n');
  }

  if (cmd === 'status') {
    const online = Array.from(wss.clients).filter((c) => c.meta && c.meta.status === 'approved');
    const names = online.map((c) => `${c.meta.user}${c.meta.handle ? '(@' + c.meta.handle + ')' : ''}[v${c.meta.clientVersion}]`).join(', ');
    return `Server v${SERVER_VERSION} | Online: ${online.length} (${names || 'ingen'}) | Nyeste klient: v${state.updater.latestVersion} (min v${state.updater.minVersion}) | Global cooldown: ${state.cooldowns.global}s`;
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
    if (ch === '*') channelHistory.clear();
    else channelHistory.delete(ch);
    broadcastToAllApproved({ type: 'admin_notice', action: 'clear_chat', channel: ch });
    return `Tømte historikk for ${ch}.`;
  }

  if (cmd === 'reload-all' || cmd === 'reload') {
    broadcastToAllApproved({ type: 'reload_page', serverVersion: SERVER_VERSION });
    return 'Sendte oppdaterings-/reload-signal til alle tilkoblede nettlesere.';
  }

  return `Ukjent kommando: "${cmd}". Skriv "help" for liste.`;
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
      admitClientSession(sock, newRole, `${sock.meta.user} logget på`);
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
        admitClientSession(sock, 'trusted', `${sock.meta.user} logget på`);
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
    if (typeof cmd.webOnlyMode === 'boolean') {
      state.settings.webOnlyMode = cmd.webOnlyMode;
      if (state.settings.webOnlyMode) {
        for (const c of wss.clients) {
          if (!c.meta || c.meta.role === 'admin') continue;
          const isWebOrigin = /^https?:\/\//i.test(c.meta.origin || '');
          const isCurrentWeb = isWebOrigin && compareVersions(c.meta.clientVersion || '1.0.0', '2.2.0') >= 0;
          if (!isCurrentWeb) {
            safeSend(c, { type: 'auth_status', status: 'rejected', text: `Den gamle appen er stengt! Åpne nettsiden isteden: ${PUBLIC_WEB_URL}` });
            setTimeout(() => { try { c.close(); } catch { } }, 150);
          }
        }
      }
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
    if (ch === '*') channelHistory.clear();
    else channelHistory.delete(ch);
    for (const c of wss.clients) {
      if (c.meta && c.meta.status === 'approved') safeSend(c, { type: 'admin_notice', action: 'clear_chat', channel: ch });
    }
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

server.listen(PORT, () => {
  console.log(`Chat Smart Relay v${SERVER_VERSION} (v5) lytter på port ${PORT}`);
});
