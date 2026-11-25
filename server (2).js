const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '2.1.0';
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

function sanitizeHandle(raw) {
  if (typeof raw !== 'string') return '';
  const cleaned = raw.trim().replace(/^@+/, '').toLowerCase().replace(/[^a-z0-9æøå._-]/g, '').slice(0, 20);
  if (cleaned.length < 3) return '';
  if (/^[._-]|[._-]$|\.\./.test(cleaned)) return '';
  if (!/[a-z0-9æøå]/.test(cleaned)) return '';
  if (RESERVED_HANDLES.has(cleaned)) return '';
  return cleaned;
}

function validateDisplayName(deviceId, raw) {
  const stripped = String(raw || '').replace(/@/g, '').replace(/\s+/g, ' ').trim().slice(0, 24);
  if (!stripped) return { ok: false, error: 'Visningsnavnet kan ikke være tomt.' };
  const norm = stripped.toLowerCase().replace(/[^a-z0-9æøå._-]/g, '');
  if (RESERVED_HANDLES.has(norm)) {
    return { ok: false, error: 'Dette visningsnavnet er reservert.' };
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
    secretTrustedOnly: false
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
let WEB_CLIENT_HTML = Buffer.from('<!doctype html><html><body><h1>Chat v2</h1></body></html>', 'utf8');
try {
  if (WEB_CLIENT_HTML_GZIP_B64 && !WEB_CLIENT_HTML_GZIP_B64.startsWith('__EMBEDDED')) {
    WEB_CLIENT_HTML = zlib.gunzipSync(Buffer.from(WEB_CLIENT_HTML_GZIP_B64, 'base64'));
  }
} catch { }

const server = http.createServer((req, res) => {
  const reqPath = (req.url || '/').split('?')[0];
  if (reqPath === '/health' || reqPath === '/status') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end(`Chat Smart Relay v${SERVER_VERSION} (v5) OK\n`);
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
  for (const [channel, msgs] of channelHistory.entries()) {
    if (!canAccessChannel(ws.meta, channel)) continue;
    for (const m of msgs) {
      safeSend(ws, formatChatPayload(m, isAdmin, undefined));
    }
  }
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

  return {
    type: 'admin_state',
    serverMode: 'cloud-relay',
    serverVersion: SERVER_VERSION,
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

  ws.meta = {
    connId,
    nonce,
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

      const clientVersion = String(msg.clientVersion || '1.0.0').trim().slice(0, 20) || '1.0.0';
      const fallbackUser = 'Bruker-' + devVerify.deviceId.slice(0, 4);
      const checkedName = validateDisplayName(devVerify.deviceId, msg.user || fallbackUser);
      const user = checkedName.ok ? checkedName.name : fallbackUser;
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : '#3498DB';
      const channel = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32) : '#general-1';
      const host = String(msg.host || '').trim().slice(0, 40);

      ws.meta.user = user;
      ws.meta.color = color;
      ws.meta.channel = channel;
      ws.meta.host = host;
      ws.meta.clientVersion = clientVersion;
      ws.meta.deviceId = devVerify.deviceId;
      ws.meta.fingerprint = devVerify.fingerprint;

      // Optional auto-claim handle on first connect if desiredHandle provided & not yet locked
      if (!state.handles[devVerify.deviceId] && msg.desiredHandle) {
        const clean = sanitizeHandle(msg.desiredHandle);
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
        lastSeenIso: formatIsoNow()
      };

      // Strictly PC/Device-ID based ban (NEVER IP-based!)
      if (state.bannedDevices[devVerify.deviceId]) {
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

      if (msg.adminSig) {
        const adminVerify = verifyRsaSha256(ADMIN_PUBKEY_XML, `ADMIN:${ws.meta.nonce}`, msg.adminSig);
        if (adminVerify) {
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

          const lastSeq = typeof msg.lastVaultSeq === 'number' ? msg.lastVaultSeq : 0;
          const missing = vault.filter((r) => r.seq > lastSeq);
          if (missing.length > 0) {
            safeSend(ws, { type: 'admin_vault_sync', records: missing.slice(-300) });
          }
          broadcastAdminState();
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
        const chk = validateDisplayName(ws.meta.deviceId, msg.user);
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

    // Check permanent @handle availability
    if (msg.type === 'check_handle') {
      const clean = sanitizeHandle(msg.handle);
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
      const clean = sanitizeHandle(msg.handle);
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

      const chk = validateDisplayName(myId, msg.user || clean);
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
        const chk = validateDisplayName(ws.meta.deviceId, msg.user);
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
      state.customChannels[slug] = {
        name: slug,
        ownerDeviceId: myId,
        ownerName: ws.meta.user,
        members: [myId],
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
      if (!ch.members.includes(targetId)) {
        ch.members.push(targetId);
        saveState();
        broadcastSocialStates();
        broadcastAdminState();
        for (const c of wss.clients) {
          if (c.meta && c.meta.deviceId === targetId && c.meta.status === 'approved') {
            const hist = channelHistory.get(slug) || [];
            for (const m of hist) {
              safeSend(c, formatChatPayload(m, c.meta.role === 'admin', undefined));
            }
          }
        }
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

      const nameCheck = msg.user ? validateDisplayName(ws.meta.deviceId, msg.user) : { ok: false };
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

      const nameCheck = msg.user ? validateDisplayName(ws.meta.deviceId, msg.user) : { ok: false };
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
      '  clear <kanal|*>               - Tøm meldingshistorikk i kanal',
      '  status                        - Vis serverstatus, online brukere og versjon'
    ].join('\n');
  }

  if (cmd === 'status') {
    const online = Array.from(wss.clients).filter((c) => c.meta && c.meta.status === 'approved');
    const names = online.map((c) => `${c.meta.user}${c.meta.handle ? '(@' + c.meta.handle + ')' : ''}[v${c.meta.clientVersion}]`).join(', ');
    return `Server v${SERVER_VERSION} | Online: ${online.length} (${names || 'ingen'}) | Nyeste klient: v${state.updater.latestVersion} (min v${state.updater.minVersion}) | Global cooldown: ${state.cooldowns.global}s`;
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
    if (targetDev && state.handles[targetDev]) {
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
