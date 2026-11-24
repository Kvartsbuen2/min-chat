const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const MAX_CHANNEL_HISTORY = 30;
const MAX_VAULT_MEMORY = 5000;

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

const state = {
  settings: {
    heartbeatEnabled: true,
    heartbeatSec: 30,
    accessMode: 'approval', // approval | invite | trusted_only | open
    secretTrustedOnly: true
  },
  trustedDevices: {},
  verifiedDevices: {},
  bannedDevices: {},
  bannedIps: {},
  mutedDevices: {},
  heartbeatOffDevices: {},
  knownDevices: {},
  invites: {}
};

const channelHistory = new Map();
const vault = [];
let nextSeq = 1;
let nextConnNum = 1;

try {
  if (fs.existsSync(STATE_FILE)) {
    const saved = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    if (saved.settings) Object.assign(state.settings, saved.settings);
    if (saved.trustedDevices) Object.assign(state.trustedDevices, saved.trustedDevices);
    if (saved.verifiedDevices) Object.assign(state.verifiedDevices, saved.verifiedDevices);
    if (saved.bannedDevices) Object.assign(state.bannedDevices, saved.bannedDevices);
    if (saved.bannedIps) Object.assign(state.bannedIps, saved.bannedIps);
    if (saved.mutedDevices) Object.assign(state.mutedDevices, saved.mutedDevices);
    if (saved.heartbeatOffDevices) Object.assign(state.heartbeatOffDevices, saved.heartbeatOffDevices);
    if (saved.knownDevices) Object.assign(state.knownDevices, saved.knownDevices);
    if (saved.invites) Object.assign(state.invites, saved.invites);
  }
  if (fs.existsSync(VAULT_FILE)) {
    const lines = fs.readFileSync(VAULT_FILE, 'utf8').split(/\r?\n/).filter(Boolean);
    for (const line of lines.slice(-MAX_VAULT_MEMORY)) {
      try {
        const rec = JSON.parse(line);
        vault.push(rec);
        if (typeof rec.seq === 'number' && rec.seq >= nextSeq) nextSeq = rec.seq + 1;
        if (rec.type === 'chat' && rec.channel) {
          const arr = channelHistory.get(rec.channel) || [];
          arr.push(rec);
          if (arr.length > MAX_CHANNEL_HISTORY) arr.shift();
          channelHistory.set(rec.channel, arr);
        }
      } catch { }
    }
  }
} catch { }

function saveState() {
  try { fs.writeFileSync(STATE_FILE, JSON.stringify(state, null, 2), 'utf8'); } catch { }
}

function appendVaultRecord(rec) {
  vault.push(rec);
  if (vault.length > MAX_VAULT_MEMORY) vault.shift();
  try { fs.appendFileSync(VAULT_FILE, JSON.stringify(rec) + '\n', 'utf8'); } catch { }
  sendToAdmins({ type: 'admin_log', record: rec });
}

const server = http.createServer((req, res) => {
  res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end('Chat Smart Relay v2 OK\n');
});

const wss = new WebSocketServer({ server, maxPayload: 64 * 1024 });

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

function canAccessChannel(meta, channel) {
  if (!meta || meta.status !== 'approved') return false;
  if (channel === '#hemmelig' && state.settings.secretTrustedOnly) {
    return meta.role === 'admin' || meta.role === 'trusted';
  }
  return true;
}

function effectiveHeartbeatFor(deviceId) {
  if (!state.settings.heartbeatEnabled) return false;
  if (deviceId && state.heartbeatOffDevices[deviceId]) return false;
  return true;
}

function pushConfigToClient(ws) {
  if (!ws.meta) return;
  safeSend(ws, {
    type: 'config_push',
    heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
    globalHeartbeatEnabled: state.settings.heartbeatEnabled,
    heartbeatSec: state.settings.heartbeatSec,
    accessMode: state.settings.accessMode,
    secretTrustedOnly: state.settings.secretTrustedOnly,
    role: ws.meta.role,
    status: ws.meta.status,
    muted: !!(ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId]),
    fingerprint: ws.meta.fingerprint || ''
  });
}

function replayHistoryToClient(ws) {
  if (!ws.meta || ws.meta.status !== 'approved') return;
  for (const [channel, msgs] of channelHistory.entries()) {
    if (!canAccessChannel(ws.meta, channel)) continue;
    for (const m of msgs) {
      safeSend(ws, {
        type: 'chat',
        msgId: m.msgId,
        channel: m.channel,
        user: m.user,
        color: m.color,
        role: m.role,
        fingerprint: m.fingerprint,
        text: m.text,
        time: m.time,
        isoTime: m.isoTime
      });
    }
  }
}

function buildAdminStateSnapshot() {
  const activeByDevice = new Set();
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
      color: m.color,
      deviceId: m.deviceId || '',
      fingerprint: m.fingerprint || 'UKJENT',
      ip: m.ip,
      host: m.host || '',
      channel: m.channel || '#generelt',
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

  return {
    type: 'admin_state',
    serverMode: 'cloud-relay',
    serverTimeIso: formatIsoNow(),
    totalVaultRecords: vault.length,
    settings: state.settings,
    invites: Object.values(state.invites),
    clients
  };
}

function broadcastAdminState() {
  sendToAdmins(buildAdminStateSnapshot());
}

function broadcastChatOrSystem(record) {
  for (const c of wss.clients) {
    if (!c.meta || c.meta.status !== 'approved') continue;
    if (!canAccessChannel(c.meta, record.channel)) continue;
    if (record.type === 'chat') {
      safeSend(c, {
        type: 'chat',
        msgId: record.msgId,
        channel: record.channel,
        user: record.user,
        color: record.color,
        role: record.role,
        fingerprint: record.fingerprint,
        text: record.text,
        time: record.time,
        isoTime: record.isoTime
      });
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
    channel: channel || '#generelt',
    user: actorMeta ? actorMeta.user : 'SYSTEM',
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
  broadcastChatOrSystem(rec);
}

function admitClientSession(ws, newRole, announceText) {
  ws.meta.role = newRole;
  ws.meta.status = 'approved';
  ws.meta.lastHeartbeatMs = Date.now();
  ws.meta.lastHeartbeatIso = formatIsoNow();

  safeSend(ws, {
    type: 'auth_status',
    status: 'approved',
    role: newRole,
    fingerprint: ws.meta.fingerprint,
    heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
    heartbeatSec: state.settings.heartbeatSec,
    secretTrustedOnly: state.settings.secretTrustedOnly,
    text: newRole === 'admin'
      ? 'Autentisert som Administrator (RSA-2048 verifisert).'
      : (newRole === 'trusted'
          ? `Tilkoblet som Klarert bruker ★ (${ws.meta.fingerprint}).`
          : `Tilkoblet og godkjent ✓ (${ws.meta.fingerprint}).`)
  });

  pushConfigToClient(ws);
  replayHistoryToClient(ws);

  if (announceText) {
    recordAndBroadcastSystem(ws.meta.channel || '#generelt', announceText, ws.meta);
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
    color: '#3498DB',
    channel: '#generelt',
    host: '',
    winState: 'Synlig',
    deviceId: '',
    fingerprint: 'VENTER',
    role: 'unverified',
    status: 'handshaking',
    connectedAt: formatIsoNow(),
    lastHeartbeatMs: Date.now(),
    lastHeartbeatIso: formatIsoNow(),
    rttMs: 0
  };

  if (state.bannedIps[cleanIp]) {
    safeSend(ws, { type: 'auth_status', status: 'banned', text: 'IP-adressen din er blokkert av administrator.' });
    ws.close();
    return;
  }

  safeSend(ws, {
    type: 'hello_challenge',
    nonce,
    serverMode: 'cloud-relay',
    accessMode: state.settings.accessMode,
    heartbeatEnabled: state.settings.heartbeatEnabled,
    heartbeatSec: state.settings.heartbeatSec,
    secretTrustedOnly: state.settings.secretTrustedOnly
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
        safeSend(ws, { type: 'auth_status', status: 'rejected', text: 'Ugyldig kryptografisk enhetsnøkkel.' });
        ws.close();
        return;
      }

      const user = String(msg.user || 'Anonym').trim().slice(0, 28) || 'Anonym';
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : '#3498DB';
      const channel = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32) : '#generelt';
      const host = String(msg.host || '').trim().slice(0, 40);

      ws.meta.user = user;
      ws.meta.color = color;
      ws.meta.channel = channel;
      ws.meta.host = host;
      ws.meta.deviceId = devVerify.deviceId;
      ws.meta.fingerprint = devVerify.fingerprint;

      state.knownDevices[devVerify.deviceId] = {
        deviceId: devVerify.deviceId,
        fingerprint: devVerify.fingerprint,
        user,
        color,
        ip: ws.meta.ip,
        host,
        lastChannel: channel,
        lastSeenIso: formatIsoNow()
      };

      if (state.bannedDevices[devVerify.deviceId]) {
        saveState();
        safeSend(ws, {
          type: 'auth_status',
          status: 'banned',
          fingerprint: devVerify.fingerprint,
          text: `Enheten (${devVerify.fingerprint}) er blokkert av administrator.`
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
            note: 'Administrator-PC',
            addedAt: formatIsoNow()
          };
          saveState();
          admitClientSession(ws, 'admin', `⚡ ${user} (Admin) logget på`);

          const lastSeq = typeof msg.lastVaultSeq === 'number' ? msg.lastVaultSeq : 0;
          const missing = vault.filter((r) => r.seq > lastSeq);
          if (missing.length > 0) {
            safeSend(ws, { type: 'admin_vault_sync', records: missing });
          }
          broadcastAdminState();
          return;
        }
      }

      if (state.trustedDevices[devVerify.deviceId]) {
        state.trustedDevices[devVerify.deviceId].user = user;
        saveState();
        admitClientSession(ws, 'trusted', `★ ${user} logget på`);
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
            state.trustedDevices[devVerify.deviceId] = {
              deviceId: devVerify.deviceId,
              fingerprint: devVerify.fingerprint,
              user,
              note: `Invitasjon (${code})`,
              addedAt: formatIsoNow()
            };
            saveState();
            admitClientSession(ws, 'trusted', `★ ${user} ble klarert med invitasjonskode`);
          } else {
            state.verifiedDevices[devVerify.deviceId] = {
              deviceId: devVerify.deviceId,
              fingerprint: devVerify.fingerprint,
              user,
              addedAt: formatIsoNow()
            };
            saveState();
            admitClientSession(ws, 'verified', `${user} logget på med invitasjonskode`);
          }
          broadcastAdminState();
          return;
        }
      }

      if (state.verifiedDevices[devVerify.deviceId] && (state.settings.accessMode === 'approval' || state.settings.accessMode === 'open')) {
        saveState();
        admitClientSession(ws, 'verified', `${user} logget på`);
        broadcastAdminState();
        return;
      }

      if (state.settings.accessMode === 'open') {
        state.verifiedDevices[devVerify.deviceId] = {
          deviceId: devVerify.deviceId,
          fingerprint: devVerify.fingerprint,
          user,
          addedAt: formatIsoNow()
        };
        saveState();
        admitClientSession(ws, 'verified', `${user} logget på`);
        broadcastAdminState();
        return;
      }

      if (state.settings.accessMode === 'trusted_only') {
        saveState();
        safeSend(ws, {
          type: 'auth_status',
          status: 'rejected',
          fingerprint: devVerify.fingerprint,
          text: `Serveren er låst til kun klarerte enheter (★). Din enhetskode: ${devVerify.fingerprint}`
        });
        ws.close();
        broadcastAdminState();
        return;
      }

      ws.meta.role = 'pending';
      ws.meta.status = 'pending';
      saveState();
      safeSend(ws, {
        type: 'auth_status',
        status: 'pending',
        fingerprint: devVerify.fingerprint,
        text: state.settings.accessMode === 'invite'
          ? `Ugyldig/manglende invitasjonskode. Venter på evt. manuell godkjenning (Enhetskode: ${devVerify.fingerprint})...`
          : `Venter på godkjenning fra administrator... Oppgi enhetskode: ${devVerify.fingerprint}`
      });
      broadcastAdminState();
      return;
    }

    if (msg.type === 'heartbeat') {
      ws.meta.lastHeartbeatMs = Date.now();
      ws.meta.lastHeartbeatIso = formatIsoNow();
      if (typeof msg.user === 'string' && msg.user.trim()) ws.meta.user = msg.user.trim().slice(0, 28);
      if (/^#[0-9A-Fa-f]{6}$/.test(msg.color)) ws.meta.color = msg.color;
      if (typeof msg.channel === 'string' && msg.channel.startsWith('#')) ws.meta.channel = msg.channel.slice(0, 32);
      if (typeof msg.winState === 'string') ws.meta.winState = msg.winState.slice(0, 20);
      if (typeof msg.rttMs === 'number' && msg.rttMs >= 0) ws.meta.rttMs = Math.round(msg.rttMs);

      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].user = ws.meta.user;
        state.knownDevices[ws.meta.deviceId].lastChannel = ws.meta.channel;
        state.knownDevices[ws.meta.deviceId].lastSeenIso = ws.meta.lastHeartbeatIso;
      }

      safeSend(ws, {
        type: 'heartbeat_ack',
        clientTs: msg.clientTs || Date.now(),
        heartbeatEnabled: effectiveHeartbeatFor(ws.meta.deviceId),
        heartbeatSec: state.settings.heartbeatSec
      });
      broadcastAdminState();
      return;
    }

    if (msg.type === 'admin_cmd') {
      if (ws.meta.role !== 'admin' || ws.meta.status !== 'approved') {
        safeSend(ws, { type: 'system', channel: '#generelt', text: 'Ingen administratortilgang.' });
        return;
      }
      handleAdminCommand(ws, msg);
      return;
    }

    if (ws.meta.status !== 'approved') {
      safeSend(ws, {
        type: 'system',
        channel: '#generelt',
        text: `Du venter fortsatt på godkjenning (Enhetskode: ${ws.meta.fingerprint}).`
      });
      return;
    }

    if (msg.type === 'chat') {
      if (ws.meta.deviceId && state.mutedDevices[ws.meta.deviceId] && ws.meta.role !== 'admin') {
        safeSend(ws, { type: 'system', channel: ws.meta.channel, text: 'Du er dempet av administrator og kan ikke sende meldinger.' });
        return;
      }

      const channel = typeof msg.channel === 'string' && msg.channel.startsWith('#') ? msg.channel.slice(0, 32) : '#generelt';
      if (!canAccessChannel(ws.meta, channel)) {
        safeSend(ws, { type: 'system', channel: '#generelt', text: 'Kun klarerte brukere (★) har tilgang til #hemmelig.' });
        return;
      }

      const text = typeof msg.text === 'string' ? msg.text.trim().slice(0, 1000) : '';
      if (!text) return;

      const user = String(msg.user || ws.meta.user || 'Ukjent').trim().slice(0, 28) || 'Ukjent';
      const color = /^#[0-9A-Fa-f]{6}$/.test(msg.color) ? msg.color : ws.meta.color;
      ws.meta.user = user;
      ws.meta.color = color;
      ws.meta.channel = channel;

      const seq = nextSeq++;
      const rec = {
        seq,
        msgId: `${Date.now()}-${seq}`,
        type: 'chat',
        channel,
        user,
        color,
        role: ws.meta.role,
        deviceId: ws.meta.deviceId,
        fingerprint: ws.meta.fingerprint,
        ip: ws.meta.ip,
        host: ws.meta.host,
        text,
        time: formatShortTime(),
        isoTime: formatIsoNow(),
        unixMs: Date.now()
      };

      const arr = channelHistory.get(channel) || [];
      arr.push(rec);
      if (arr.length > MAX_CHANNEL_HISTORY) arr.shift();
      channelHistory.set(channel, arr);

      appendVaultRecord(rec);
      broadcastChatOrSystem(rec);
      broadcastAdminState();
    }
  });

  ws.on('close', () => {
    if (ws.meta && ws.meta.status === 'approved') {
      if (ws.meta.deviceId && state.knownDevices[ws.meta.deviceId]) {
        state.knownDevices[ws.meta.deviceId].lastSeenIso = formatIsoNow();
      }
      recordAndBroadcastSystem(ws.meta.channel || '#generelt', `${ws.meta.user} logget av`, ws.meta);
    }
    broadcastAdminState();
  });
});

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

  if (action === 'approve_user') {
    if (targetDev) {
      const known = state.knownDevices[targetDev] || {};
      state.verifiedDevices[targetDev] = {
        deviceId: targetDev,
        fingerprint: known.fingerprint || targetDev.slice(0, 8),
        user: known.user || 'Gjest',
        addedAt: formatIsoNow()
      };
      delete state.bannedDevices[targetDev];
    }
    for (const sock of findTargetSockets()) {
      if (sock.meta.role === 'admin') continue;
      const newRole = state.trustedDevices[sock.meta.deviceId] ? 'trusted' : 'verified';
      admitClientSession(sock, newRole, `${sock.meta.user} ble godkjent av administrator`);
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
        state.trustedDevices[targetDev] = {
          deviceId: targetDev,
          fingerprint: known.fingerprint || targetDev.slice(0, 8),
          user: known.user || 'Bruker',
          note: String(cmd.note || 'Klarert av Admin').slice(0, 60),
          addedAt: formatIsoNow()
        };
        delete state.bannedDevices[targetDev];
      } else {
        delete state.trustedDevices[targetDev];
        state.verifiedDevices[targetDev] = {
          deviceId: targetDev,
          fingerprint: known.fingerprint || targetDev.slice(0, 8),
          user: known.user || 'Bruker',
          addedAt: formatIsoNow()
        };
      }
    }
    for (const sock of findTargetSockets()) {
      if (sock.meta.role === 'admin') continue;
      if (sock.meta.status !== 'approved' && makeTrusted) {
        admitClientSession(sock, 'trusted', `★ ${sock.meta.user} ble klarert og koblet inn av administrator`);
      } else {
        sock.meta.role = makeTrusted ? 'trusted' : 'verified';
        pushConfigToClient(sock);
        if (makeTrusted) replayHistoryToClient(sock);
        safeSend(sock, {
          type: 'system',
          channel: sock.meta.channel || '#generelt',
          text: makeTrusted
            ? '★ Administrator oppgraderte enheten din til Klarert bruker!'
            : 'Klarert-status (★) ble fjernet av administrator (du er nå vanlig gjest).'
        });
      }
    }
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'disconnect_user') {
    const reason = String(cmd.reason || 'Frakoblet av administrator.').slice(0, 200);
    for (const sock of findTargetSockets()) {
      if (sock === adminWs) continue;
      safeSend(sock, { type: 'admin_notice', action: 'disconnect', text: reason });
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
        state.bannedDevices[targetDev] = {
          deviceId: targetDev,
          fingerprint: known.fingerprint || targetDev.slice(0, 8),
          user: known.user || 'Ukjent',
          ip: known.ip || '',
          reason: String(cmd.reason || 'Blokkert av administrator').slice(0, 120),
          addedAt: formatIsoNow()
        };
        delete state.trustedDevices[targetDev];
        delete state.verifiedDevices[targetDev];
        if (cmd.banIp && known.ip) state.bannedIps[known.ip] = 'Blokkert av Admin';
      } else {
        const old = state.bannedDevices[targetDev];
        if (old && old.ip) delete state.bannedIps[old.ip];
        delete state.bannedDevices[targetDev];
      }
    }
    if (makeBanned) {
      for (const sock of findTargetSockets()) {
        if (sock === adminWs) continue;
        safeSend(sock, { type: 'auth_status', status: 'banned', text: 'Enheten din ble blokkert av administrator.' });
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
      for (const sock of findTargetSockets()) {
        pushConfigToClient(sock);
        safeSend(sock, {
          type: 'system',
          channel: sock.meta.channel || '#generelt',
          text: cmd.muted ? 'Du ble dempet av administrator.' : 'Demping opphevet av administrator.'
        });
      }
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
    if (typeof cmd.heartbeatSec === 'number' && cmd.heartbeatSec >= 5 && cmd.heartbeatSec <= 600) {
      state.settings.heartbeatSec = Math.round(cmd.heartbeatSec);
    }
    if (['approval', 'invite', 'trusted_only', 'open'].includes(cmd.accessMode)) {
      state.settings.accessMode = cmd.accessMode;
    }
    if (typeof cmd.secretTrustedOnly === 'boolean') {
      state.settings.secretTrustedOnly = cmd.secretTrustedOnly;
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
      label: String(cmd.label || (cmd.autoTrust ? 'Auto-Klarert ★' : 'Gjest ✓')).slice(0, 40),
      autoTrust: !!cmd.autoTrust,
      usesLeft: typeof cmd.maxUses === 'number' && cmd.maxUses > 0 ? Math.min(999, Math.round(cmd.maxUses)) : 1,
      createdAt: formatIsoNow()
    };
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'revoke_invite') {
    const code = String(cmd.code || '').toUpperCase();
    delete state.invites[code];
    saveState();
    broadcastAdminState();
    return;
  }

  if (action === 'force_channel') {
    const ch = String(cmd.channel || '#generelt').slice(0, 32);
    for (const sock of findTargetSockets()) {
      sock.meta.channel = ch;
      safeSend(sock, { type: 'admin_notice', action: 'force_channel', channel: ch, text: `Administrator flyttet deg til ${ch}` });
    }
    broadcastAdminState();
    return;
  }

  if (action === 'probe_ping') {
    const targets = (targetConn || targetDev) ? findTargetSockets() : Array.from(wss.clients);
    for (const sock of targets) {
      if (sock.meta && sock.meta.status === 'approved') {
        safeSend(sock, { type: 'admin_notice', action: 'probe_ping' });
      }
    }
    return;
  }

  if (action === 'broadcast_alert') {
    const text = String(cmd.text || '').trim().slice(0, 500);
    if (!text) return;
    const ch = String(cmd.channel || '*');
    const channels = ch === '*' ? ['#generelt', '#lekser', '#gaming', '#hemmelig'] : [ch];
    for (const cName of channels) {
      recordAndBroadcastSystem(cName, `[ADMIN] ${text}`, adminWs.meta);
    }
    return;
  }

  if (action === 'clear_history') {
    const ch = String(cmd.channel || '*');
    if (ch === '*') channelHistory.clear();
    else channelHistory.delete(ch);
    for (const c of wss.clients) {
      if (c.meta && c.meta.status === 'approved') {
        safeSend(c, { type: 'admin_notice', action: 'clear_chat', channel: ch });
      }
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

server.listen(PORT, () => console.log(`Chat Smart Relay v2 lytter på port ${PORT}`));
