const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const readline = require('readline');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = process.env.PORT || 3000;
const SERVER_VERSION = '2.2.0';
const SERVER_BOOT_ID = crypto.randomBytes(6).toString('hex');
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
let WEB_CLIENT_HTML = Buffer.from('<!doctype html><html><body><h1>Chat v2.2</h1></body></html>', 'utf8');
try {
  if (WEB_CLIENT_HTML_GZIP_B64 && !WEB_CLIENT_HTML_GZIP_B64.startsWith('__EMBEDDED')) {
    WEB_CLIENT_HTML = zlib.gunzipSync(Buffer.from(WEB_CLIENT_HTML_GZIP_B64, 'base64'));
  }
} catch { }

// Server-delivered Admin UI bundle (sent ONLY over WebSocket after RSA-2048 adminSig verification!)
const ADMIN_BUNDLE_GZIP_B64 = 'H4sIAAG1BmsC/8U823IbR3a/0qIdzSAGIFwIigQl2RQtW4ope8uk90VSkQNMAxhhLsjMgJeVWbVbtclTki1vNpXKZqucpMqVl7zkab2Vt9Wf7A/En5BzTnfPdM8FBGh7U7YkTE/36dOnz71Pz5utcZJsDdnWy5CxtuMGreicx75zxd5gC2OulyzgccjCKOT7om0RJV7qReGQTbxL7spWL0x4OmQd+ThyxvNpHC1Dd8ji6cixO00m/28Peg3Z62ctL3T55ZB1u2rg62WSepOr1jgKUx4CxInPL1s8FPNcFxFtJ7Pogr3JEcXu+1o/N3YueKzWc+G56WzIAi+07+90FpdNtrdzfqHQmXFvOoMpu53OX1Ss453uqDvuZSuMYpfHLZ9PcMTikiWR77nsnX6n3+s7+wX6EVqijRbkejEfCyqOI38ZhBnUy1Yyc9zoYsha3R6A7bD+DvwjiUj/tXcGjQI5Ztxx1SIXjut64RSw2oaB3d3FZeVitruD7q65mFGUplFgLKc36rn97RXLcXxvGra8lAcJrAW2jMd1W5ksnDFvjXh6wbla8NRZIMEXBnUuYmzFvwvLTL3U57DdEwDZSryfcRh7H8aKhgu5f7udzj6SNYphnZPepD8Z7Bc5pAptgQzSS5ty5LjT4pRd7JKRuQ/UokGSirHjekuAure3R6061YE1BgNHw24yKSB/H5HXVuyMkpI0auQnlHcy8uV738G9367e+16n1+vd32zvUeAmfnTRAnF1lmlU3BlnpNAUAA2dUaDMbhnfXUS3n7OBRu1Cq06oqrXpSEsynzux3Wql/DJtBcuUu0rgx8s4wfeLyNP49mIGbNEiZsVFVLGhM2o7IL7nyBj67GIiZ4wM1SjsssZSkXuFHOWT6tvPSXslSattI25tkXdrNIiUpW2Tf8dO7BawBC7sDXqj/WynTPXV749LvIyqaN/ULKVJZtsFMdluD7BbURIDJ556Yc5wnYolVornDQpFw2cae65uFfB5n/4GLgigDTZYUA3Ax3zBndRGyrcmXtpE8xA4l3Z3lyxEdxI3GvuaotLmmXjcd5nvjLivTzfyo/F836BFr6Sl7mtaqsygRSptV03shYsl4Ku1JNwHrjCaEKoTc6dgA2uNnANmblIrP6MYsW/sm6KuM9Cgv7vd20zuO9VyT+wjtc8y9b2QG0qF+k6cwPOB5F4447GXFgS1SAHc2pYy8zuktGMupgMZTL2x4+tUjtG3+LOZvvptqCAzKLlOf7eazHt15qCXvShw1+6a9hcIAi7bJJKUVKy0S2KR6TOzv2Gzq5g/UwyG7jD5HQEly1FBwfQ09VIvQmkEi+mV4Y3SMCm7jrQrA7UenRS6votC2Afe8qNpZvWM3et0u93tFbunG6mbhaQoIIrpl14riMKImKvJjj96Dg+tz/l06Ttxkx0Skk4CCk11qpCyniZlakP2Rnx3NMhY5TITmV4nx6RktSqs5yLmrYyNarmuTNdJFAc1W1Nwz4wRpA/Vhih2vGl7Clz4Qym2PVPgfvB966/QjTl5ICxbgEEAkl9WM+qgu9N1VjDqBKKZ0UZqpoptdm5km+qlbRw/Ge5wmQxBAvKao7uTee4GTSa9LnjHxeXeNxkvdaY6h3oh7kGrwvJ3qy1/hgQGefcrwgfy/KTEiChzUEK13+1v93muSd2Bu8d7BTTbEeFWcAIpoOwPmt2dQXMPg8peT/NYd0a8t7dXBESKtQpOb7vT7N7fbQ5KgCYTt7/Di4BGThjWQOoClEFzhwANDEC7413hRm812dYsDXyRuXjgeufMcx++3ALon4m0wMstNgYJSkSjSha83HqEWNAA/bXIEci3Fe8xuM7eVrwnC6d1YOy7r//13//321+xAxfN5Bw2P458P3//AKQ6NGBQmAkwfgpezMRLwBlh9vH89dJPGw/uYe98+nswv4lMkl75HAApbiRp0b0T6ZygdAgR1ZF9IPxXBSTnXWkbxA68s7e9N3K299eZA1lXxlZZaKXPCHMKVa227XA2f0ZMChuXXi0QjfGMj+egtmAg+9xJ5pzNQ2ex4DHz2HjmpBr+92gB+opGS7AwYQb+cRoe+lHCNbYA48+SAIATkZl94KfvfQakFiMriW381pnuBGL0Asel1JSDkQgVujARRMJY10kdbIF3S9h8HPvd1199wx7HyzmPeRmvaoAmJCATiJmPwP70q/9GfjyMIt+NLkJ21wnAofnECR2fx7eELiwvYfqP/8E+WYbh9PXbb2NQago89fBvBz7haQqgCPnf/gsi/ywMwav2gU2mt8X53AGBEhj/jh1h/H4UTacFWLX7/Bji9sI+j6jpUT5E/VL/oq56LXOsSLGUvcseMttzG+zhI+ZG42UActOe8vSJz/Hn46tnLr7eV/15MoYR4/SyDb+cBX8Kmi976RynEMvCezLu0YJjWtbxE97EZ2GUTmDTE70ZaDFkFvGZRQ0JSFYyi8DEhEvfpyaiFBAHBr54RS1yv596SRrFYPFeWJl2w11mc3Be2ux4HgPFXm7NuL8AWoFbxuZREDihG4Ho2qM4ctyxk0CIOpa82IQQzIfWlgNTA3E5+kAJLGuZNNrWK7kQst/cPUFVC8hbZvPzRCD6MrwG0ijiqGT2Q/aubeXGwcppS5kY9Rq3V3s3Vjop65BpKer1MpwsQ/JBIOoO3cPAtRfOFa6kIXYDtwzf/FUShfZno9eAaRs4BzSm/Ya0HKzDQRKejgPXYtdNpsYj+GtjhsCZc9BiNmk6pBJ4h5NQTSTWAnhm/DSGcDflkqVsS/C3JcL2UZs4+FMnwKVZQhMyi73HbIDLvvwSyKt6Yjx1KIJY6EuzyzdROPa98RxaJ8L5inm6jEM2KuGegoj53AZWGPOfOr5EWnBuG1kWYCA5oglTfdjDh4gZcAh3Qou9n78YsjvaSJpYHQXQqo6APdtyRgsPB6ymPpVYlzdhtt6oXGO1j29IMaNzacX8r5c8SU+RITlsksp8xNCVx7bMwzPQslxBwX2P+STmyewQDNUXnp1l64kwktukTbIaGilt0gqKYCiwOFQtEDzGJ+ewE7hGHsLsFo2DFdqcBr6hlfF2Cl4jT4mIcmyjAFQsJGNxRAGMxZRnOOh7pKkR1ETZIDLR8gSoetEojRlPAiHjq2NKUEXxge/blkqmAg1gg58445ltAzvmCMBDiTqSyhI3tKIPqR+qeTAa2KKihw1nJvCjCj4SZhroPCKaIorVfIBLLugG1UEXVdS3gLVcgtK+QrBACQHBYXefnjw/Qvm0Mpa9gz0zZhWgLhwvXSH4YIQshSp2NUVfpW4tvYcp8tYRKGvQ3KSoWkhjNokdkJQYGKvdbltZbAh4o38GEjTzfNdGWGrmjeQKtYiSl4Kw0majZhC2q0AKSkKvRwrsupoUEqTvwVjkehtp31bPoCNfvGq0E2BMbsO/UZzatgP8QSz06TIYwZaPZODVYC3V5KgmAxF9u88ezLYN10/6Uk/CGcd9sN99I5FoTzwfWuwxTjlWgNs+D6fp7Jot3n7jA/uCGrjH8jHqbRqlDoUWMNtZFoIDeLluBspYjsmorIiCWdH1yMywb5nO0GjtmzApqbguUOxcCZVyk5bZzyCuFiIUg7gsVVmIVN59A26XPW4jy5Ft/GL+GnCyGtdmr3EbFKjrczBWZyK8UwGVGT/pmYAdPMLaevSBmkNAaFzLiO+MoadTmkeG8+8zqxxGYlYikpHUo58oFpDwLIRXOQY6fxQ782jk551L84rov3Zaeg2APuTBwpyyDErG/7WwxHsA9kXK0dZNV8CrW9C5oqrgYwisE9THuIW9ds/KqKwHknpkXcMjyXKEpD1sPftwyN4Rc8AkLj8HXfDMle6TVA2d5najcY1CK1CZUOyygBgplR2vG+yPvxeB2DDjNRm4UZcWYaojdlaQHcpjrys72LladvCNJjugdcdt4YYLnYuqHdC3NH0gwelqXzmq1seRi4ISgtW0pjHn+EMY8AprABBi8FROUcignyLmkOWExYAhDEWb+AVGo5Ev7NrEPAbXkd15+FC62GtirTH5Z4vFjJ8DKsGCmA7ZGlDTeohV4bsLJ165PBxyKhZSuzoCC96tmsBYnFqVMij1ZP8EzDVbpkj1VRi5XoJEBIfo+9B8JSVzGZekHDmCWkqmiZp5r5ycLnqi8Sr0YdRN9BSAiaByjkqKSpWrc8cqrv4U4mNKQrAPQuc8NMhsgJDwo3DixYF9lo3jEIejzJJxRxDsg9x2XJMNxmfclOv3zxqNat8J/NxTMaRm/blDJaXDWPp1SWjQTosF22g1m0SCfAi5KTpBoL96e13jAOKYhu7IUYxU5c2pPFXJoXMPN3DpqPNaTp2L6lL4czIHQR7dGzb1oxHq4U6TKZyG7M01+fXaHJUuBfptMst27EcXQeRy8LyyhJtNyRIGZoFymI7vp56b5UDuCE+sNsOMlQsvtzKPwjxHq8joFsfTOXgxBSuypmR6IGgE1ozZx0QA4kLAkDfKqVW0txRI5blb94TCzQJ46BgtKAI6d/wlYi2oS9m3v/t7NZWN87C5SEQ22J9+/hsWvv0GTSFsU1sMwc3pXCcP7gmAN0zzzhRjY8dvdWGq/EEHbSNstcPs7l2mP7+w8kHWq8YtJ+/pk/duM3nvxskBluDiZQJ8cKhAyuAkcBb2eIaK6ayIpfQzZu0QBAUcWdyS3/yaFZqNzZhlsnLMx0W0zhrt15EH6rHgFYOHRbyyiY+1glWP+XyJwTSzOxg9nzcxLZawfqdTzaiFMwYXMM/PF0KKyOAZxBIeO/jLuYRfAA5+56Qq8qEpaeZhzJpHM+qMJK8wEIfkWxVnGMUDC5HOHrsC50cH50CNpHxwsRaAPgDoJ7cbO4Cxg1uO7SLm3c4tR/dxdP+2o3dw9M7K0TnHHCwW/lXp1IiRqwJgMERHTpmmDLT5ysOjs7o8ibApBStWTli9kCt4Vc5YZX7HqC5Xltu+NE9mS7UN8IjX94td0UhmmQyVXBu7uh+hIIFgKTAw6DjFMyA70XtWeDHowyidYmUGd8jSJvQGFFywvYnpx1BGfRZdnETgQ9lnmXEVXlN6zRInxa3w4Sm5Ts606EA5K6pJoU47XJGDLeQ81qBbiWoV1BEKPRvyQ1DltjQRByWaVzTbxNmare1sSduUu1wVxsqEWpEOA+N0gH4CRM7neN4l/QWyUOKUXCYoYWxyFVKWTE2scl5msovyqcU+eqqriMt7sMQHi6pT8n5+Rr7b2d3e5ajIn0EIE5bwjSDO5WnKUwaR8dtv2g/uLR4pepmHCGY6bkb5OIVtoyzXm+Tk1snKKbgBD04ukfnRLYAH4GvDwQhQVgKRHHuP2UGeBLPsD/BIKWt5j1kNkb1pKG8BgqciVubeV+VfMDzBE9dV+btKb6YuT0TOTZBMD6NlCOIS+K5MDAn1vSIJ9MTDaqlsHpA6Hn8qJvvj79lzDssOgryLoKXK5oi/z0oU3yibs34+Z1VQ+93XX/0C45YjnrCEpAm3BngX4oyrPLzNj4P0w1jcKBFDECGR2Ndn+1WqTY47lTpN125yIOq1Qqi6Cut//kpEWyBRiHAhbfDGjMCpm9IgQiA1jOtCbRdscMo3QzmPpQXGZiidqZaacDoLqGvj6plyGHQ9C4ZmffUtOq+jvt0gU9xu8HkUBabGloAqNPav/4sdzOmGxIfPW4kTpKT/QC8DxBUaOX+rKbnSLLfSxToeHnr94aZqOEYtDBj+WfTvD6cNhfaJiV0PMKz7298wve3xSuUY30434kCh+Q/QGJAtEFPK1obI5EtsVPPjys6PZec6zVmUuErN9uHzDbXah8+HhBnRLUeUSHaDinMDmGDOr4YsbsM/FUpC8vRtlYAYnisBLa1mLqR0ejeKLjfQFEz1X60s8m5VZ5m/UNVbV6GyhdW4XhsKQcN4E2zLmGpF0OYBx50iGlhHVNY/AmzhXFwolYD7Lp3psBn8Edokn6OoSwxtEqA2qUKgkIyWingD9QLcVU8EkGar0NfcsySNo3BaOL2UHkybnuhcCi+1WZQ7Uu/KJ6SgLAjYI9j14KbzUaGv8+PQoOY4lK0Yva+Zgu4Ca0dfKGCpB7SQZ26vJMTMM6PNVW/PDPLg1huStzqRruTAcACiS51DC6IsRxjp9Bsz5qIWr5gwB9dEWWv4CTp7TByyX+izgfzL3qulX3WqzYtTgahM+M7LdaKfgmeWeC5vQXjkAib46nvkw3fXTYdn4+lioLhHMOyye6zV3a/OQD4X4s6SKGDnXoL+Mvyi8yXQAFHCDo6OnqyRizwIwxPguDwbmYqnhe+M+QwieB6jX9Pm86TNPr1iGmEYzLRM+R0jR0kqFTb/fdwLwcwUaa1KVm6Ye009f53TAFjZET/n/o2nAcJzwRz2HcQcZA9R93Gs4HGq5WigPyCm4K48/H/0p1/+QViUScTsx/7bbxprZueXREUxK056925xUtGjetrvvv7tz9ln2k7YH8dvvw3DdWfHU+JVc9MpcvWCf/tv4jbBuRPDO2Z//vZbt3raG1Pum+Sod9fMUavNPwalBgxQSJiqbClpAewC/EsJKTz6WScNiyXBZbAi3MPy8N/9E/voNcfaUxLENUB+ThXHB75fgCm9Q5FC+CXD2jcGWo2FUkOFWFbFwqs01aT9NllfqTLNbKQkX1U2si5VqKt5cDlR8ocSmtQxKvXYTmFtdqPJiOO0TiSuWfoWPVUzpWgZlf2IR3rHQn/WzKTKTfreyFtWFQ6PhYqd4DbzqvmzHa1EQM8EWI85cR6yIFU8uVwex3PmY7Gj2PErLFLAW8HJa2Ac8OvetxqN6rWI+vVTAFqJO24rgNJ0OBWBgy1UQiDWU07JRpuYatn7xqj+JlP96/9hRmF/2RJnghmFR9G0cCNCuxprXIyoNDj67U1TsxTO7qLwGTbcYDDx0gH7Ul4egB/ZbQP2lHt3oEFl1pl2LjyA9vwGAnZCVm4JXbJS3QFWny/rtN0nKDG3PBKKDOWQMQMQOz+GoEd98+GxEKNIr9G8uCFzry9fhsXByRgvqZ1EWJpsND2lakUDm3gZwjx1pyXjwNURpa0r6CEzDoMBDb30VyvwLmC/WCYz23pE1xVwVNa9era8gLrmvEWCpysYWO5EV1WGtAL9kOX7kHdDAhf0KvGYodQE7Yu91LKjcM6viMcfFq8FYCaCPI0neCUPXA0Byc6U6U1hh7qTVYw7shyh6kDlNNcGx8CrDZSZ7L1amalO9fU44uLYMRWr09mQdn/s5vjilq7yiedPwTdJgshdJmv5zOMxT5Lnkctv9Jrxugr5kEnbyUaJzcFXVpX3+PZv8I6NLLSJ8EQCLdy6XqsozcS6ncpZ1evKmT+JwbdQdwemsiCUgru1pvbCc0+66+WJxcvqaZego/G1g7Y7mcOYNWdM4yVYffc0CunYv2pevUvl7EdvvwF2tyHOpStxPE75LV31zdjuKVitdAQSxexEFsqsUxbzdLSqLGaQlcXsFMpikvZMTSgrgvo/WG0Mxh3axzvoMwobxSHOOT/GirRKy3zkwC/mrbxNWheFlCKGLAr57uv//AM7efttQFGBOvFdA/BHEZYTfMILdSYiBvmKLqhiwOScCzmiCAQikZCznxy2eHg7F0OqzkL8Ici2qhqixpMX14FOM/vQZLnYZKFG1qKMc5NlLPQkdNATHzIQL70dWGto1lMQvxr1FP1OfT2EZVwaBv8etp7Ch0pbK7f45hAC9xls0oxsvjefM8/Y9fpQgXzLUzHuSj9OtP6yMnY40KojWQqzplqskGOe8dDNqFOkzCUlpGoO3347n3OfbnYJ1sKA1+ewrTykxSBaE5qEYgOYSXkNuo0HpbuBjZe9V9t41WlFwPIPX4tskKHwKwz8OupGL6ndROPA7MepW64UyxMK72EeDyKT0IXlIIbM7lLc2VhDRwD4E7Q79aVoBF7aGybAD2rAVykI7VwCKI4nE6K0VFhZVfLxI18F+6GPPAF58M5dnpVcrDquVAPIYIoKjmfT15xOrLB9mfDkiE/SmkPI2iPIuvKEyjzCeTTnp9KzwWgEtadahXl/QcnFhkX5cpip9wXzVqiOKgVGW5zjiJ/wIdZUHxhAd+ELoNWQdYvVdoqLv/dMwkhkEw3URDfFL/RRgx/32mjNGaj+uQkQLbzADXwl8cu+tZBdz5zhpWFYRWyWSGx6HrruaSj2I+3YBpqKYBR7b+N33cx6EB+wzEPfHHFx3a3V7XUabXL6E57F+BTh+1HVyWrtuWpGACYvsZpHqzcVaeBsFVUamxyirn+EWjpAXXW4+UJVXlSdR64owxCDtIuBAAE89uxwlMlz26xrdhqrn8PmhRZ4DMtW3FPNz2HjmnPYYVZEUnd4uuLo1CxvGK84MV19r4gkXn55grZbXNkXHyxxQvQ2Y9jloVQz+kcn8MSp9H2DpviSBQZPEE/h31E0R85KHegSN9m5xy9OgPBN/HgsdExlJWv+PZOc8fQSA5ry7l12pzxnIfOFo9Qsxv0oq2R+8SyonqNFdKkxNTRUffrDMjoIPZB/lwv74Qdjt3u7lR3po2XYSf9U3rg/2d4zu6eyrMaCCAMwz69IZdXOhbIPoO+hm1dT2xl9zcszpdYX5sbISzQ5FTRdkaCueNFpsl6TDZqsi7/gTx/+7HReVSiQVXfURYRv6JBoZU18VFB94p5tB3MKhc81DdnBOaYXzkrtoqa7cKtRACL6NWAWlaDAz6zERqE/7osuWlHFdVrsU/11kI1r2IsSkxW0yy3GqWRYt0HZvwnVrHdXACvvAtCmCrkuxMZ+XlilleUe+vG6n9iRlaswovJbO9IVLHYtWMIso1DquDrEO5PRKSX88gIlr0yruqrX2ijVHC/K2m6gpkDZrG4hLRuFz3mSOFNugz01dCY8k3GTGUb6RJL4TogmkoWPpwAtYJhxqmB84cf4Tkv+oRFdIq5XY0DOzmlyFY4tVDwHcexctb2E/qUBMbBz7CaNMpKZnySwVD2V14QX2OowpzqBGjf2+68J/CRaTI7UCuTF2YvWtQrnoi/LHrH+oNOo8Bhn3iS1/5/WLRn6FN4lFtqHqk5uIN6XSWKU68GelnkhEKydYDmH/syGefH0j8Kl6jwrWqYViFcdphEU5cHZaRSAXTx34oZVuTcFCNkmo+dfM8stdjqvb1ufIvIFRaGZewg/tq7/DzDcHc7nZAAA';
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

          // Deliver privileged Admin Panel UI ONLY to cryptographically verified Admin!
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
