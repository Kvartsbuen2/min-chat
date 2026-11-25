# Chat Smart Relay (`min-chat`) — v3.1.0

Live nettside: **https://min-chat-qtl0.onrender.com**

---

## ⚠️ VIKTIGE REGLER FOR FREMTIDIGE OPPDATERINGER (LES FØRST!)

> **TIL FREMTIDIGE OPPDATERINGER / AI-AGENTER:**
> Brukeren har eksplisitt bedt om at **INGENTING skal slettes ved fremtidige oppdateringer** etter v3.1.0!

1. **ALDRI øk `STATE_EPOCH`!**
   - Behold `const STATE_EPOCH = 3;` i `server.js` på alle fremtidige versjoner (`v3.2+`, `v3.3+`, osv.).
   - Å øke `STATE_EPOCH` vil slette `chat_relay_state.json` og `chat_relay_vault.jsonl`. Det var **kun** ment for den ene rene overgangen fra v2 → v3!
2. **Kun bakoverkompatible datamigreringer (null datatap):**
   - Alle nye felter på kontoer (`state.accounts`), innstillinger (`state.settings`), kanaler (`state.customChannels`) eller meldinger **må ha trygge standardverdier** når gammel data lastes inn.
   - Behold alltid eksisterende:
     - `state.accounts` (konto-ID, `@handle`, `passwordSalt`/`passwordHash`, `displayName`, `color`, `firstJoinedMs`, `gifFavorites`)
     - `state.sessions` (aktive innlogginger slik at folk forblir pålogget!)
     - `state.handles` & `state.handleOwners`
     - `state.friends`, `state.friendRequests`, `state.customChannels`
     - `state.bannedDevices`, `state.mutedDevices`, `state.cooldowns`, `state.settings`
     - `channelHistory`, `dmHistory` og `chat_relay_vault.jsonl`
3. **Null datatap på Render Gratis-plan (`plan: free`):**
   - Render gratis-plan nullstiller lokal disk ved hver deploy/restart.
   - Derfor har admin-panelet **automatisk nettleser-backup hvert 60. sekund** (`chat_server_autobackup_v3` med `epoch === 3`) og en **1-klikk «🔄 Gjenopprett all data nå»**-knapp straks serveren starter opp igjen!
   - **IKKE endre `AUTOBACKUP_KEY` (`chat_server_autobackup_v3`) eller `backup.epoch === 3`** i fremtidige versjoner, slik at auto-backup alltid fungerer på tvers av oppdateringer.
   - Hvis Render senere oppgraderes med en Persistent Disk, sett miljøvariabelen `DATA_DIR=/var/data` (støttes allerede i `server.js`!).
   - Tips: Sett gjerne miljøvariabelen `ADMIN_PASSWORD` i Render → Environment hvis `@kvartsbuen` skal forhåndsopprettes automatisk ved helt tom server.
4. **Sikkerhetsregler (ALDRI bryt disse!):**
   - **ALDRI** legg private nøkler (`admin_private.txt`, `admin_passordfil.txt`, `*.key`) inn i dette repoet! `server.js` skal **kun** inneholde den offentlige RSA-2048-nøkkelen (`DEFAULT_ADMIN_PUBKEY_XML`).
   - **ALDRI** lekk admin-UI, admin-kommandoer eller admin-brukernavnet inn i den offentlige HTML-en (`WEB_CLIENT_HTML_GZIP_B64`).
   - Admin-panelet skal **kun** leveres over WebSocket (`admin_ui_bundle`) etter at:
     1. brukeren er logget inn som `@kvartsbuen`, **OG**
     2. brukeren har låst opp med **`Alt + U`** (eller 5 trykk på versjonsmerket på mobil) + kryptografisk RSA-2048 signatur fra sin private passordfil (`admin_passordfil.txt`).
   - Behold eksisterende `DEFAULT_ADMIN_PUBKEY_XML` i `server.js` slik at brukerens passordfil alltid fortsetter å virke.

---

## ✨ Funksjoner i v3.1.0

- **Kontoer med fast `@brukernavn`, permanent konto-ID (`#XXXX`) og `scrypt`-kryptert passord**
  - Kompatibel med **Chrome passordlagring** (`/api/auth/login`, `/api/auth/register`, `autocomplete`, `PasswordCredential`).
  - **Forblir innlogget automatisk** (1-års `HttpOnly`-cookie + lagret økt-token) helt til brukeren trykker **Logg ut**.
  - Visningsnavn kan endres når som helst, men ingen kan utgi seg for en annens faste `@brukernavn`.
- **Tenor GIF-velger med søkebar og konto-synkroniserte favoritter**
  - Server-side proxy `/api/gifs?q=...` (fungerer rett ut av boksen uten API-nøkkel, pluss valgfri `KLIPY_API_KEY`).
  - Favoritter (`⭐`) fungerer både i GIF-velgeren og rett på GIF-er i chatten.
- **80 reaksjons-emojier**, meldings-svar med hopp til original, live skriveindikator nederst, rediger/slett egne meldinger, opptil 5 private kanaler per bruker, venner & DM, og live 2 MB bilde-/filoverføring (lagres aldri på server).
- **Personvern og ren chat:**
  - Nye brukere (og nyinviterte i private kanaler) ser kun meldinger sendt *etter* at de ble med.
  - Ingen «logget på» / «logget av»-spam i chatten.
- **Skjult Admin-panel (`Alt + U` + privat RSA-2048 passordfil):**
  - Brukeradministrasjon (endre fast `@brukernavn`, sett nytt passord, demp, kast ut, utesteng, slett bruker).
  - Slowmode/cooldown globalt eller per kanal (admin slipper alltid cooldown).
  - Skjult innsyn i private kanaler & DM-er, global kunngjøringsbanner, tvungen nettside-oppdatering, admin-konsoll, live logg, og **`💣 Slett ALT i alle chatter & DM-er`**-knapp.
  - **`🔒 Lås`**-knapp som låser admin-panelet igjen når du er ferdig.

---

## 🛠️ Drift på Render

- **Build command:** `npm install`
- **Start command:** `npm start` (`node server.js`)
- **Node:** `>= 18.0.0`
- **Valgfrie miljøvariabler:**
  - `DATA_DIR` — mappe for persistent lagring av `chat_relay_state.json` og `chat_relay_vault.jsonl`
  - `ADMIN_PASSWORD` — forhåndsoppretter `@kvartsbuen` med dette passordet hvis serveren starter tom
  - `KLIPY_API_KEY` — valgfri KLIPY API-nøkkel for GIF-søk (Tenor fungerer automatisk uten)
