/* ============================================================
   TRY TO MAKE NOISE — v6 / botanica
   Mikrofon-reaktiv typografi. p5.js 1.x + p5.sound
   ------------------------------------------------------------
   Væggen er stemt efter den menneskelige stemme. Grundtonen
   detekteres med autokorrelation, og rækkerne spænder fra 80 Hz
   nederst til 700 Hz øverst — nyn dybt, og de nederste rækker
   sætter frø; nyn lyst, og de øverste gør.

   STILHED    -> massiv, skarp vektortypografi. Helt ubevægelig.
   GRUNDTONE  -> rækken ved den tone slipper frø, kanterne først
   ANSLAG     -> vindstød ruller gennem rækken fra midten
   IKKE-TONAL -> klap og hvæs fordeles efter deres spektrum
   RÆKKENS
   PLACERING  -> både fysik og farve: dybe rækker er tunge og
                 jordfarvede, høje er lette og lysegrønne
   ============================================================ */

/* ---------- 1. KONFIGURATION ------------------------------- */

const CFG = {
  /* Palet */
  bg:   [255, 255, 255],         // næsten sort, en anelse grøn
  ink:  [105, 92, 80],     // varm knogle
  trail: 26,                 // lav = lange, bløde spor efter frøene

  /* Vækstgradienten: båndets placering bestemmer farven.
     Bas = jord og rod. Diskant = nyt skud.                    */
  hueLow:  [186, 118, 58],   // okker
  hueMid:  [146, 166, 96],   // mos
  hueHigh: [223, 234, 186],  // lys kalkgrøn

  /* Typografisk væg */
  message:  'TRY TO MAKE NOISE',
  gap:      0.90,            // mellemrum mellem gentagelser, i em
  leading:  2.05,            // linjeafstand — mere luft end før
  rowsTall: 7,               // gentagelser i højden = tonehøjdens opløsning

  /* Spiring */
  breakAt:      0.28,        // hvor meget lyd der skal til for fuld spredning
  breakRelease: 0.976,       // frøene bliver længe synlige mens de driver hjem
  bloomMin:     0.14,        // intet frø slipper under dette — dødzone
  edgeFirst:    0.55,        // kantpunkter spirer inden for de første 55%

  /* Frø */
  sampleFactor: 0.30,
  maxParticles: 5600,
  dotRest:      0.85,        // frøene skrumper knap nok — de er objekter,
  dotScatter:   0.60,        // ikke støv

  /* Ranker */
  tendrilWidth: 0.9,
  tendrilAlpha: 0.30,
  tendrilMin:   12,          // px afstand før en ranke tegnes
  curlMin:      0.14,        // hvor meget ranken buer
  curlMax:      0.34,

  /* Fysik — interpoleres af rækkens frekvensbånd */
  stiffLow:  0.010,          // meget løs fjeder: frøene driver hjem,
  stiffHigh: 0.032,          // de snapper ikke
  dampLow:   0.930,          // høj luftmodstand
  dampHigh:  0.900,

  gravity:     0.060,        // frø falder, mens de driver
  flutter:     0.090,        // svirp på tværs af faldet, som en ahornnød
  flutterRate: 0.090,

  /* Kræfter */
  chaos: 5.5,                // turbulens ved fuldt båndniveau
  lift:  3.2,                // bas synker mod rod, diskant stiger som pollen
  blast: 0.5,                // svag udadgående drift fra midten

  /* Støjfelt — båndet styrer skala og hastighed */
  noiseLow:  0.0009,         // bas     = store, langsomme luftstrømme
  noiseHigh: 0.0075,         // diskant = finere hvirvler
  speedLow:  0.0008,
  speedHigh: 0.0055,

  /* Vindstød på transienten */
  waveSpeed: 22,             // px pr. frame — fronten ruller udad
  waveWidth: 18,             // bredde i frames
  wavePush:  9,

  /* Analyse — stemt efter den menneskelige stemme */
  fftBins:   1024,           // 2048-punkts FFT
  fftSmooth: 0.25,
  voiceLow:   80,            // Hz — dybeste nynnede grundtone = nederste række
  voiceHigh: 700,            // Hz — lyseste = øverste række
  clarityMin: 0.55,          // hvor tonal lyden skal være for at tælle som tone
  pitchGlide: 0.25,          // hvor hurtigt blomstringen følger tonen
  voiceSpread: 1.10,         // hvor mange rækker én tone breder sig over
  noiseSpread: 0.50,         // hvor bredt ikke-tonal lyd fordeles

  /* Gate — i dBFS på signalets RMS */
  gateDb:     15,            // dB over den lærte rumtone før gaten åbner
  squelch:    0.10,          // hårdt knæ: alt under dette niveau er nul
  hysteresis: 0.55,          // gaten lukker først ved 55% af åbningsniveauet
  rangeDb:    20,            // dynamikområde over gaten -> 0..1
  onsetDb:     7,            // dB-spring pr. frame der tæller som anslag
  hardGate:  -48,            // absolut bund i dBFS uanset hvad rummet lærer
  floorStart: -65,
  floorFall:  0.2000,
  floorRise:  0.0022,

  attack:      0.50,
  releaseLow:  0.020,        // dybe rækker slipper meget langsomt
  releaseHigh: 0.110,

  onsetDecay: 0.955,
  onsetHold:  6,

  bleed: 0.05                // hvor meget det kraftigste bånd smitter af
};

const ALPHA_STEPS = 20;

/* ---------- 2. STATE --------------------------------------- */

let font = null, fontReady = false;
let mic = null, fft = null, micReady = false, micFailed = false;

let particles = [];
let bands = [];              // ét objekt pr. række = ét frekvensbånd
let rowRange = [];           // partikel-indeksinterval pr. bånd
let tileRows = [];           // gentagelsernes ankre, grupperet pr. bånd
let vignettes = [];

let glyphSize = 60;
let gridStep  = 4;

let waveBuf = null;          // tidsdomæne til autokorrelationen
let decBuf = null, preBuf = null, nsdf = null;

let rowPos    = 0;           // kontinuerlig rækkeposition for grundtonen
let ampFloor  = -65;         // den lærte rumtone i dBFS
let ampOpen   = false;
let prevDb    = -100;
let clarity   = 0, f0 = 0;

let energy = 0;              // 0..1  det kraftigste bånd lige nu

let smoothFps = 60;
let hintAlpha = 255;
let reducedMotion = false;
let resizeTimer = null;

/* ---------- 3. FRØ ----------------------------------------- */

class Seed {
  constructor(x, y, row, edge) {
    this.home = createVector(x, y);
    this.pos  = createVector(x, y);
    this.vel  = createVector(0, 0);
    this.row  = row;
    this.mass = random(0.6, 1.8);
    this.seed = random(1000);

    /* Spiretærskel. Kantpunkter slipper først, så bogstaverne
       frayer indefra og ud i stedet for at eksplodere samlet —
       en kant der opløses læses som noget der gror, ikke knuses. */
    const span = 1 - CFG.bloomMin;
    this.bloom = CFG.bloomMin + span * (edge
      ? random(0, CFG.edgeFirst)
      : random(CFG.edgeFirst * 0.6, 1));

    this.curl = random(CFG.curlMin, CFG.curlMax) * (random() < 0.5 ? -1 : 1);
    this.settled = true;
    this.alpha = 0;
    this.size  = 3;
  }

  reseat(x, y, row) {
    this.home.set(x, y);
    this.row = row;
    this.settled = false;
  }

  update(b, frame) {
    // Hvor meget af dette frø er sluppet? 0 = stadig en del af bogstavet.
    const rel = constrain((b.brk - this.bloom) / 0.22, 0, 1);
    this.alpha = rel;

    /* --- 3a. HVILE ----------------------------------------------
       Ikke spiret og parkeret: spring hele fysikken over. Rækker
       hvis frekvensbånd ikke rammes koster reelt ingenting.       */
    if (this.settled) {
      if (rel === 0 && b.onsetAmt < 0.01) return;
      this.settled = false;
    }

    /* --- 3b. FJEDER (Hookes lov): F = -k · x --------------------
       k er lavt her: frøet trækkes hjem, men driver derhen over
       et par sekunder i stedet for at snappe.                     */
    this.vel.x += (this.home.x - this.pos.x) * b.k / this.mass;
    this.vel.y += (this.home.y - this.pos.y) * b.k / this.mass;

    const dx = this.pos.x - width * 0.5;

    /* --- 3c. VINDSTØD FRA TRANSIENTEN ---------------------------
       Fronten ruller udad fra midten med waveSpeed px pr. frame.
       Et frø mærker den først når fronten når frem — derfor
       forsinkelsen |dx| / waveSpeed. sin-vinduet gør fronten blød. */
    if (b.onsetAmt > 0.01) {
      const age = (frame - b.onsetT) - abs(dx) / CFG.waveSpeed;
      if (age >= 0 && age < CFG.waveWidth) {
        const env = sin(PI * age / CFG.waveWidth);
        const imp = env * b.onsetAmt * CFG.wavePush / this.mass;
        this.vel.x += (dx >= 0 ? 1 : -1) * imp;
        this.vel.y -= imp * 0.45;
      }
    }

    if (rel > 0) {
      /* --- 3d. LUFTSTRØM: retning fra et 3D Perlin-felt ----------
         b.ns er feltets rumlige opløsning. I basrækkerne driver
         hele ord samlet som én langsom strøm; i diskantrækkerne
         hvirvler frøene hver for sig.                             */
      const n = noise(
        this.pos.x * b.ns,
        this.pos.y * b.ns,
        b.t + this.seed * 0.01
      );
      const angle = n * TWO_PI * 3;
      const force = rel * b.excite * CFG.chaos / this.mass;

      this.vel.x += cos(angle) * force;
      this.vel.y += sin(angle) * force;

      /* --- 3e. TYNGDE OG OPDRIFT ---------------------------------
         b.lift går fra +1 (bas) til −1 (diskant): basrækker synker
         mod rod, diskantrækker stiger som pollen. Ovenpå ligger en
         konstant, svag tyngdekraft, så frøene altid daler mens de
         driver — det er den der gør faldet troværdigt.            */
      this.vel.y += b.lift * b.excite * CFG.lift / this.mass;
      this.vel.y += CFG.gravity * rel / this.mass;

      /* --- 3f. SVIRP ---------------------------------------------
         Vandret udsving proportionalt med faldhastigheden. Præcis
         som en ahornnød der roterer i stedet for at falde lodret.  */
      this.vel.x += sin(frame * CFG.flutterRate + this.seed)
                  * abs(this.vel.y) * CFG.flutter;

      // Svag udadgående drift, så væggen åbner sig
      const dy = this.pos.y - height * 0.5;
      const d  = max(1, sqrt(dx * dx + dy * dy));
      this.vel.x += (dx / d) * b.excite * CFG.blast / this.mass;
      this.vel.y += (dy / d) * b.excite * CFG.blast / this.mass;
    }

    /* --- 3g. LUFTMODSTAND: v *= damping -------------------------
       Høj her. Frø har lav masse og stor overflade — de bremses
       hårdt af luften, og det er derfor de svæver frem for at
       flyve.                                                      */
    this.vel.mult(b.damp);
    this.pos.add(this.vel);

    /* --- 3h. RODFÆSTNING ----------------------------------------
       Fjederen når matematisk aldrig helt nul. Når restafvigelsen
       er under en tiendedel pixel, sættes frøet på plads for godt
       — ellers ville vektorlaget aldrig stå knivskarpt igen.      */
    if (rel === 0 && b.onsetAmt < 0.01 &&
        abs(this.home.x - this.pos.x) < 0.1 &&
        abs(this.home.y - this.pos.y) < 0.1 &&
        this.vel.magSq() < 0.002) {
      this.pos.set(this.home.x, this.home.y);
      this.vel.set(0, 0);
      this.settled = true;
    }

    const d = dist(this.pos.x, this.pos.y, this.home.x, this.home.y);
    const near = constrain(map(d, 0, 620, 1, 0), 0, 1);
    this.alpha = rel * (0.45 + near * 0.55);
    this.size  = gridStep * lerp(CFG.dotScatter, CFG.dotRest, near);
  }
}

/* ---------- 4. FONT ---------------------------------------- */

function preload() {
  // Playfair: høj kontrast, organiske former. De tynde hårstreger
  // bærer færrest frø og opløses derfor først af sig selv — stammerne
  // står længst. Formen bestemmer forfaldet.
  font = loadFont(
    'https://cdn.jsdelivr.net/npm/@fontsource/playfair-display/files/playfair-display-latin-700-normal.woff',
    () => { fontReady = true; },
    () => { fontReady = false; }        // systemfont + pixel-sampler overtager
  );
}

/* ---------- 5. SETUP / LOOP -------------------------------- */

function setup() {
  createCanvas(windowWidth, windowHeight);
  pixelDensity(min(2, displayDensity()));
  noStroke();

  reducedMotion = window.matchMedia &&
                  window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  buildWall();
  background(CFG.bg[0], CFG.bg[1], CFG.bg[2]);
}

function draw() {
  blendMode(BLEND);
  background(CFG.bg[0], CFG.bg[1], CFG.bg[2], CFG.trail);

  analyse();
  smoothFps = lerp(smoothFps, frameRate(), 0.05);

  for (const p of particles) p.update(bands[p.row], frameCount);

  drawSolid();
  drawTendrils();
  drawSeeds();

  drawVignette();
  drawHint();
}

/* ---------- 6. ANALYSE: MULTIBÅND + ONSET ------------------ */

// Log-fordelte bånd. Ét pr. række, så væggen bliver en analysator
// med bassen nederst og diskanten øverst.
function buildBands(n) {
  bands = [];

  for (let i = 0; i < n; i++) {
    const p  = n === 1 ? 0.5 : i / (n - 1);
    // Rækkens plads i spektret, brugt når lyden IKKE er tonal
    const nLo = 100 * pow(120, i / n);
    const nHi = 100 * pow(120, (i + 1) / n);
    const col = growthColor(p);

    bands.push({
      index: i, nLo, nHi, pitch: p, col, share: 0,
      // Alpha kvantiseres til faste trin, så farvestrengene kan laves
      // én gang i stedet for pr. frø pr. frame.
      pal: rampAlpha(col),

      // Dybe bånd får lang release, høje kort. Samme logik som på en
      // multibånds-kompressor — derfor hænger bassen i billedet mens
      // diskanten blinker.
      release: lerp(CFG.releaseLow, CFG.releaseHigh, p),
      k:    lerp(CFG.stiffLow, CFG.stiffHigh, p),
      damp: lerp(CFG.dampLow,  CFG.dampHigh,  p),
      ns:   lerp(CFG.noiseLow, CFG.noiseHigh, p),
      lift: map(p, 0, 1, 1, -1),
      speed: lerp(CFG.speedLow, CFG.speedHigh, p),

      level: 0, excite: 0, brk: 0,
      onsetT: -999, onsetAmt: 0,
      solid: 1, stroke: 'rgba(0,0,0,0)',
      t: random(1000)
    });
  }
}

// Vækstgradienten: okker -> mos -> lys kalkgrøn
function growthColor(p) {
  const a = p < 0.5 ? CFG.hueLow : CFG.hueMid;
  const b = p < 0.5 ? CFG.hueMid : CFG.hueHigh;
  const t = p < 0.5 ? p * 2 : (p - 0.5) * 2;
  return [lerp(a[0], b[0], t), lerp(a[1], b[1], t), lerp(a[2], b[2], t)];
}

function rampAlpha(c) {
  const out = [];
  const rgb = `${round(c[0])},${round(c[1])},${round(c[2])}`;
  for (let i = 0; i < ALPHA_STEPS; i++) {
    out.push(`rgba(${rgb},${((i + 1) / ALPHA_STEPS).toFixed(3)})`);
  }
  return out;
}

function analyse() {
  if (micReady)        analyseVoice();
  else if (micFailed)  mouseFallback();

  energy = 0;
  for (const b of bands) energy = max(energy, b.level);

  for (const b of bands) {
    // Lidt afsmitning, så en ren tone ikke efterlader resten af
    // væggen helt død — men kun lidt.
    b.excite = max(b.level, b.onsetAmt, energy * CFG.bleed);
    if (reducedMotion) b.excite *= 0.35;
    if (b.excite > 0) b.t += b.speed;

    // Spiringen, regnet pr. række. Den visuelle release er meget
    // langsommere end lydens, så frøene stadig er synlige mens de
    // driver hjem — ellers ville typen bare snappe tilbage.
    const target = constrain(b.excite / CFG.breakAt, 0, 1);
    b.brk = max(target, b.brk * CFG.breakRelease);
    if (b.brk < 0.004) b.brk = 0;

    // Typen falmer langsommere end frøene spirer, så bogstavet står
    // og bliver tyndere i stedet for at forsvinde under dem.
    b.solid  = pow(1 - b.brk, 0.55);
    b.stroke = `rgba(${round(b.col[0])},${round(b.col[1])},${round(b.col[2])},` +
               `${(b.brk * CFG.tendrilAlpha).toFixed(3)})`;
  }
}

function analyseVoice() {
  const an = fft.analyser;
  if (!waveBuf || waveBuf.length !== an.fftSize) waveBuf = new Float32Array(an.fftSize);
  an.getFloatTimeDomainData(waveBuf);
  fft.analyze();                       // spektret bruges kun til ikke-tonal lyd

  /* --- AMPLITUDE I dBFS ---------------------------------------
     RMS over hele vinduet. Vi arbejder i dB frem for lineært,
     fordi både gaten og anslags-detektionen skal opføre sig ens
     uanset hvor meget gain mikrofonen selv lægger på.           */
  let sum = 0;
  for (let i = 0; i < waveBuf.length; i++) sum += waveBuf[i] * waveBuf[i];
  const db = 20 * Math.log10(max(Math.sqrt(sum / waveBuf.length), 1e-7));

  /* --- ADAPTIV STØJBUND + SQUELCH ------------------------------
     Bunden falder hurtigt mod et nyt minimum, kryber kun meget
     langsomt op igen, og fryses når gaten står åben. Squelchen
     ovenpå har hysterese, så en lyd der vipper omkring tærsklen
     ikke får væggen til at blinke.                              */
  const gate = max(ampFloor + CFG.gateDb, CFG.hardGate);
  if (db < ampFloor)   ampFloor += (db - ampFloor) * CFG.floorFall;
  else if (db < gate)  ampFloor += (db - ampFloor) * CFG.floorRise;

  let lvl = constrain((db - gate) / CFG.rangeDb, 0, 1);
  if (ampOpen) { if (lvl < CFG.squelch * CFG.hysteresis) ampOpen = false; }
  else         { if (lvl > CFG.squelch)                  ampOpen = true;  }
  if (!ampOpen) lvl = 0;

  /* --- GRUNDTONE ----------------------------------------------
     Autokorrelation på tidssignalet, ikke båndenergi. En nynnet
     tone lægger energi i hele sin harmoniske række, så et FFT-bånd
     kan ikke skelne en dyb tone fra en lys — men periodiciteten
     kan. Det er derfor rækken følger tonen og ikke klangfarven.  */
  if (lvl > 0) {
    const p = detectPitch(waveBuf, sampleRate());
    f0 = p.f0;
    clarity = p.clarity;
  } else {
    clarity = 0;
  }

  const voiced = clarity > CFG.clarityMin && f0 > 0;
  if (voiced) {
    // Log-mapping, så hver oktav fylder lige meget på væggen
    const t = Math.log(f0 / CFG.voiceLow) / Math.log(CFG.voiceHigh / CFG.voiceLow);
    rowPos = lerp(rowPos, constrain(t, 0, 1) * (bands.length - 1), CFG.pitchGlide);
  }

  // Ikke-tonal lyd fordeles efter hvor i spektret energien ligger
  let total = 0;
  if (!voiced && lvl > 0) {
    for (const b of bands) { b.share = fft.getEnergy(b.nLo, b.nHi); total += b.share; }
    for (const b of bands) b.share = total > 0 ? b.share / total : 0;
  }

  // Anslag: et spring i det samlede niveau, ikke pr. bånd. En
  // konsonant eller et klap rammer alle bånd på én gang, så det er
  // helheden der skal aflæses.
  const hit = lvl > 0 && (db - prevDb) > CFG.onsetDb;
  prevDb = db;

  for (let i = 0; i < bands.length; i++) {
    const b = bands[i];
    let w = 0;

    if (voiced) {
      // Blødt vindue omkring den detekterede tone, så blomstringen
      // glider mellem rækker i stedet for at hoppe
      const d = abs(i - rowPos) / CFG.voiceSpread;
      const q = 1 - d * d;
      w = d >= 1 ? 0 : q * q;
    } else if (lvl > 0) {
      w = b.share * bands.length * CFG.noiseSpread;
    }

    const target = constrain(lvl * w, 0, 1);

    if (hit && w > 0.15 && frameCount - b.onsetT > CFG.onsetHold) {
      b.onsetT   = frameCount;
      b.onsetAmt = constrain(target, 0, 1);
    } else {
      b.onsetAmt *= CFG.onsetDecay;
    }

    b.level = lerp(b.level, target, target > b.level ? CFG.attack : b.release);
    if (b.level < 0.004) b.level = 0;
  }
}

/* --- AUTOKORRELATION ------------------------------------------
   Decimeres 4x med en simpel 4-taps middelværdi først. Det er
   både en grov lavpasfiltrering — som fjerner de høje harmoniske
   der ellers snyder detektoren — og en firdobling af hastigheden.
   Derefter normaliseret autokorrelation over netop det lag-område
   der svarer til stemmens register.                             */
function detectPitch(buf, sr) {
  const n = (buf.length / 4) | 0;
  if (!decBuf || decBuf.length !== n) {
    decBuf = new Float32Array(n);
    preBuf = new Float32Array(n + 1);
    nsdf   = new Float32Array(n + 1);
  }

  for (let i = 0; i < n; i++) {
    const j = i * 4;
    decBuf[i] = (buf[j] + buf[j + 1] + buf[j + 2] + buf[j + 3]) * 0.25;
  }
  const sr2 = sr / 4;

  // Prefix-sum af kvadraterne, så vinduets energi kan slås op i O(1)
  // i stedet for at blive regnet forfra for hvert lag.
  preBuf[0] = 0;
  for (let i = 0; i < n; i++) preBuf[i + 1] = preBuf[i] + decBuf[i] * decBuf[i];

  const lagMin = max(2, floor(sr2 / CFG.voiceHigh));
  const lagMax = min(n - 8, ceil(sr2 / CFG.voiceLow));
  if (lagMax <= lagMin) return { f0: 0, clarity: 0 };

  let best = -1, bestVal = 0;

  for (let lag = lagMin; lag <= lagMax; lag++) {
    let corr = 0;
    const m = n - lag;
    for (let i = 0; i < m; i++) corr += decBuf[i] * decBuf[i + lag];

    const den = Math.sqrt((preBuf[m] - preBuf[0]) * (preBuf[n] - preBuf[lag]));
    const v = den > 1e-12 ? corr / den : 0;
    nsdf[lag] = v;
    if (v > bestVal) { bestVal = v; best = lag; }
  }
  if (best < 0) return { f0: 0, clarity: 0 };

  /* Oktavkorrektion. Autokorrelation rammer notorisk en oktav for
     lavt, fordi det dobbelte lag også passer på en periodisk
     kurve. Er det halve lag næsten lige så godt, er det det rigtige. */
  const half = best >> 1;
  if (half >= lagMin && nsdf[half] > bestVal * 0.86) {
    bestVal = nsdf[half];
    best = half;
  }

  // Parabolsk interpolation for opløsning finere end ét sample
  let lag = best;
  if (best > lagMin && best < lagMax) {
    const y0 = nsdf[best - 1], y1 = bestVal, y2 = nsdf[best + 1];
    const den = 2 * (2 * y1 - y0 - y2);
    if (abs(den) > 1e-9) lag += constrain((y2 - y0) / den, -1, 1);
  }

  return { f0: sr2 / lag, clarity: constrain(bestVal, 0, 1) };
}

// Uden mikrofon: musen bliver til en oscillator. Højde vælger bånd,
// fart bliver til niveau — så demoen aldrig står død.
function mouseFallback() {
  const raw   = dist(mouseX, mouseY, pmouseX, pmouseY) / 90;
  const speed = raw < 0.18 ? 0 : constrain(raw, 0, 1);
  const idx   = floor(constrain(1 - mouseY / height, 0, 0.999) * bands.length);

  for (let i = 0; i < bands.length; i++) {
    const b = bands[i];
    const lvl = speed * (1 - constrain(abs(i - idx) / 2, 0, 1));

    if (lvl > b.level + 0.25 && frameCount - b.onsetT > CFG.onsetHold) {
      b.onsetT = frameCount;
      b.onsetAmt = lvl;
    } else {
      b.onsetAmt *= CFG.onsetDecay;
    }

    b.level = lerp(b.level, lvl, lvl > b.level ? CFG.attack : b.release);
    if (b.level < 0.004) b.level = 0;
  }
}

function startAudio() {
  if (mic) return;
  userStartAudio();

  mic = new p5.AudioIn();
  mic.start(
    () => {
      micReady = true;
      fft = new p5.FFT(CFG.fftSmooth, CFG.fftBins);
      fft.setInput(mic);
    },
    () => { micFailed = true; mic = null; }
  );
}

// Usynligt UI: hele lærredet er knappen.
function mousePressed() { startAudio(); }
function touchStarted() { startAudio(); }
function keyPressed()   { startAudio(); }

/* ---------- 7. RENDER -------------------------------------- */

// Hvilebilledet: ægte vektortypografi. Tegnes række for række, så
// hver række kan tynde ud i takt med sit eget frekvensbånd.
function drawSolid() {
  push();
  noStroke();
  if (fontReady) textFont(font); else textStyle(BOLD);
  textSize(glyphSize);
  textAlign(LEFT, BASELINE);

  for (let i = 0; i < tileRows.length; i++) {
    const a = bands[i].solid;
    if (a < 0.004) continue;
    fill(CFG.ink[0], CFG.ink[1], CFG.ink[2], 255 * a);
    for (const t of tileRows[i]) text(CFG.message, t.x, t.y);
  }
  pop();
}

/* Ranker: en buet tråd fra bogstavet ud til frøet. Kontrolpunktet
   ligger vinkelret på forbindelseslinjen, så tråden buer i stedet
   for at være en stiv radius — det er hele forskellen på en ranke
   og en fejlstreg. Én sti pr. bånd, så det bliver ét stroke-kald
   pr. række i stedet for tusinder.                                */
function drawTendrils() {
  const ctx = drawingContext;
  ctx.lineWidth = CFG.tendrilWidth;
  ctx.lineCap   = 'round';

  const minSq = CFG.tendrilMin * CFG.tendrilMin;

  for (const b of bands) {
    if (b.brk < 0.02) continue;
    const rg = rowRange[b.index];
    if (!rg) continue;

    ctx.beginPath();
    let drew = false;

    for (let i = rg.s; i < rg.e; i++) {
      const p = particles[i];
      if (p.alpha < 0.05) continue;

      const dx = p.pos.x - p.home.x;
      const dy = p.pos.y - p.home.y;
      if (dx * dx + dy * dy < minSq) continue;

      const cx = (p.home.x + p.pos.x) * 0.5 - dy * p.curl;
      const cy = (p.home.y + p.pos.y) * 0.5 + dx * p.curl;

      ctx.moveTo(p.home.x, p.home.y);
      ctx.quadraticCurveTo(cx, cy, p.pos.x, p.pos.y);
      drew = true;
    }

    if (drew) { ctx.strokeStyle = b.stroke; ctx.stroke(); }
  }
}

// Rå canvas2d frem for p5's rect(): markant hurtigere ved tusinder
// af frø. Farven kommer fra båndets plads i vækstgradienten.
function drawSeeds() {
  const ctx = drawingContext;

  for (const b of bands) {
    if (b.brk < 0.004) continue;
    const rg = rowRange[b.index];
    if (!rg) continue;

    const pal = b.pal;
    let last = -1;

    for (let i = rg.s; i < rg.e; i++) {
      const p = particles[i];
      const q = (p.alpha * ALPHA_STEPS) | 0;
      if (q < 1) continue;
      const k = q > ALPHA_STEPS - 1 ? ALPHA_STEPS - 1 : q;
      if (k !== last) { ctx.fillStyle = pal[k]; last = k; }
      const s = p.size;
      ctx.fillRect(p.pos.x - s * 0.5, p.pos.y - s * 0.5, s, s);
    }
  }
}

// Blød ramme, så ordene ikke bare bliver klippet brutalt ved kanten.
// Lagt oven på alle lag, så type, ranker og frø maskes ens.
function buildVignette() {
  const ctx = drawingContext;
  const c = `rgba(${CFG.bg[0]},${CFG.bg[1]},${CFG.bg[2]},`;
  const bw = width * 0.075, bh = height * 0.09;

  const ramp = (x0, y0, x1, y1) => {
    const g = ctx.createLinearGradient(x0, y0, x1, y1);
    g.addColorStop(0, c + '1)');
    g.addColorStop(1, c + '0)');
    return g;
  };

  vignettes = [
    { g: ramp(0, 0, bw, 0),               x: 0,          y: 0,           w: bw,    h: height },
    { g: ramp(width, 0, width - bw, 0),   x: width - bw, y: 0,           w: bw,    h: height },
    { g: ramp(0, 0, 0, bh),               x: 0,          y: 0,           w: width, h: bh },
    { g: ramp(0, height, 0, height - bh), x: 0,          y: height - bh, w: width, h: bh }
  ];
}

function drawVignette() {
  const ctx = drawingContext;
  for (const v of vignettes) {
    ctx.fillStyle = v.g;
    ctx.fillRect(v.x, v.y, v.w, v.h);
  }
}

function drawHint() {
  if (micReady || micFailed) hintAlpha = lerp(hintAlpha, 0, 0.05);
  if (hintAlpha < 2) return;

  push();
  noStroke();
  rectMode(CENTER);
  fill(CFG.bg[0], CFG.bg[1], CFG.bg[2], hintAlpha * 0.94);
  rect(width / 2, height - 58, 250, 32);

  textAlign(CENTER, CENTER);
  textStyle(NORMAL);
  textSize(10);
  if (fontReady) textFont(font);
  fill(CFG.ink[0], CFG.ink[1], CFG.ink[2], hintAlpha * 0.75);
  text('CLICK TO ENABLE MICROPHONE', width / 2, height - 57);
  pop();
}

/* ---------- 8. VÆGGEN: TEKST -> GITTER --------------------- */

function buildWall() {
  const ref = measureRef();

  // Layoutet drives af hvor mange gentagelser der skal stå i højden —
  // ikke af en fast fontstørrelse.
  const rowsWanted = height < 560 ? 4 : height < 820 ? 5 : CFG.rowsTall;

  let size = (height / rowsWanted) / (CFG.leading * ref.capRatio);
  size = min(size, (width * 0.62) / ref.widthRatio);
  glyphSize = size = constrain(size, 20, 240);

  const box   = measureBox(size);
  const tileW = box.w + size * CFG.gap;
  const lead  = box.h * CFG.leading;

  const cols     = ceil(width / tileW) + 1;
  const rowCount = ceil(height / lead) + 1;

  const x0 = (width  - cols * tileW) / 2;
  const y0 = (height - rowCount * lead) / 2 + (lead - box.h) / 2;

  buildBands(rowCount);

  // Ankre pr. række. Bånd nummereres nedefra: nederste række = bas.
  tileRows = [];
  const rows = [];
  for (let r = 0; r < rowCount; r++) {
    const stagger = ((r * 0.37) % 1) * tileW;
    const y    = y0 + r * lead;
    const band = rowCount - 1 - r;
    const list = [];

    tileRows[band] = [];
    for (let c = -1; c < cols; c++) {
      const x = x0 + c * tileW + stagger;
      if (x > width) continue;
      list.push({ x, y });
      // Ankeret er baseline-venstre, præcis som textToPoints regner
      // ud fra — så vektorlag og frølag flugter til pixlen.
      tileRows[band].push({ x: x + box.ax, y: y + box.ay });
    }
    rows[band] = list;
  }

  let originCount = 0;
  for (const list of rows) originCount += list.length;

  // Budgettet fordeles jævnt over de synlige gentagelser og skaleres
  // efter skærmarealet, så en telefon ikke render 5.600 frø.
  const budget  = min(CFG.maxParticles, round(width * height / 240));
  const perTile = max(50, floor(budget / max(1, originCount)));
  const base    = tilePoints(size, box, perTile);

  // Frøene lægges sammenhængende pr. bånd, så hver række kan tegnes
  // som ét enkelt stroke- og fill-forløb.
  const homes = [];
  rowRange = [];

  for (let band = 0; band < rowCount; band++) {
    const s = homes.length;
    for (const o of rows[band]) {
      for (const pt of base) {
        homes.push({ x: o.x + pt.x, y: o.y + pt.y, row: band, edge: pt.edge });
      }
    }
    rowRange[band] = { s, e: homes.length };
  }

  // Genbrug eksisterende frø ved resize, så de glider på plads i
  // stedet for at poppe
  const next = [];
  for (let i = 0; i < homes.length; i++) {
    const h = homes[i];
    if (particles[i]) { particles[i].reseat(h.x, h.y, h.row); next.push(particles[i]); }
    else              { next.push(new Seed(h.x, h.y, h.row, h.edge)); }
  }
  particles = next;

  buildVignette();
}

// Punktsættet for ÉN gentagelse — resten er translationer af det samme
// sæt. Konturen kommer fra textToPoints (ægte vektorgeometri, så
// bogstavkanterne er skarpe); kroppen fra et raster, så bogstaverne
// har fyld. Kant og krop mærkes hver for sig, fordi kanten skal spire
// først.
function tilePoints(size, box, budget) {
  const outline = fontReady
    ? font.textToPoints(CFG.message, box.ax, box.ay, size, {
        sampleFactor: CFG.sampleFactor,
        simplifyThreshold: 0
      }).map(p => ({ x: p.x, y: p.y, edge: true }))
    : [];

  return outline.concat(interior(size, budget - outline.length));
}

// Rasteriserer teksten offscreen og sampler dens indre på et regulært
// gitter. Gitterafstanden regnes ud fra det faktiske blækareal mod
// budgettet, så fordelingen er jævn uanset skærmstørrelse.
function interior(size, budget) {
  if (budget < 20) { gridStep = max(3, size * 0.05); return []; }

  const pg = createGraphics(ceil(size * CFG.message.length * 0.9) + 20, ceil(size * 2));
  pg.pixelDensity(1);
  pg.background(0);
  pg.fill(255);
  pg.noStroke();
  pg.textAlign(LEFT, TOP);
  if (fontReady) pg.textFont(font); else pg.textStyle(BOLD);
  pg.textSize(size);
  pg.text(CFG.message, 4, 4);
  pg.loadPixels();

  // Første pas: estimér blækarealet groft
  const probe = max(2, round(size * 0.06));
  let ink = 0;
  for (let y = 0; y < pg.height; y += probe)
    for (let x = 0; x < pg.width; x += probe)
      if (pg.pixels[4 * (y * pg.width + x)] > 128) ink++;

  gridStep = constrain(sqrt(ink * probe * probe / budget), 2.5, size * 0.14);

  // Andet pas: den rigtige sampling
  const step = max(2, round(gridStep));
  const pts = [];
  let minX = 1e9, minY = 1e9;

  for (let y = 0; y < pg.height; y += step) {
    for (let x = 0; x < pg.width; x += step) {
      if (pg.pixels[4 * (y * pg.width + x)] > 128) {
        pts.push({ x, y, edge: false });
        minX = min(minX, x); minY = min(minY, y);
      }
    }
  }
  pg.remove();

  // Flugt med konturpunkterne, som ligger med bbox-hjørnet i (0,0)
  for (const p of pts) { p.x -= minX; p.y -= minY; }
  return pts;
}

// Tekstens tætte bounding box plus ankeret (baseline-venstre) der
// placerer den med hjørnet i (0,0).
function measureBox(size) {
  if (fontReady) {
    const b = font.textBounds(CFG.message, 0, 0, size);
    return { w: b.w, h: b.h, ax: -b.x, ay: -b.y };
  }
  const pg = createGraphics(10, 10);
  pg.textStyle(BOLD);
  pg.textSize(size);
  const w = pg.textWidth(CFG.message);
  pg.remove();
  return { w, h: size * 0.72, ax: 0, ay: size * 0.72 };
}

function measureRef() {
  const b = measureBox(100);
  return { capRatio: b.h / 100, widthRatio: b.w / 100 };
}

/* ---------- 9. RESPONSIVITET ------------------------------- */

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(buildWall, 120);   // debounce
}