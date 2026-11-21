/* ============================================================
   ХРОНОСКОП — жестовое управление камерой
   ✌️ 2 пальца — волна инверсии цвета
   🤟 3 пальца — хронозона (замороженное время + вихрь частиц)
   ✊ кулак — сброс
   🖐 левая ладонь — пси-линза
   ============================================================ */
'use strict';

/* ── DOM ─────────────────────────────────────────────────── */
const canvas = document.getElementById('scene');
const ctx = canvas.getContext('2d');
const overlay = document.getElementById('overlay');
const statusEl = document.getElementById('status');
const hintInvert = document.getElementById('hint-invert');
const hintField = document.getElementById('hint-field');
const hintFist = document.getElementById('hint-fist');
const hintHole = document.getElementById('hint-hole');
const hintLens = document.getElementById('hint-lens');
const stCam = document.getElementById('st-cam');
const stHand = document.getElementById('st-hand');
const stFps = document.getElementById('st-fps');

/* ── размеры (Retina: рендер в физических пикселях) ──────── */
let cw = 0, ch = 0;            // размер сцены (css px)
let dpr = 1;
function resize() {
  cw = window.innerWidth;
  ch = window.innerHeight;
  dpr = Math.min(window.devicePixelRatio || 1, 2);
  canvas.width = Math.round(cw * dpr);
  canvas.height = Math.round(ch * dpr);
  for (const c of [normalC, invC, frozenC, snapC]) { c.width = canvas.width; c.height = canvas.height; }
  for (const x of [normalX, invX, frozenX, snapX]) x.setTransform(dpr, 0, 0, dpr, 0, 0);
}
const normalC = document.createElement('canvas'); // живой кадр (зеркальный)
const invC = document.createElement('canvas');    // инвертированный кадр
const frozenC = document.createElement('canvas'); // застывший кадр хронозоны
const snapC = document.createElement('canvas');   // снимок экрана для линзы дыры
const normalX = normalC.getContext('2d');
const invX = invC.getContext('2d');
const frozenX = frozenC.getContext('2d');
const snapX = snapC.getContext('2d');
window.addEventListener('resize', resize);
resize();

/* ── состояние ───────────────────────────────────────────── */
let invertOn = false;          // текущее инвертирование (после волны)
let wave = null;               // { x, y, r, target } — расширяющийся фронт
let fieldOn = false;           // хронозона открыта
let fieldR = 0;                // текущий радиус хронозоны
const FIELD_R_MAX_K = 0.27;    // радиус от min(cw,ch)
let hole = null;               // чёрная дыра { x, y, R, power }
let pinchHeld = false;         // щипок удерживается
let particles = [];            // частицы вихря / взрыва
let trail = [];                // след ладони
let stableCount = -1;          // стабильное число пальцев
let countBuffer = [];          // буфер для дебаунса жестов
const COUNT_STABLE_N = 9;
let handSeen = false;
let leftLens = null;           // { x, y, open }
let hueT = 0;
let lastT = performance.now();
let shake = 0;                 // тряска экрана от ударной волны
let flashA = 0;                // вспышка
let fpsFrames = 0;
let fpsLast = performance.now();

/* сглаживание скелета рук (убирает дрожание точек) */
const smoothMap = new Map();
function smoothedPts(key, lms) {
  const pts = lms.map(toScreen);
  const prev = smoothMap.get(key);
  if (prev && prev.length === pts.length) {
    for (let i = 0; i < pts.length; i++) {
      pts[i].x = prev[i].x + (pts[i].x - prev[i].x) * 0.62;
      pts[i].y = prev[i].y + (pts[i].y - prev[i].y) * 0.62;
    }
  }
  smoothMap.set(key, pts);
  return pts;
}

/* сглаженная позиция ладони (для хронозоны) */
const palm = { x: 0, y: 0, has: false };

/* ── звук ────────────────────────────────────────────────── */
let actx = null;
function beep(freq, dur = 0.14, type = 'sine', gain = 0.12) {
  try {
    if (!actx) actx = new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state === 'suspended') actx.resume();
    const o = actx.createOscillator();
    const g = actx.createGain();
    o.type = type;
    o.frequency.value = freq;
    g.gain.setValueAtTime(0.0001, actx.currentTime);
    g.gain.exponentialRampToValueAtTime(gain, actx.currentTime + 0.02);
    g.gain.exponentialRampToValueAtTime(0.0001, actx.currentTime + dur);
    o.connect(g).connect(actx.destination);
    o.start();
    o.stop(actx.currentTime + dur + 0.05);
  } catch (e) { /* без звука — не страшно */ }
}
window.addEventListener('pointerdown', () => { if (actx && actx.state === 'suspended') actx.resume(); });

/* ── геометрия кадра: cover + зеркало ────────────────────── */
let map = { s: 1, dx: 0, dy: 0, dw: 0, dh: 0 };
function computeMap() {
  const vw = video.videoWidth || 1280, vh = video.videoHeight || 720;
  const s = Math.max(cw / vw, ch / vh);
  map = { s, dw: vw * s, dh: vh * s, dx: (cw - vw * s) / 2, dy: (ch - vh * s) / 2 };
}
/* landmark (0..1, координаты камеры) → экранные зеркальные px */
function toScreen(lm) {
  return {
    x: cw - (map.dx + lm.x * map.dw),
    y: map.dy + lm.y * map.dh,
  };
}

/* ── распознавание жестов ────────────────────────────────── */
const CONNS = [
  [0,1],[1,2],[2,3],[3,4],[0,5],[5,6],[6,7],[7,8],[5,9],[9,10],[10,11],[11,12],
  [9,13],[13,14],[14,15],[15,16],[13,17],[17,18],[18,19],[19,20],[0,17]
];
const TIPS = [8, 12, 16, 20], PIPS = [6, 10, 14, 18];

function dist3(a, b) {
  const dx = a.x - b.x, dy = a.y - b.y, dz = (a.z || 0) - (b.z || 0);
  return Math.hypot(dx, dy, dz);
}
function palmCenter(lms) {
  const ids = [0, 5, 9, 13, 17];
  let x = 0, y = 0;
  for (const i of ids) { x += lms[i].x; y += lms[i].y; }
  return { x: x / ids.length, y: y / ids.length };
}
function countFingers(lms) {
  let n = 0;
  for (let f = 0; f < 4; f++) {
    if (dist3(lms[TIPS[f]], lms[0]) > dist3(lms[PIPS[f]], lms[0]) * 1.04) n++;
  }
  return n;
}
function isOpenPalm(lms) { return countFingers(lms) >= 4; }

/* ── реакции на жесты ────────────────────────────────────── */
function toggleInvert(origin) {
  const target = !invertOn;
  if (wave) { invertOn = wave.target; }        // мгновенно завершаем прошлую волну
  wave = { x: origin.x, y: origin.y, r: 0, target };
  shake = 13;                                  // удар: тряска + вспышка + низкий бум
  flashA = 0.3;
  beep(target ? 880 : 440, 0.16, 'triangle');
  beep(65, 0.32, 'sine', 0.22);
}
function openField() {
  fieldOn = true;
  /* застывший кадр = то, что сейчас на экране */
  frozenX.clearRect(0, 0, cw, ch);
  frozenX.drawImage(invertOn ? invC : normalC, 0, 0, cw, ch);
  spawnVortex();
  beep(520, 0.22, 'sine');
}
function closeField() {
  fieldOn = false;
  burst();
  beep(390, 0.2, 'sine');
}
function resetAll(origin) {
  if (invertOn || wave) toggleInvert(origin);
  if (fieldOn) closeField();
  beep(220, 0.25, 'sawtooth');
}

function onStableGesture(n, origin) {
  if (n === 2) toggleInvert(origin);
  else if (n === 3) fieldOn ? closeField() : openField();
  else if (n === 0) resetAll(origin);
}

/* ── частицы ─────────────────────────────────────────────── */
function spawnVortex() {
  particles = [];
  const R = Math.min(cw, ch) * FIELD_R_MAX_K;
  let img = null;
  try { img = frozenX.getImageData(0, 0, cw * dpr, ch * dpr); } catch (e) { /* taint — без цветов */ }
  const N = 130;
  for (let i = 0; i < N; i++) {
    const a = Math.random() * Math.PI * 2;
    const d = Math.sqrt(Math.random()) * R * 0.95;
    const px = Math.round((palm.x + Math.cos(a) * d) * dpr);
    const py = Math.round((palm.y + Math.sin(a) * d) * dpr);
    let col = '160, 240, 255';
    if (img && px >= 0 && py >= 0 && px < cw * dpr && py < ch * dpr) {
      const k = (py * cw * dpr + px) * 4;
      col = `${img.data[k]}, ${img.data[k + 1]}, ${img.data[k + 2]}`;
    }
    particles.push({
      relX: Math.cos(a) * d, relY: Math.sin(a) * d,
      angle: a, dist: d, spd: 0.4 + Math.random() * 1.1,
      size: 1.5 + Math.random() * 2.5,
      col, mode: 'vortex', life: 1, vx: 0, vy: 0, ph: Math.random() * Math.PI * 2,
    });
  }
}
function burst() {
  const R = Math.min(cw, ch) * FIELD_R_MAX_K;
  for (const p of particles) {
    if (p.mode !== 'vortex') continue;
    const a = Math.atan2(p.relY, p.relX);
    const sp = 2 + Math.random() * 6;
    p.mode = 'free';
    p.cx = palm.x; p.cy = palm.y;
    p.vx = Math.cos(a) * sp * (0.5 + p.dist / R);
    p.vy = Math.sin(a) * sp * (0.5 + p.dist / R) - 1.5;
    p.life = 1;
  }
}

/* ── чёрная дыра: спиральные частицы аккреции ───────────── */
const HOT_COLS = ['255, 214, 150', '255, 160, 90', '255, 240, 225', '255, 120, 70', '255, 190, 120'];
function spawnSpiral() {
  const R = hole.R;
  const N = 90;
  for (let i = 0; i < N; i++) {
    particles.push({
      mode: 'spiral',
      angle: Math.random() * Math.PI * 2,
      dist: R * (0.35 + Math.random() * 1.2),
      spd: 0.5 + Math.random() * 1.2,
      size: 1.2 + Math.random() * 2.2,
      col: HOT_COLS[(Math.random() * HOT_COLS.length) | 0],
      ph: Math.random() * Math.PI * 2,
      relX: 0, relY: 0, cx: 0, cy: 0, life: 1, vx: 0, vy: 0,
    });
  }
}
function holeRelease() {
  for (const p of particles) {
    if (p.mode !== 'spiral') continue;
    const a = Math.atan2(p.relY, p.relX);
    const sp = 3 + Math.random() * 7;
    p.mode = 'free';
    p.cx = hole.x; p.cy = hole.y;
    p.vx = Math.cos(a) * sp;
    p.vy = Math.sin(a) * sp;
    p.life = 1;
  }
}

function updateParticles(dt) {
  const R = Math.min(cw, ch) * FIELD_R_MAX_K;
  for (const p of particles) {
    if (p.mode === 'vortex') {
      p.angle += p.spd * 0.035 * dt;
      const wob = Math.sin(hueT * 0.05 + p.ph) * R * 0.08;
      const d = Math.min(R * 0.97, p.dist + wob);
      p.relX = Math.cos(p.angle) * d;
      p.relY = Math.sin(p.angle) * d;
    } else if (p.mode === 'spiral') {
      if (!hole) {   // дыра исчезла — частицы разлетаются свободно
        p.mode = 'free';
        p.cx = palm.x; p.cy = palm.y;
        const fa = Math.atan2(p.relY, p.relX);
        p.vx = Math.cos(fa) * 3; p.vy = Math.sin(fa) * 3;
        p.life = 1;
        continue;
      }
      /* закручивание и падение к горизонту событий */
      p.angle += p.spd * 0.05 * dt * (1 + (hole.R * 1.6) / (p.dist + 25));
      p.dist -= (0.45 + 42 / (p.dist + 12)) * dt * (0.4 + hole.power);
      p.relX = Math.cos(p.angle) * p.dist;
      p.relY = Math.sin(p.angle) * p.dist;
      if (p.dist < hole.R * 0.14) {
        if (hole && hole.power > 0.4) {
          p.dist = hole.R * (1.25 + Math.random() * 0.45);
          p.angle = Math.random() * Math.PI * 2;
        } else {
          p.mode = 'free';
          p.cx = hole.x; p.cy = hole.y;
          const a = Math.atan2(p.relY, p.relX);
          p.vx = Math.cos(a) * (2 + Math.random() * 4);
          p.vy = Math.sin(a) * (2 + Math.random() * 4);
          p.life = 1;
        }
      }
    } else {
      p.vx *= 0.985; p.vy = p.vy * 0.985 + 0.05 * dt;
      p.relX += p.vx * dt; p.relY += p.vy * dt;
      p.life -= 0.012 * dt;
    }
  }
  particles = particles.filter(p => p.mode !== 'free' || p.life > 0);
}
function particleCenter(p) {
  if (p.mode === 'vortex') return palm;
  if (p.mode === 'spiral') return hole;
  return { x: p.cx, y: p.cy };
}
function drawParticles() {
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  for (const p of particles) {
    const c = particleCenter(p);
    if (!c) continue;
    const a = p.mode === 'free' ? p.life
      : 0.55 + 0.35 * Math.sin(hueT * 0.08 + p.ph);
    ctx.fillStyle = `rgba(${p.col}, ${a.toFixed(3)})`;
    const s = p.size * (p.mode === 'free' ? p.life + 0.4 : 1);
    ctx.fillRect(c.x + p.relX - s / 2, c.y + p.relY - s / 2, s, s);
  }
  ctx.restore();
}

/* ── отрисовка ───────────────────────────────────────────── */
function drawCover(x2, img) {
  x2.save();
  x2.translate(cw, 0); x2.scale(-1, 1);          // зеркало
  x2.drawImage(img, cw - map.dx - map.dw, map.dy, map.dw, map.dh);
  x2.restore();
}
function updateFrames() {
  drawCover(normalX, video);
  drawCover(invX, video);
  /* инверсия через composite «difference» — работает во всех браузерах */
  invX.globalCompositeOperation = 'difference';
  invX.fillStyle = '#fff';
  invX.fillRect(0, 0, cw, ch);
  invX.globalCompositeOperation = 'source-over';
}

function drawBase() {
  ctx.drawImage(invertOn ? invC : normalC, 0, 0, cw, ch);
}

function drawWave() {
  if (!wave) return;
  const target = wave.target ? invC : normalC;
  const { x, y, r } = wave;

  /* внутренность волны */
  ctx.save();
  ctx.beginPath();
  ctx.arc(x, y, r, 0, Math.PI * 2);
  ctx.clip();
  ctx.drawImage(target, 0, 0, cw, ch);
  /* рывок пространства у самого фронта — растяжение наружу */
  ctx.beginPath();
  ctx.arc(x, y, r, 0, Math.PI * 2);
  ctx.arc(x, y, Math.max(0, r - 42), 0, Math.PI * 2, true);
  ctx.clip();
  ctx.translate(x, y);
  ctx.scale(1.045, 1.045);
  ctx.translate(-x, -y);
  ctx.drawImage(target, 0, 0, cw, ch);
  ctx.restore();

  /* свечение фронта */
  const g = ctx.createRadialGradient(x, y, Math.max(0, r - 34), x, y, r + 6);
  g.addColorStop(0, 'rgba(120,255,230,0)');
  g.addColorStop(0.7, wave.target ? 'rgba(150,255,235,0.5)' : 'rgba(255,150,230,0.5)');
  g.addColorStop(1, 'rgba(255,255,255,0)');
  ctx.fillStyle = g;
  ctx.beginPath();
  ctx.arc(x, y, r + 6, 0, Math.PI * 2);
  ctx.fill();

  /* хроматическая аберрация + белый фронт */
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  ctx.lineWidth = 2;
  ctx.strokeStyle = 'rgba(255, 70, 70, 0.4)';
  ctx.beginPath(); ctx.arc(x, y, r + 6, 0, Math.PI * 2); ctx.stroke();
  ctx.strokeStyle = 'rgba(70, 210, 255, 0.4)';
  ctx.beginPath(); ctx.arc(x, y, Math.max(1, r - 6), 0, Math.PI * 2); ctx.stroke();
  ctx.shadowColor = wave.target ? 'rgba(140, 255, 230, 1)' : 'rgba(255, 150, 230, 1)';
  ctx.shadowBlur = 26;
  ctx.strokeStyle = 'rgba(255, 255, 255, 0.95)';
  ctx.lineWidth = 2.5;
  ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.stroke();
  ctx.restore();

  /* затухающая рябь позади фронта */
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  for (let k = 1; k <= 3; k++) {
    const rk = r - k * 30;
    if (rk <= 0) continue;
    ctx.strokeStyle = `rgba(200, 245, 255, ${(0.3 - k * 0.08).toFixed(3)})`;
    ctx.lineWidth = 1.2;
    ctx.beginPath(); ctx.arc(x, y, rk, 0, Math.PI * 2); ctx.stroke();
  }
  ctx.restore();
}

function drawField(dt) {
  if (!fieldOn && fieldR <= 0.5) return;
  const Rmax = Math.min(cw, ch) * FIELD_R_MAX_K;
  fieldR += ((fieldOn ? Rmax : 0) - fieldR) * Math.min(1, 0.16 * dt);
  if (fieldR < 0.5) return;

  ctx.save();
  ctx.beginPath();
  ctx.arc(palm.x, palm.y, fieldR, 0, Math.PI * 2);
  ctx.clip();
  ctx.drawImage(frozenC, 0, 0, cw, ch);
  /* голографический оттенок */
  ctx.fillStyle = 'rgba(80, 220, 255, 0.07)';
  ctx.fillRect(palm.x - fieldR, palm.y - fieldR, fieldR * 2, fieldR * 2);
  /* сканирующие линии */
  ctx.fillStyle = 'rgba(180, 255, 250, 0.06)';
  const off = (hueT * 0.9) % 8;
  for (let y = palm.y - fieldR + off; y < palm.y + fieldR; y += 8) {
    ctx.fillRect(palm.x - fieldR, y, fieldR * 2, 2);
  }
  ctx.restore();

  /* кольцо хронозоны */
  ctx.save();
  ctx.shadowColor = 'rgba(100, 240, 255, 0.9)';
  ctx.shadowBlur = 18;
  ctx.strokeStyle = `hsla(${(190 + 40 * Math.sin(hueT * 0.04)) | 0}, 100%, 70%, 0.9)`;
  ctx.lineWidth = 2.5;
  ctx.beginPath();
  ctx.arc(palm.x, palm.y, fieldR, 0, Math.PI * 2);
  ctx.stroke();
  ctx.restore();
}

function drawLens() {
  if (!leftLens || !leftLens.open) return;
  const R = Math.min(cw, ch) * 0.22;
  ctx.save();
  ctx.beginPath();
  ctx.arc(leftLens.x, leftLens.y, R, 0, Math.PI * 2);
  ctx.clip();
  ctx.drawImage(invertOn ? invC : normalC, 0, 0, cw, ch);
  /* психоделика: blend-режим «hue» перекрашивает зону циклическим цветом */
  ctx.globalCompositeOperation = 'hue';
  ctx.fillStyle = `hsl(${(hueT * 3) % 360}, 100%, 50%)`;
  ctx.fillRect(leftLens.x - R, leftLens.y - R, R * 2, R * 2);
  ctx.restore();
  ctx.strokeStyle = 'rgba(255, 140, 250, 0.75)';
  ctx.lineWidth = 2;
  ctx.beginPath();
  ctx.arc(leftLens.x, leftLens.y, R, 0, Math.PI * 2);
  ctx.stroke();
}

/* ── чёрная дыра: гравитационное искривление ─────────────── */
function updateHole(dt) {
  if (!hole) return;
  const target = pinchHeld ? 1 : 0;
  hole.power += (target - hole.power) * Math.min(1, 0.14 * dt);
  if (!pinchHeld && hole.power < 0.03) {
    hole = null;
    return;
  }
  if (!pinchHeld && hole.power < 0.9 && !hole.released) {
    hole.released = true;
    holeRelease();
    beep(660, 0.22, 'triangle');
    setTimeout(() => beep(330, 0.3, 'sine'), 90);
  }
}

function drawHole() {
  if (!hole || hole.power <= 0.02) return;
  const { x, y, R, power } = hole;

  /* снимок того, что уже нарисовано под дырой */
  snapX.clearRect(0, 0, cw, ch);
  snapX.drawImage(canvas, 0, 0, cw, ch);

  /* искривление: кольца, каждое растянуто и закручено к центру */
  const N = 30;
  const rOut = R * 1.7;
  for (let i = 0; i < N; i++) {
    const r1 = rOut * (i / N);
    const r2 = rOut * ((i + 1) / N);
    const rMid = (r1 + r2) / 2;
    const s = rMid + power * (R * R * 1.15) / (rMid + 8);   // откуда берём свет
    const th = power * 0.85 * (R / (rMid + 8));             // закрутка
    const f = s / rMid;
    ctx.save();
    ctx.beginPath();
    ctx.arc(x, y, r2, 0, Math.PI * 2);
    ctx.arc(x, y, r1, 0, Math.PI * 2, true);
    ctx.clip();
    ctx.translate(x, y);
    ctx.rotate(th);
    ctx.scale(f, f);
    ctx.translate(-x, -y);
    ctx.drawImage(snapC, 0, 0, cw, ch);
    ctx.restore();
  }

  /* горизонт событий — тёмное ядро */
  ctx.fillStyle = `rgba(2, 2, 10, ${(0.9 * power).toFixed(3)})`;
  ctx.beginPath();
  ctx.arc(x, y, R * 0.3, 0, Math.PI * 2);
  ctx.fill();

  /* аккреционный диск */
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  const g = ctx.createRadialGradient(x, y, R * 0.28, x, y, R * 0.85);
  g.addColorStop(0, `rgba(255, 205, 130, ${(0.5 * power).toFixed(3)})`);
  g.addColorStop(0.4, `rgba(255, 120, 60, ${(0.22 * power).toFixed(3)})`);
  g.addColorStop(1, 'rgba(255, 80, 40, 0)');
  ctx.fillStyle = g;
  ctx.beginPath();
  ctx.arc(x, y, R * 0.85, 0, Math.PI * 2);
  ctx.fill();
  /* фотонное кольцо */
  ctx.shadowColor = 'rgba(255, 190, 120, 0.95)';
  ctx.shadowBlur = 22;
  ctx.strokeStyle = `rgba(255, 235, 200, ${(0.75 * power).toFixed(3)})`;
  ctx.lineWidth = 1.6;
  ctx.beginPath();
  ctx.arc(x, y, R * 0.33, 0, Math.PI * 2);
  ctx.stroke();
  ctx.restore();
}

function drawTrail(dt) {
  if (palm.has) {
    trail.push({ x: palm.x, y: palm.y });
    if (trail.length > 26) trail.shift();
  } else if (trail.length) {
    trail.shift();
  }
  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  for (let i = 0; i < trail.length; i++) {
    const t = i / trail.length;
    const p = trail[i];
    ctx.fillStyle = `hsla(${(hueT * 2 + i * 9) % 360}, 100%, 65%, ${(t * 0.28).toFixed(3)})`;
    ctx.beginPath();
    ctx.arc(p.x, p.y, 1.5 + t * 4.5, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.restore();
}

function drawSkeleton(pts, color) {
  ctx.save();
  ctx.shadowColor = color;
  ctx.shadowBlur = 10;
  ctx.strokeStyle = color;
  ctx.lineWidth = 2;
  ctx.beginPath();
  for (const [a, b] of CONNS) {
    ctx.moveTo(pts[a].x, pts[a].y);
    ctx.lineTo(pts[b].x, pts[b].y);
  }
  ctx.stroke();
  ctx.fillStyle = '#fff';
  for (let i = 0; i < pts.length; i++) {
    const r = (i === 4 || TIPS.includes(i)) ? 4 : 2.4;
    ctx.beginPath();
    ctx.arc(pts[i].x, pts[i].y, r, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.restore();
}

function drawCountBadge(n, x, y) {
  const label = `${n}`;
  ctx.save();
  ctx.font = '600 13px "SF Mono", Menlo, monospace';
  const w = ctx.measureText(label).width + 18;
  ctx.fillStyle = 'rgba(5, 12, 20, 0.6)';
  ctx.beginPath();
  if (ctx.roundRect) ctx.roundRect(x - w / 2, y - 40, w, 22, 11);
  else ctx.rect(x - w / 2, y - 40, w, 22);
  ctx.fill();
  ctx.strokeStyle = 'rgba(140, 230, 255, 0.5)';
  ctx.lineWidth = 1;
  ctx.stroke();
  ctx.fillStyle = '#aef2ff';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillText(label, x, y - 29);
  ctx.restore();
}

/* ── обновление HUD ──────────────────────────────────────── */
function updateHud() {
  hintInvert.classList.toggle('active', invertOn || !!(wave && wave.target));
  hintField.classList.toggle('active', fieldOn);
  hintFist.classList.toggle('active', false);
  hintHole.classList.toggle('active', pinchHeld || !!hole);
  hintLens.classList.toggle('active', !!(leftLens && leftLens.open));
  stCam.classList.add('on');
  stHand.classList.toggle('on', handSeen);
}

/* ── MediaPipe ───────────────────────────────────────────── */
const video = document.createElement('video');
video.playsInline = true;
video.muted = true;

let hands = null;
let sending = false;

function onResults(res) {
  /* кадры обновляем всегда */
  computeMap();
  updateFrames();

  let rightLms = null, rightCount = 0;
  leftLens = null;
  handSeen = false;

  if (res.multiHandLandmarks && res.multiHandLandmarks.length) {
    for (let i = 0; i < res.multiHandLandmarks.length; i++) {
      const lms = res.multiHandLandmarks[i];
      const label = res.multiHandedness[i] && res.multiHandedness[i].label;
      const pc = palmCenter(lms);
      const sp = toScreen(pc);
      if (label === 'Right') {
        handSeen = true;
        rightLms = lms;
        rightCount = countFingers(lms);

        /* щипок: большой + указательный (с гистерезисом) */
        const unit = dist3(lms[0], lms[9]) || 1;
        const pd = dist3(lms[4], lms[8]);
        const mp = toScreen({
          x: (lms[4].x + lms[8].x) / 2,
          y: (lms[4].y + lms[8].y) / 2,
        });
        if (!pinchHeld && pd < unit * 0.30) {
          pinchHeld = true;
          hole = { x: mp.x, y: mp.y, R: Math.min(cw, ch) * 0.20, power: 0, released: false };
          spawnSpiral();
          beep(90, 0.5, 'sawtooth');
        }
        if (pinchHeld && pd > unit * 0.52) pinchHeld = false;
        if (pinchHeld && hole) {
          const k = Math.min(1, 0.35);
          hole.x += (mp.x - hole.x) * k;
          hole.y += (mp.y - hole.y) * k;
        }

        /* сглаживание ладони */
        if (!palm.has) { palm.x = sp.x; palm.y = sp.y; palm.has = true; }
        else {
          palm.x += (sp.x - palm.x) * 0.35;
          palm.y += (sp.y - palm.y) * 0.35;
        }
      } else if (label === 'Left') {
        leftLens = { x: sp.x, y: sp.y, open: isOpenPalm(lms) };
      }
    }
  }
  if (!handSeen) {
    palm.has = false;
    if (pinchHeld) pinchHeld = false;   // рука пропала — дыра гаснет
  }

  /* дебаунс жестов (щипок перекрывает счёт пальцев) */
  if (handSeen && !pinchHeld) {
    countBuffer.push(rightCount);
    if (countBuffer.length > COUNT_STABLE_N) countBuffer.shift();
    if (countBuffer.length === COUNT_STABLE_N &&
        countBuffer.every(c => c === rightCount) &&
        rightCount !== stableCount) {
      stableCount = rightCount;
      onStableGesture(rightCount, { x: palm.x, y: palm.y });
    }
  } else {
    countBuffer = [];
    stableCount = -1;
  }

  /* физика волны */
  if (wave) {
    wave.r += 46;
    if (wave.r > Math.hypot(cw, ch)) { invertOn = wave.target; wave = null; }
  }

  const dtF = Math.max(0.5, Math.min(2, (performance.now() - lastT) / 16.6));
  updateHole(dtF);
  updateParticles(dtF);
  lastT = performance.now();
  hueT++;

  /* ── рендер (Retina + тряска) ── */
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, cw, ch);
  ctx.save();
  if (shake > 0.3) {
    ctx.translate((Math.random() - 0.5) * shake, (Math.random() - 0.5) * shake);
    shake *= Math.pow(0.87, dtF);
  }
  drawBase();
  drawWave();
  drawField();
  drawLens();
  drawHole();
  drawParticles();
  drawTrail();

  if (res.multiHandLandmarks && res.multiHandLandmarks.length) {
    for (let i = 0; i < res.multiHandLandmarks.length; i++) {
      const lms = res.multiHandLandmarks[i];
      const label = res.multiHandedness[i] && res.multiHandedness[i].label;
      if (label === 'Right') {
        const hue = (hueT * 1.5) % 360;
        drawSkeleton(smoothedPts('R', lms), `hsla(${hue}, 100%, 65%, 0.95)`);
        if (fieldOn) {
          const R = Math.min(cw, ch) * FIELD_R_MAX_K;
          ctx.save();
          ctx.strokeStyle = 'rgba(140, 245, 255, 0.35)';
          ctx.setLineDash([6, 8]);
          ctx.lineWidth = 1;
          ctx.beginPath();
          ctx.arc(palm.x, palm.y, R + 10, hueT * 0.02, hueT * 0.02 + Math.PI * 2);
          ctx.stroke();
          ctx.restore();
        }
      } else {
        drawSkeleton(smoothedPts('L', lms), 'rgba(255, 120, 240, 0.9)');
      }
    }
    if (rightLms) drawCountBadge(rightCount, palm.x, palm.y);
  }
  ctx.restore();

  /* вспышка удара */
  if (flashA > 0.01) {
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    ctx.fillStyle = `rgba(255, 250, 240, ${flashA.toFixed(3)})`;
    ctx.fillRect(0, 0, cw, ch);
    ctx.restore();
    flashA *= Math.pow(0.8, dtF);
  }

  /* счётчик FPS */
  fpsFrames++;
  const nowMs = performance.now();
  if (nowMs - fpsLast > 500) {
    const fps = Math.round(fpsFrames * 1000 / (nowMs - fpsLast));
    stFps.querySelector('.lbl').textContent = `${fps} fps`;
    fpsFrames = 0;
    fpsLast = nowMs;
  }

  updateHud();
}

async function loop() {
  if (video.readyState >= 2 && !sending) {
    sending = true;
    try { await hands.send({ image: video }); } catch (e) { /* пропускаем кадр */ }
    sending = false;
  }
  requestAnimationFrame(loop);
}

async function init() {
  statusEl.textContent = 'Загружаю модель распознавания рук…';

  hands = new Hands({
    locateFile: f => `https://cdn.jsdelivr.net/npm/@mediapipe/hands@0.4.1675469240/${f}`,
  });
  hands.setOptions({
    maxNumHands: 2,
    modelComplexity: 1,
    minDetectionConfidence: 0.6,
    minTrackingConfidence: 0.55,
  });
  hands.onResults(onResults);

  statusEl.textContent = 'Запрашиваю камеру…';
  const stream = await navigator.mediaDevices.getUserMedia({
    video: { width: { ideal: 1920 }, height: { ideal: 1080 }, facingMode: 'user' },
    audio: false,
  });
  video.srcObject = stream;
  await new Promise(r => { video.onloadedmetadata = r; });
  await video.play();

  statusEl.textContent = 'Готово! Покажите руку в кадр ✋';
  setTimeout(() => overlay.classList.add('hidden'), 900);

  loop();
}

init().catch(err => {
  console.error(err);
  overlay.querySelector('.ring').style.display = 'none';
  statusEl.innerHTML =
    `<span class="err">Не удалось запустить: ${err.name || ''} ${err.message || err}</span><br><br>` +
    'Разрешите доступ к камере в браузере и обновите страницу.<br>' +
    'Для загрузки модели нужен интернет (CDN MediaPipe).';
});
