'use strict';
/* Import from a screen recording or screenshots of the in-game appraisal.
   1. IVs: read from the three appraisal bars by pixel colour (exact, no OCR).
   2. CP, HP: OCR with an English-only model. Species: OCR of the leader's speech bubble
      (「この〇〇を捕まえた…」, always the species even when nicknamed) with the Japanese model.
   3. The name picks the species; CP and HP pick the level (a one-digit CP misread is corrected and flagged).
   Built for iPhone Safari: one pass over the video, reused canvases, only small crops are kept per Pokémon.
   Everything runs on this device; the video is never uploaded. */

const IMP = { items: [], busy: false, cancel: false, origin: 'normal' };
const SAMPLE_STEP = 0.25;   // seconds of video between analysed frames
const WORK_W = 585;         // analysis width (bars are read at this width)
const HEVC_MSG = 'This browser can\'t decode this video. iPhone screen recordings use HEVC: open this page in Safari (iPhone, iPad or Mac), or use screenshots instead.';
const ASSET = p => new URL(p, document.baseURI).href;
const TESS_LOCAL = location.protocol !== 'file:';   // workers can't load from file://, so use the CDN there
const TESS_CDN = 'https://cdn.jsdelivr.net/npm/tesseract.js@5.1.1/dist/tesseract.min.js';

/* ---------- canvases (reused: iPhone Safari has a hard cap on total canvas memory) ---------- */
const CANVASES = {};
function getCanvas(name, w, h) {
  const c = CANVASES[name] || (CANVASES[name] = document.createElement('canvas'));
  if (c.width !== w) c.width = w;
  if (c.height !== h) c.height = h;
  return c;
}
const ctx2d = c => c.getContext('2d', { willReadFrequently: true });
function releaseCanvases() { for (const c of Object.values(CANVASES)) { c.width = 0; c.height = 0; } }
const freeCanvas = c => { if (c) { c.width = 0; c.height = 0; } };

/* ---------- appraisal bars ---------- */
function barClass(r, g, b) {
  if (r > 215 && g > 125 && g < 185 && b < 110) return 1;                                   // orange fill
  if (r > 190 && g > 85 && g < 140 && b > 90 && b < 150 && r - g > 70) return 1;            // red fill (15)
  if (Math.abs(r - g) < 14 && Math.abs(g - b) < 14 && r > 205 && r < 236) return 2;        // empty (grey)
  return 0;
}
function readBars(img) {
  const { data, width: W, height: H } = img;
  const minLen = Math.floor(W * 0.22), gapTol = Math.max(4, Math.floor(W * 0.015));
  const rows = [];
  for (let y = Math.floor(H * 0.45); y < H; y++) {
    let o = y * W * 4, best = null, run = null, lastX = -1e9;
    for (let x = 0; x < W; x++, o += 4) {
      if (!barClass(data[o], data[o + 1], data[o + 2])) continue;
      if (run && x - lastX <= gapTol) run[1] = x; else run = [x, x];
      lastX = x;
      if (!best || run[1] - run[0] > best[1] - best[0]) best = [run[0], run[1]];
    }
    if (best && best[1] - best[0] >= minLen && best[0] <= W * 0.5) rows.push({ y, x0: best[0], x1: best[1] });
  }
  const bars = [];
  for (const r of rows) {
    const g = bars[bars.length - 1];
    if (g && r.y - g[g.length - 1].y <= 2 && Math.abs(r.x0 - g[g.length - 1].x0) < W * 0.02) g.push(r); else bars.push([r]);
  }
  const good = bars.filter(b => b.length >= Math.max(3, Math.floor(H / 400)));
  for (let i = 0; i + 2 < good.length; i++) {
    const mids = good.slice(i, i + 3).map(b => b[b.length >> 1]);
    const x0s = mids.map(m => m.x0), x1s = mids.map(m => m.x1);
    if (Math.max(...x0s) - Math.min(...x0s) > W * 0.01 || Math.max(...x1s) - Math.min(...x1s) > W * 0.01) continue;
    if (Math.abs((mids[1].y - mids[0].y) - (mids[2].y - mids[1].y)) > H * 0.006) continue;
    const iv = mids.map(m => {
      let last = -1;
      const o = m.y * W * 4;
      for (let x = m.x0; x <= m.x1; x++) { const p = o + x * 4; if (barClass(data[p], data[p + 1], data[p + 2]) === 1) last = x; }
      return last < 0 ? 0 : Math.round(15 * (last - m.x0 + 1) / (m.x1 - m.x0 + 1));
    });
    return { iv, ys: mids.map(m => m.y), x0: mids[0].x0, x1: mids[0].x1 };
  }
  return null;
}
/* coarse colour signature of the top of the screen (CP + Pokémon), to split two Pokémon with identical IVs */
function signature(img) {
  const { data, width: W, height: H } = img, out = [];
  for (let gy = 0; gy < 4; gy++) for (let gx = 0; gx < 6; gx++) {
    let s = 0, n = 0;
    for (let y = Math.floor(H * (0.03 + gy * 0.075)); y < H * (0.03 + (gy + 1) * 0.075); y += 3)
      for (let x = Math.floor(W * gx / 6); x < W * (gx + 1) / 6; x += 3) { const o = (y * W + x) * 4; s += data[o] + data[o + 1] + data[o + 2]; n++; }
    out.push(s / n / 3);
  }
  return out;
}
const sigDist = (a, b) => a.reduce((s, v, i) => s + Math.abs(v - b[i]), 0) / a.length;

/* ---------- crops for OCR ---------- */
/* crop + binarise: pixels matching keep(r,g,b) become black ink on white; optional scale and removal of shapes touching the edge */
function cropBin(src, x, y, w, h, keep, up = 1, clearEdges = false) {
  x = Math.max(0, Math.round(x)); y = Math.max(0, Math.round(y));
  w = Math.min(src.width - x, Math.round(w)); h = Math.min(src.height - y, Math.round(h));
  if (w <= 0 || h <= 0) return null;
  const pad = keep ? 16 : 0;
  const c = document.createElement('canvas');
  c.width = Math.round(w * up) + pad * 2; c.height = Math.round(h * up) + pad * 2;
  const ctx = ctx2d(c);
  ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, c.width, c.height);
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(src, x, y, w, h, pad, pad, c.width - pad * 2, c.height - pad * 2);
  if (!keep) return c;
  const img = ctx.getImageData(0, 0, c.width, c.height), d = img.data, CW = c.width, CH = c.height;
  const ink = new Uint8Array(CW * CH);
  for (let y2 = pad; y2 < CH - pad; y2++) for (let x2 = pad; x2 < CW - pad; x2++) {
    const i = (y2 * CW + x2) * 4; if (keep(d[i], d[i + 1], d[i + 2])) ink[y2 * CW + x2] = 1;
  }
  if (clearEdges) {  // e.g. the white corner circle next to the CP
    const stack = [];
    for (let x2 = pad; x2 < CW - pad; x2++) stack.push(pad * CW + x2, (CH - pad - 1) * CW + x2);
    for (let y2 = pad; y2 < CH - pad; y2++) stack.push(y2 * CW + pad, y2 * CW + CW - pad - 1);
    while (stack.length) {
      const k = stack.pop(); if (!ink[k]) continue; ink[k] = 0;
      const kx = k % CW, ky = (k / CW) | 0;
      if (kx > 0) stack.push(k - 1); if (kx < CW - 1) stack.push(k + 1); if (ky > 0) stack.push(k - CW); if (ky < CH - 1) stack.push(k + CW);
    }
  }
  for (let k = 0; k < ink.length; k++) { const v = ink[k] ? 0 : 255; d[k * 4] = d[k * 4 + 1] = d[k * 4 + 2] = v; }
  ctx.putImageData(img, 0, 0);
  return c;
}
const WHITE_TXT = (r, g, b) => Math.min(r, g, b) > 205 && Math.max(r, g, b) - Math.min(r, g, b) < 45;
const DARK_TXT = (r, g, b) => r + g + b < 420;
/* the mint-green HP bar under the name: first row (top-down) with a long green run */
function findHpBar(full, yMax) {
  const W = full.width, y0 = Math.floor(full.height * 0.25), y1 = Math.floor(yMax);
  if (y1 <= y0) return null;
  const { data } = ctx2d(full).getImageData(0, y0, W, y1 - y0);
  for (let yy = 0; yy < y1 - y0; yy += 2) {
    let run = 0, best = 0;
    for (let x = 0; x < W; x++) {
      const o = (yy * W + x) * 4, r = data[o], g = data[o + 1], b = data[o + 2];
      if (g > 190 && r < 150 && b > 120 && b < 200 && g - r > 70) { run++; if (run > best) best = run; } else run = 0;
    }
    if (best > W * 0.3) return y0 + yy;
  }
  return null;
}
/* grab what OCR needs from one settled frame, then forget the frame */
function capture(src, W, H, bars, k, t) {
  const full = getCanvas('full', W, H);
  ctx2d(full).drawImage(src, 0, 0, W, H);
  const ys = bars.ys.map(y => y * k), gap = ys[1] - ys[0];
  const hb = findHpBar(full, ys[0]);
  const thumbSrc = cropBin(full, 0, H * 0.03, W, H * 0.33, null);
  const th = document.createElement('canvas'); th.width = 160; th.height = Math.round(160 * thumbSrc.height / thumbSrc.width);
  th.getContext('2d').drawImage(thumbSrc, 0, 0, th.width, th.height);
  freeCanvas(thumbSrc);
  // keep crops as small PNGs (black-and-white text compresses to a few KB) so long recordings stay within iPhone memory
  const png = c => { if (!c) return null; const u = c.toDataURL('image/png'); freeCanvas(c); return u; };
  const out = {
    t, iv: bars.iv.slice(),
    cp: png(cropBin(full, W * 0.15, H * 0.04, W * 0.6, H * 0.065, WHITE_TXT, 0.5, true)),
    hp: hb != null ? png(cropBin(full, W * 0.25, hb + gap * 0.12, W * 0.5, gap * 0.55, DARK_TXT, 1.5)) : null,
    bubble: png(cropBin(full, W * 0.03, ys[2] + gap * 1.35, W * 0.94, gap * 2.1, DARK_TXT)),
    thumb: th.toDataURL('image/jpeg', 0.7),
  };
  freeCanvas(th);
  return out;
}

/* ---------- reading a video in one pass ---------- */
/* consecutive identical bar readings = one Pokémon; the 2nd identical reading means the bar animation has settled */
function segmenter(onCap) {
  let cur = null, count = 0;
  return {
    get count() { return count; },
    push(s) {
      if (cur && s.key && s.key === cur.key && sigDist(s.sig, cur.sig) < 28) {
        cur.n++; cur.sig = s.sig;
        if (cur.n === 2) cur.cap = s.grab();
        return;
      }
      this.flush();
      cur = s.key ? { key: s.key, n: 1, sig: s.sig } : null;
    },
    flush() { if (cur && cur.cap) { count++; onCap(cur.cap); } cur = null; },
  };
}
async function openVideo(file) {
  const v = document.createElement('video');
  v.muted = true; v.defaultMuted = true; v.playsInline = true; v.preload = 'auto';
  v.setAttribute('muted', ''); v.setAttribute('playsinline', ''); v.setAttribute('webkit-playsinline', '');
  // iPhone Safari only decodes videos that are in the page
  v.style.cssText = 'position:fixed;left:0;top:0;width:2px;height:2px;opacity:0.01;pointer-events:none;z-index:-1';
  document.body.appendChild(v);
  v.src = URL.createObjectURL(file);
  try {
    await new Promise((res, rej) => {
      const to = setTimeout(() => rej(new Error('The video took too long to open. Try a shorter recording.')), 30000);
      v.addEventListener('loadedmetadata', () => { clearTimeout(to); res(); }, { once: true });
      v.addEventListener('error', () => { clearTimeout(to); rej(new Error(HEVC_MSG)); }, { once: true });
    });
    if (!v.videoWidth || !v.videoHeight) throw new Error(HEVC_MSG);
  } catch (e) { closeVideo(v); throw e; }
  return v;
}
function closeVideo(v) {
  try { v.pause(); } catch { /* already gone */ }
  URL.revokeObjectURL(v.src); v.removeAttribute('src'); v.load(); v.remove();
}
function seek(v, t) {
  return new Promise((res, rej) => {
    const done = () => { clearTimeout(to); v.removeEventListener('seeked', done); res(); };
    const to = setTimeout(() => { v.removeEventListener('seeked', done); rej(new Error('The video stopped responding while seeking.')); }, 10000);
    v.addEventListener('seeked', done); v.currentTime = t;
  });
}
async function walkBySeeking(v, sample) {
  try { await v.play(); v.pause(); } catch { /* iPhone: a brief play lets seeking decode frames; harmless elsewhere */ }
  for (let t = 0; t < v.duration; t += SAMPLE_STEP) {
    if (IMP.cancel) return;
    await seek(v, t);
    sample(t);
  }
}
/* play at 2× and analyse frames as they are shown (much faster than seeking on iPhone) */
function walkByPlaying(v, sample) {
  return new Promise((res, rej) => {
    let next = 0, last = -1, watchdog = null, finished = false, samples = 0;
    const finish = err => {
      if (finished) return; finished = true;
      clearInterval(watchdog); v.pause(); v.removeEventListener('ended', onEnd);
      err ? rej(err) : res();
    };
    // if the browser delivered far fewer frames than expected (it may skip painting a hidden video), redo by seeking
    const onEnd = () => finish(!IMP.cancel && samples < v.duration / SAMPLE_STEP * 0.5 ? new Error('too few frames') : null);
    const cb = (_now, meta) => {
      if (finished) return;
      if (IMP.cancel) return finish();
      const t = meta.mediaTime;
      if (t >= next) { sample(t); samples++; next = t + SAMPLE_STEP; }
      v.requestVideoFrameCallback(cb);
    };
    v.addEventListener('ended', onEnd);
    v.requestVideoFrameCallback(cb);
    v.playbackRate = 2;
    v.play().catch(e => finish(e));
    watchdog = setInterval(() => {   // let the caller fall back to seeking if playback froze or no frames arrive
      if (!v.paused && v.currentTime === last) finish(new Error('playback stalled'));
      if (!samples && v.currentTime > 1.5) finish(new Error('no frames delivered'));
      last = v.currentTime;
    }, 1000);
  });
}
/* onCap(cap) is called as soon as each Pokémon's frame is captured, so text reading can run alongside */
async function scanVideo(file, progress, onCap) {
  const v = await openVideo(file);
  try {
    const W = v.videoWidth, H = v.videoHeight, h = Math.round(H * WORK_W / W), k = W / WORK_W;
    const work = getCanvas('work', WORK_W, h), wctx = ctx2d(work);
    let seen = 0;
    const run = async walk => {
      const seg = segmenter(cap => { if (cap.t >= seen - 1e-6) { seen = cap.t; onCap(cap); } });
      const sample = t => {
        wctx.drawImage(v, 0, 0, WORK_W, h);
        const img = wctx.getImageData(0, 0, WORK_W, h);
        const bars = readBars(img);
        seg.push({ key: bars ? bars.iv.join('/') : null, sig: signature(img), grab: () => capture(v, W, H, bars, k, t) });
        progress(`Reading the video · ${Math.min(99, Math.round(t / v.duration * 100))}% · ${seg.count} Pokémon found`, t / v.duration);
      };
      await walk(v, sample);
      seg.flush();
    };
    const canPlayWalk = 'requestVideoFrameCallback' in HTMLVideoElement.prototype && !window.__IMPORT_FORCE_SEEK;
    if (canPlayWalk) {
      try { await run(walkByPlaying); return; } catch { await seek(v, 0); }   // fall back to seeking (frames already sent are skipped)
    }
    await run(walkBySeeking);
  } finally { closeVideo(v); }
}
async function scanImage(file) {
  const im = new Image(); im.src = URL.createObjectURL(file);
  try { await im.decode(); } catch { URL.revokeObjectURL(im.src); return []; }
  const W = im.naturalWidth, H = im.naturalHeight, h = Math.round(H * WORK_W / W);
  const work = getCanvas('work', WORK_W, h), wctx = ctx2d(work);
  wctx.drawImage(im, 0, 0, WORK_W, h);
  const bars = readBars(wctx.getImageData(0, 0, WORK_W, h));
  const caps = bars ? [capture(im, W, H, bars, W / WORK_W, 0)] : [];
  URL.revokeObjectURL(im.src);
  return caps;
}

/* ---------- OCR (Tesseract.js, served from this site so it also works offline) ---------- */
let tessWorkers = null;
function loadScript(src) {
  return new Promise((res, rej) => { const s = document.createElement('script'); s.src = src; s.onload = res; s.onerror = rej; document.head.appendChild(s); });
}
async function ocrWorkers(progress) {
  if (tessWorkers) return tessWorkers;
  progress('Loading the text reader (first time only, about 10 MB)…');
  let opts = {};
  if (TESS_LOCAL) {
    try {
      if (!window.Tesseract) await loadScript(ASSET('vendor/tesseract/tesseract.min.js'));
      opts = { workerPath: ASSET('vendor/tesseract/worker.min.js'), corePath: ASSET('vendor/tesseract/core'), langPath: ASSET('vendor/tesseract/lang') };
    } catch { /* not bundled: use the CDN */ }
  }
  if (!window.Tesseract) {
    try { await loadScript(TESS_CDN); } catch { throw new Error('Could not load the text reader. Connect to the internet once and try again.'); }
  }
  // digits read far better with the English-only model; the Japanese model only reads the species name
  const [eng, jpn] = await Promise.all([Tesseract.createWorker('eng', 1, opts), Tesseract.createWorker('jpn', 1, opts)]);
  tessWorkers = { eng, jpn };
  return tessWorkers;
}
async function ocr(worker, image, whitelist, psm) {
  if (!image) return '';
  await worker.setParameters({ tessedit_char_whitelist: whitelist || '', tessedit_pageseg_mode: String(psm) });
  const { data } = await worker.recognize(image);
  return data.text || '';
}
async function readText(w, cap) {
  const cpTxt = await ocr(w.eng, cap.cp, 'CP0123456789', 7);
  const cpM = cpTxt.replace(/[^0-9CP]/g, '').match(/(\d{2,5})/);
  const hpTxt = await ocr(w.eng, cap.hp, '0123456789/HP ', 7);
  const hpM = hpTxt.match(/(\d+)\s*H\s*P/i);     // max HP = the number right before "HP" (the slash is often misread)
  const nameTxt = (await ocr(w.jpn, cap.bubble, '', 6)).replace(/\s+/g, '');
  let name = (nameTxt.match(/この(.{1,8}?)(?:を捕|を|は\d|は)/) || [])[1] || '', enTxt = '';
  if (!name) {   // English game: "This Torchic was caught on …"
    enTxt = (await ocr(w.eng, cap.bubble, '', 6)).replace(/\s+/g, ' ');
    name = ((enTxt.match(/This (.{2,24}?) (?:was|is) /i) || [])[1] || '').trim();
  }
  return { cp: cpM ? +cpM[1] : null, hp: hpM ? +hpM[1] : null, name, raw: { cpTxt, hpTxt, nameTxt, enTxt } };
}

/* ---------- species + level solver ---------- */
function lev(a, b) {
  const m = a.length, n = b.length; if (!m) return n; if (!n) return m;
  let prev = Array.from({ length: n + 1 }, (_, j) => j);
  for (let i = 1; i <= m; i++) {
    const cur = [i];
    for (let j = 1; j <= n; j++) cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] === b[j - 1] ? 0 : 1));
    prev = cur;
  }
  return prev[n];
}
const simOne = (a, b) => !a || !b ? 0 : 1 - lev(a, b) / Math.max(a.length, b.length);
const enBase = p => p.name.replace(/\s*\(.*\)\s*/g, '').toLowerCase();
/* the read name against the Japanese species name, or the English one for an English game */
const nameSim = (ocrName, p) => !ocrName ? 0 : /[A-Za-z]/.test(ocrName) ? simOne(ocrName.toLowerCase(), enBase(p)) : simOne(ocrName, p.ja);
const hpAt = (p, iv, i) => Math.max(10, Math.floor((p.hp + iv[2]) * CPM[i]));
const SOLVE_POOL = D.pokemon.filter(p => !p.mega && p.released !== false);
/* The name picks the species; CP and HP pick the level. Each level is scored by how many CP digits
   differ from what was read, plus a penalty if HP disagrees. */
function solve(iv, cp, hp, name) {
  const maxI = li(51);
  let pool = SOLVE_POOL, byName = false;
  if (name) {
    const sims = SOLVE_POOL.map(p => nameSim(name, p));
    const best = Math.max(...sims);
    if (best >= 0.7) { pool = SOLVE_POOL.filter((p, k) => sims[k] >= best - 1e-9); byName = true; }
  }
  if (!byName && !cp) return { cands: [], status: 'nomatch' };
  const cands = [];
  for (const p of pool) {
    let bestL = null;
    for (let i = 0; i <= maxI; i++) {
      const c = cpAt(p, iv, i), hpOk = !hp || hpAt(p, iv, i) === hp;
      const score = (cp ? lev(String(c), String(cp)) : 0) + (hpOk ? 0 : 1.5);
      if (!bestL || score < bestL.score || (score === bestL.score && cp && Math.abs(c - cp) < Math.abs(cpAt(p, iv, bestL.i) - cp))) bestL = { i, score };
    }
    if (!byName && bestL.score > 0) continue;   // without a name, only exact CP (+HP) matches count
    cands.push({ p, lvIdx: bestL.i, score: bestL.score, sim: nameSim(name, p) });
  }
  const plain = c => /\(/.test(c.p.name) ? 1 : 0;
  cands.sort((a, b) => a.score - b.score || b.sim - a.sim || plain(a) - plain(b) || a.p.dex - b.p.dex);
  const top = cands[0];
  let status = 'nomatch';
  if (top && top.score === 0) status = byName || new Set(cands.filter(c => c.score === 0).map(c => c.p.dex)).size === 1 ? 'ok' : 'check';
  else if (top && top.score <= 1.5) status = 'check';
  if (top && top.score > 2.5) top.lvIdx = null;
  return { cands: cands.slice(0, 8), status };
}
function levelFor(p, iv, cp) {
  if (!p || !cp) return null;
  for (let i = 0; i <= li(51); i++) if (cpAt(p, iv, i) === cp) return i;
  return null;
}
/* userPicked: the species was chosen by hand, so keep it even if the numbers point elsewhere */
function recompute(it, userPicked) {
  const r = solve(it.iv, it.cp, it.hp, it.ocrName);
  const hit = r.cands.find(c => c.p.id === it.id);
  if (userPicked && it.id) {
    it.cands = hit ? r.cands : [{ p: POKE.get(it.id), lvIdx: null, sim: 0 }, ...r.cands];
    it.lvIdx = levelFor(POKE.get(it.id), it.iv, it.cp);
    it.status = it.lvIdx != null ? 'ok' : 'nomatch';
    return;
  }
  const c = hit || r.cands[0];
  it.cands = r.cands; it.status = r.status;
  it.id = c ? c.p.id : it.id;
  it.lvIdx = c ? (c.lvIdx ?? levelFor(c.p, it.iv, it.cp)) : null;
}

/* ---------- UI ---------- */
const defaultOrigin = () => IMP.origin === 'mixed' ? 'normal' : IMP.origin;
/* same species, IVs and level already saved for this trainer (e.g. the same Pokémon recorded twice) */
const inBox = it => it.id && it.lvIdx != null && box().some(e => e.id === it.id && e.lvIdx === it.lvIdx && e.iv.join() === it.iv.join());
function itemFromCap(cap, txt) {
  const iv = cap.iv.slice();
  const r = solve(iv, txt.cp, txt.hp, txt.name);
  const c = r.cands[0];
  const it = { uid: Math.random().toString(36).slice(2), thumb: cap.thumb, iv, cp: txt.cp, hp: txt.hp, ocrName: txt.name, raw: txt.raw,
    cands: r.cands, status: r.status, id: c ? c.p.id : null, lvIdx: c ? c.lvIdx : null, origin: defaultOrigin(),
    include: !!(c && c.lvIdx != null && (r.status === 'ok' || (r.status === 'check' && c.score <= 1))) };
  // the same Pokémon twice in one recording, or already in the box: leave it unticked
  it.dupe = inBox(it) || IMP.items.some(o => o.id === it.id && o.lvIdx === it.lvIdx && o.iv.join() === iv.join());
  if (it.dupe) it.include = false;
  return it;
}
const STATUS = { ok: ['Matched', 'top'], check: ['Check', 'mid'], nomatch: ['No CP match', 'bad'] };
const ORIGINS = [['normal', 'Normal'], ['shadow', 'Shadow'], ['purified', 'Purified']];
function renderImport() {
  const out = $('#import-out');
  $('#import-target').textContent = boxState.current;
  setSeg($('#import-origin'), IMP.origin);
  $('#import-cancel').hidden = !IMP.busy;
  $('.progress-row').hidden = !IMP.busy;
  $('#import-file').disabled = IMP.busy;
  $('#import-drop').classList.toggle('busy', IMP.busy);
  if (!IMP.items.length) {
    out.innerHTML = IMP.busy ? '' : `<div class="panel empty"><strong>Nothing imported yet</strong><span>Choose a screen recording or screenshots of the appraisal screen above.</span></div>`;
    updateAddBtn(); return;
  }
  out.innerHTML = `<div class="imp-grid">${IMP.items.map(it => {
    const p = it.id ? POKE.get(it.id) : null;
    const st = it.lvIdx == null ? STATUS.nomatch : STATUS[it.status] || STATUS.ok;
    const opts = it.cands.map(c => `<option value="${esc(c.p.id)}" ${c.p.id === it.id ? 'selected' : ''}>${esc(c.p.name)}${c.p.ja ? ` · ${esc(c.p.ja)}` : ''}</option>`).join('');
    const fitCp = p && it.lvIdx != null ? cpAt(p, it.iv, it.lvIdx) : null;
    return `<article class="imp-card${it.include ? '' : ' off'}" data-uid="${it.uid}">
      <img class="imp-thumb" src="${it.thumb}" alt="">
      <div class="imp-body">
        <div class="imp-head">${p ? pic(p) : ''}<label class="toggle"><input type="checkbox" data-f="include" ${it.include ? 'checked' : ''}> Add</label><span class="pill ${it.dupe ? '' : st[1]}">${it.dupe ? 'Already in box' : st[0]}</span></div>
        <label class="label" for="sp-${it.uid}">Species</label>
        <select id="sp-${it.uid}" data-f="id">${opts || '<option value="">(not found)</option>'}<option value="__other">Other…</option></select>
        <div class="imp-nums">
          ${['A', 'D', 'H'].map((n, j) => `<label>${n}<input type="number" min="0" max="15" inputmode="numeric" data-f="iv${j}" value="${it.iv[j]}"></label>`).join('')}
          <label>CP<input type="number" min="10" inputmode="numeric" data-f="cp" value="${it.cp ?? ''}"></label>
        </div>
        <div class="imp-meta">${it.lvIdx != null ? `Lv ${LV[it.lvIdx]}${fitCp != null && it.cp && fitCp !== it.cp ? ` · <b>CP ${fitCp}</b> (read ${it.cp})` : ''}` : 'Level unknown: check CP and IVs'}${it.hp ? ` · HP ${it.hp}` : ''}${it.ocrName ? ` · 「${esc(it.ocrName)}」` : ''}</div>
        <div class="seg sm" data-f="origin" role="radiogroup" aria-label="Origin">${ORIGINS.map(([o, n]) => `<button type="button" data-v="${o}" role="radio" aria-checked="${it.origin === o}">${n}</button>`).join('')}</div>
      </div></article>`;
  }).join('')}</div>`;
  updateAddBtn();
}
function updateAddBtn() {
  const n = IMP.items.filter(it => it.include && it.id && it.lvIdx != null).length;
  const b = $('#import-add'); b.disabled = !n || IMP.busy; b.textContent = n ? `Add ${n} to ${boxState.current}'s box` : 'Add to box';
}
async function runImport(files) {
  if (IMP.busy || !files.length) return;
  IMP.busy = true; IMP.cancel = false; IMP.items = []; renderImport();
  let wakeLock = null;   // keep the iPhone screen on during a long import (the page pauses if it locks)
  try { wakeLock = await navigator.wakeLock?.request('screen'); } catch { /* not supported or refused */ }
  const status = $('#import-status'), bar = $('#import-progress');
  const progress = (msg, frac) => { status.textContent = msg; if (frac != null) { bar.hidden = false; bar.value = frac; } };
  try {
    // start loading the text reader now; it runs in background workers while the video is scanned
    let ocrError = null;
    const workersP = ocrWorkers(() => { }).catch(e => { ocrError = e; return null; });
    let found = 0, scanning = true, chain = Promise.resolve();
    const report = () => { if (!scanning) progress(`Reading CP and names · ${IMP.items.length} of ${found}`, IMP.items.length / Math.max(1, found)); };
    const onCap = cap => {
      found++;
      chain = chain.then(async () => {
        if (IMP.cancel) return;
        const w = await workersP;
        const txt = w ? await readText(w, cap) : { cp: null, hp: null, name: '', raw: {} };
        cap.cp = cap.hp = cap.bubble = null;
        IMP.items.push(itemFromCap(cap, txt));
        renderImport(); report();
      });
    };
    for (const f of files) {
      if (IMP.cancel) break;
      progress(`Opening ${f.name}…`, 0);
      if (f.type.startsWith('video/') || /\.(mp4|mov|m4v)$/i.test(f.name)) await scanVideo(f, progress, onCap);
      else if (f.type.startsWith('image/') || /\.(png|jpe?g|heic)$/i.test(f.name)) (await scanImage(f)).forEach(onCap);
    }
    scanning = false; releaseCanvases(); report();
    if (!found && !IMP.cancel) { progress('No appraisal screen found. Open a Pokémon, tap Appraise, then record while you swipe through your Pokémon.'); return; }
    await chain;
    if (ocrError) { progress(`${ocrError.message} IVs were still read; enter CP and species by hand.`); return; }
    const ok = IMP.items.filter(it => it.include).length, n = IMP.items.length, dup = IMP.items.filter(it => it.dupe).length;
    progress(IMP.cancel ? `Stopped after ${n} Pokémon.` : `Found ${n} Pokémon · ${ok} ready${dup ? ` · ${dup} already in the box` : ''}${n - ok - dup > 0 ? ` · ${n - ok - dup} need a look` : ''}. Check them, then add them to the box.`, 1);
  } catch (e) {
    progress(e.message || String(e));
  } finally {
    IMP.busy = false; releaseCanvases(); bar.hidden = true; renderImport();
    try { await wakeLock?.release(); } catch { /* already released */ }
  }
}
function bindImport() {
  const input = $('#import-file'), drop = $('#import-drop');
  input.addEventListener('change', () => { const fs = [...input.files]; input.value = ''; runImport(fs); });
  drop.addEventListener('dragover', e => { e.preventDefault(); drop.classList.add('over'); });
  drop.addEventListener('dragleave', () => drop.classList.remove('over'));
  drop.addEventListener('drop', e => { e.preventDefault(); drop.classList.remove('over'); runImport([...e.dataTransfer.files]); });
  $('#import-cancel').addEventListener('click', () => { IMP.cancel = true; $('#import-status').textContent = 'Stopping…'; });
  bindSeg($('#import-origin'), v => {
    IMP.origin = v;
    if (v !== 'mixed') for (const it of IMP.items) it.origin = v;
    renderImport();
  });
  const out = $('#import-out');
  const itemOf = el => IMP.items.find(it => it.uid === el.closest('[data-uid]')?.dataset.uid);
  out.addEventListener('change', e => {
    const it = itemOf(e.target); if (!it) return;
    const f = e.target.dataset.f;
    if (f === 'include') { it.include = e.target.checked; renderImport(); return; }
    if (f === 'id') {
      if (e.target.value === '__other') {
        $('#import-other-uid').value = it.uid; $('#import-other').hidden = false; $('#import-other-input').focus(); return;
      }
      it.id = e.target.value;
    }
    if (f && f.startsWith('iv')) it.iv[+f.slice(2)] = Math.max(0, Math.min(15, +e.target.value || 0));
    if (f === 'cp') it.cp = +e.target.value || null;
    recompute(it, f === 'id'); it.dupe = false; it.include = it.lvIdx != null && !!it.id; renderImport();
  });
  out.addEventListener('click', e => {
    const b = e.target.closest('[data-f="origin"] button'); if (!b) return;
    const it = itemOf(b); it.origin = b.dataset.v;
    if (IMP.origin !== 'mixed' && it.origin !== IMP.origin) IMP.origin = 'mixed';
    renderImport();
  });
  $('#import-add').addEventListener('click', () => {
    const list = IMP.items.filter(it => it.include && it.id && it.lvIdx != null);
    for (const it of list) box().push({ uid: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), id: it.id, origin: it.origin, iv: it.iv.slice(), lvIdx: it.lvIdx, fast: null, charged: null, added: Date.now() });
    saveBox(false, list.length);
    IMP.items = IMP.items.filter(it => !list.includes(it)); renderImport();
    toast(`Added ${list.length} Pokémon to ${boxState.current}'s box`);
  });
  combo($('[data-combo="import"]'), { megas: false, getId: () => '', onPick: p => {
    const it = IMP.items.find(x => x.uid === $('#import-other-uid').value); if (!it) return;
    it.id = p.id; recompute(it, true); it.include = it.lvIdx != null;
    $('#import-other').hidden = true; renderImport();
  } });
  $('#import-other-close').addEventListener('click', () => { $('#import-other').hidden = true; renderImport(); });
}
bindImport();
window.renderImport = renderImport;
