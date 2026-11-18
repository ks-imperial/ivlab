'use strict';
/* IV Lab — all calculations run in the browser from window.PKGO_DATA (built by tools/build_data.py). */

const D = window.PKGO_DATA;
const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmt = (x, d = 1) => Number.isFinite(x) ? x.toFixed(d) : '—';
const fmtInt = x => Number.isFinite(x) ? Math.round(x).toLocaleString('en-US') : '—';

/* ================= core game math ================= */
const LV = D.cpm.map(r => r[0]);
const CPM = D.cpm.map(r => r[1]);
const DUST = D.cpm.map(r => r[2]);
const li = lv => Math.round((lv - 1) * 2);
const REF_LV = D.meta.ref_level;
const DOWNTIME = D.meta.downtime;
const TYPES = ['normal', 'fire', 'water', 'electric', 'grass', 'ice', 'fighting', 'poison', 'ground', 'flying', 'psychic', 'bug', 'rock', 'ghost', 'dragon', 'dark', 'steel', 'fairy'];

const POKE = new Map(D.pokemon.map(p => [p.id, p]));
const MOVES = new Map();
for (const r of D.moves) {
  const m = { id: r[0], shadow: !!r[1], fast: r[2], fastType: r[3], fastStar: !!r[4], charged: r[5], chargedType: r[6], chargedStar: !!r[7], dps: r[8], tdo: r[9], edps: r[10], surv: r[11], er: r[12] };
  if (!MOVES.has(m.id)) MOVES.set(m.id, []);
  MOVES.get(m.id).push(m);
}

function cpAt(p, iv, i) {
  const m = CPM[i];
  return Math.max(10, Math.floor((p.atk + iv[0]) * Math.sqrt(p.def + iv[1]) * Math.sqrt(p.hp + iv[2]) * m * m / 10));
}
function statsAt(p, iv, i) {
  const m = CPM[i];
  return { a: (p.atk + iv[0]) * m, d: (p.def + iv[1]) * m, h: Math.max(10, Math.floor((p.hp + iv[2]) * m)) };
}
/* highest level index with CP <= cap (binary search; CP is monotonic in level). -1 if even Lv1 is over. */
function maxIdxUnder(p, iv, cap, maxLv) {
  let hi = li(maxLv);
  if (!Number.isFinite(cap)) return hi;
  if (cpAt(p, iv, 0) > cap) return -1;
  let lo = 0;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (cpAt(p, iv, mid) <= cap) lo = mid; else hi = mid - 1; }
  return lo;
}
function dustCost(fromIdx, toIdx, origin) {
  let s = 0;
  for (let i = fromIdx; i < toIdx; i++) s += DUST[i];
  const mult = origin === 'shadow' ? 1.2 : origin === 'purified' ? 0.9 : 1;
  return Math.round(s * mult);
}

const LEAGUES = [
  { key: 'little', name: 'Little Cup', cap: 500 },
  { key: 'great', name: 'Great League', cap: 1500 },
  { key: 'ultra', name: 'Ultra League', cap: 2500 },
  { key: 'master', name: 'Master League', cap: Infinity },
];
const leagueMaxLv = L => Number.isFinite(L.cap) ? settings.lvCapped : settings.lvMaster;

/* Full 4096-IV table for one species and league.
   % = (SP - worst SP) / (rank-1 SP - worst SP): the worst combination is 0%, rank 1 is 100%.
   Ties share a rank (standard competition ranking). */
const tableCache = new Map();
function leagueTable(p, L) {
  const maxLv = leagueMaxLv(L);
  const key = `${p.id}|${L.key}|${maxLv}`;
  if (tableCache.has(key)) return tableCache.get(key);
  const n = 4096, sp = new Float64Array(n), lvI = new Int16Array(n), cps = new Int32Array(n);
  let min = Infinity, max = -Infinity, eligible = 0;
  for (let a = 0; a < 16; a++) for (let d = 0; d < 16; d++) for (let h = 0; h < 16; h++) {
    const k = a * 256 + d * 16 + h, iv = [a, d, h];
    const i = maxIdxUnder(p, iv, L.cap, maxLv);
    lvI[k] = i;
    if (i < 0) { sp[k] = -1; continue; }
    const s = statsAt(p, iv, i);
    sp[k] = s.a * s.d * s.h; cps[k] = cpAt(p, iv, i);
    eligible++;
    if (sp[k] < min) min = sp[k];
    if (sp[k] > max) max = sp[k];
  }
  const order = Array.from({ length: n }, (_, k) => k).filter(k => sp[k] >= 0).sort((x, y) => sp[y] - sp[x] || cps[y] - cps[x] || y - x);
  const rank = new Int16Array(n);
  order.forEach((k, pos) => {
    const prev = order[pos - 1];
    rank[k] = pos > 0 && Math.abs(sp[k] - sp[prev]) <= 1e-9 * sp[k] ? rank[prev] : pos + 1;
  });
  const t = { p, L, maxLv, sp, lvI, cps, order, rank, min, max, eligible };
  tableCache.set(key, t);
  return t;
}
const ivKey = iv => iv[0] * 256 + iv[1] * 16 + iv[2];
const pctOf = (t, k) => t.sp[k] < 0 ? NaN : (t.max === t.min ? 100 : (t.sp[k] - t.min) / (t.max - t.min) * 100);
const ivOf = k => [k >> 8, (k >> 4) & 15, k & 15];

/* Raid: Pokébase numbers are for Lv40 15/15/15. DPS scales with ATK, survival time with DEF×HP. */
function raidScale(p, iv, lvIdx) {
  const r = statsAt(p, [15, 15, 15], li(REF_LV)), s = statsAt(p, iv, lvIdx);
  return { ra: s.a / r.a, rs: (s.d * s.h) / (r.d * r.h) };
}
function scaled(m, sc) {
  const dps = m.dps * sc.ra, surv = m.surv * sc.rs;
  return { dps, edps: dps * surv / (surv + DOWNTIME), er: m.er * sc.ra * Math.pow(sc.rs, 0.25), tdo: dps * surv };
}
function movesFor(p, origin) {
  const all = MOVES.get(p.id) || [];
  if (origin === 'shadow') {
    const sh = all.filter(m => m.shadow);
    if (sh.length) return sh;
  }
  return all.filter(m => !m.shadow && (origin === 'purified' || m.charged !== 'Return'));
}
/* Lv40 15/15/15 = the CSV's own numbers; LvMax (50) 15/15/15 shown faded next to them. */
function refValues(p, m) {
  const hi = scaled(m, raidScale(p, [15, 15, 15], li(settings.lvMaster)));
  return { edps: m.edps, er: m.er, dps: m.dps, tdo: m.tdo, edpsHi: hi.edps, erHi: hi.er };
}
const refCell = (lo, hi) => `<span class="now">${fmt(lo, 2)}</span> <span class="later">(${fmt(hi, 2)})</span>`;
const passesRaidBar = m => m.edps >= settings.minEdps || m.er >= settings.minEr;

/* PokeAPI sprites by id; small pixel sprite for lists, official artwork for cards. */
const IMG_BASE = 'https://raw.githubusercontent.com/PokeAPI/sprites/master/sprites/pokemon/';
function pic(p, kind = 'sprite') {
  const src = !p.img ? '' : kind === 'art' ? `${IMG_BASE}other/official-artwork/${p.img}.png` : `${IMG_BASE}${p.img}.png`;
  const t = esc(p.types[0] || 'normal');
  return src ? `<img class="pic ${kind}" src="${src}" alt="" loading="lazy" decoding="async" data-dex="${p.dex}" data-t="${t}">`
    : `<span class="pic ${kind} pic-fallback" style="--t:var(--t-${t})">${p.dex}</span>`;
}
document.addEventListener('error', e => {
  const img = e.target;
  if (!(img instanceof HTMLImageElement) || !img.classList.contains('pic')) return;
  const s = document.createElement('span');
  s.className = img.className + ' pic-fallback'; s.style.setProperty('--t', `var(--t-${img.dataset.t})`); s.textContent = img.dataset.dex;
  img.replaceWith(s);
}, true);

const metricOf = (v) => settings.metric === 'er' ? v.er : v.edps;
const metricName = () => settings.metric === 'er' ? 'ER' : 'eDPS';
const moveLabel = (name, star) => `${esc(name)}${star ? '<span class="star">*</span>' : ''}`;
const typeChip = (t, sm) => `<span class="type${sm ? ' sm' : ''}" style="--t:var(--t-${esc(t)})">${esc(t)}</span>`;

/* Evolution line from p onwards (+ megas of those species). */
function evoLine(p) {
  const out = [p], seen = new Set([p.id]), q = [p];
  while (q.length) {
    const x = q.shift();
    for (const e of x.evolutions || []) {
      const y = POKE.get(e);
      if (y && !seen.has(y.id) && !y.mega) { seen.add(y.id); out.push(y); q.push(y); }
    }
  }
  const dexes = new Set(out.map(x => x.dex));
  for (const m of D.pokemon) {
    if (m.mega && !seen.has(m.id) && dexes.has(m.dex) && m.family === p.family && (MOVES.get(m.id) || []).length) { seen.add(m.id); out.push(m); }
  }
  return out;
}

/* ================= state & storage ================= */
const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v == null ? d : JSON.parse(v); } catch { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch { /* storage unavailable: keep in memory */ } },
};
/* ivRaid / ivRaidShadow: Master League IV % a box Pokémon needs for a full raid label; ivPvp: league % for a PvP label */
const settings = Object.assign({ lvCapped: 51, lvMaster: 50, metric: 'edps', minEdps: 11, minEr: 34, ivRaid: 90, ivRaidShadow: 80, ivPvp: 90, lvRaid: 40 }, store.get('ivlab.settings', {}));
const boxState = Object.assign({ users: { K: [], M: [], T: [] }, current: 'K' }, store.get('ivlab.box', {}));
if (!boxState.users[boxState.current]) boxState.current = Object.keys(boxState.users)[0];
const saveSettings = () => store.set('ivlab.settings', settings);
/* quiet: not a change to the Pokémon (switching trainer, recording a backup); n: how many Pokémon changed */
const saveBox = (quiet, n = 1) => {
  if (!quiet) boxState.changesSinceBackup = (boxState.changesSinceBackup || 0) + n;
  store.set('ivlab.box', boxState); renderBoxCount();
};
const box = () => boxState.users[boxState.current];

const check = Object.assign({ id: 'charizard', origin: 'normal', iv: [12, 12, 15], lvIdx: li(25), view: 'as-is' }, store.get('ivlab.check', {}));
if (!POKE.has(check.id)) check.id = 'charizard';
const ui = Object.assign({ rankId: 'medicham', rankLeague: 'great', rankFloor: 0, raidType: '', raidLevel: 40, braidType: '', boxSort: 'raid-at', boxTypes: [], boxTypeMode: 'and', boxMove: '' }, store.get('ivlab.ui', {}));
if (!POKE.has(ui.rankId)) ui.rankId = D.pokemon.find(p => !p.mega).id;
if (!ui.sortAt) { if (ui.boxSort === 'raid-hi') ui.boxSort = 'raid-at'; ui.sortAt = 1; }   // raids compare at Lv40 now
if ('boxType' in ui) { ui.boxMove = ui.boxMove || ui.boxType; delete ui.boxType; }   // old single filter was the move type
const saveUi = () => { store.set('ivlab.ui', ui); store.set('ivlab.check', check); };

function toast(msg) {
  const t = $('#toast'); t.textContent = msg; t.hidden = false;
  clearTimeout(toast.t); toast.t = setTimeout(() => { t.hidden = true; }, 2200);
}

/* ================= widgets ================= */
function setSeg(el, value) {
  for (const b of $$('button', el)) { b.setAttribute('role', 'radio'); b.setAttribute('aria-checked', String(b.dataset.v === String(value))); }
}
function bindSeg(el, onPick) {
  el.addEventListener('click', e => { const b = e.target.closest('button'); if (b && !b.disabled) onPick(b.dataset.v); });
}

const norm = s => s.toLowerCase().normalize('NFKD').replace(/[^a-z0-9 ]+/g, ' ').replace(/\s+/g, ' ').trim();
/* Japanese: full-width (NFKC), hiragana → katakana, no spaces or ・, so りざ / ﾘｻﾞ / リザ all match リザードン. */
const jnorm = s => String(s || '').normalize('NFKC').replace(/[\u3041-\u3096]/g, c => String.fromCharCode(c.charCodeAt(0) + 0x60)).replace(/[\s・･]/g, '');
const isKana = s => /[\u3040-\u30ff\uff66-\uff9f]/.test(s);
const SEARCH = D.pokemon.map(p => ({ p, n: norm(p.name), j: jnorm(p.ja) }));
/* name filter for lists: English words or Japanese name */
const nameMatch = (p, raw) => isKana(raw) ? jnorm(p.ja).includes(jnorm(raw)) : norm(p.name).includes(norm(raw));
function searchPokemon(q, { megas = false, limit = 40 } = {}) {
  const pool = SEARCH.filter(s => (megas || !s.p.mega) && s.p.released !== false);
  if (isKana(q)) {
    const jq = jnorm(q), hits = [];
    for (const s of pool) {
      if (!s.j.includes(jq)) continue;
      hits.push([(s.j === jq ? 0 : s.j.startsWith(jq) ? 1 : 2) * 10000 + s.p.dex + (s.p.mega ? 0.5 : 0), s.p]);
    }
    return hits.sort((a, b) => a[0] - b[0]).slice(0, limit).map(h => h[1]);
  }
  q = norm(q);
  if (!q) return pool.slice(0, limit).map(s => s.p);
  if (/^\d+$/.test(q)) return pool.filter(s => String(s.p.dex) === q).map(s => s.p);
  const toks = q.split(' ');
  const hits = [];
  for (const s of pool) {
    const words = s.n.split(' ');
    if (!toks.every(t => words.some(w => w.startsWith(t)) || s.n.includes(t))) continue;
    const score = (s.n.startsWith(q) ? 0 : words.some(w => w.startsWith(toks[0])) ? 1 : 2) * 10000 + s.p.dex;
    hits.push([score, s.p]);
  }
  return hits.sort((a, b) => a[0] - b[0]).slice(0, limit).map(h => h[1]);
}
function combo(root, { megas, onPick, getId }) {
  const input = $('.combo-input', root), list = $('.combo-list', root);
  let items = [], active = 0;
  const show = () => {
    list.innerHTML = items.length ? items.map((p, i) => `<li role="option" id="${root.dataset.combo}-opt-${i}" data-i="${i}" aria-selected="${i === active}">${pic(p)}<span class="dex">#${p.dex}</span><span>${esc(p.name)}${p.ja ? ` <span class="ja">${esc(p.ja)}</span>` : ''}</span><span class="types">${p.types.map(t => typeChip(t, true)).join('')}</span></li>`).join('')
      : '<li aria-disabled="true">No Pokémon found</li>';
    list.hidden = false; input.setAttribute('aria-expanded', 'true');
    if (items.length) input.setAttribute('aria-activedescendant', `${root.dataset.combo}-opt-${active}`);
  };
  const hide = () => { list.hidden = true; input.setAttribute('aria-expanded', 'false'); };
  const reset = () => { const p = POKE.get(getId()); input.value = p ? p.name : ''; };
  const pick = i => { const p = items[i]; if (!p) return; hide(); input.value = p.name; onPick(p); };
  input.addEventListener('focus', () => { input.select(); items = searchPokemon('', { megas }); active = 0; });
  input.addEventListener('input', () => { items = searchPokemon(input.value, { megas }); active = 0; show(); });
  input.addEventListener('keydown', e => {
    if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
      e.preventDefault(); if (list.hidden) { items = searchPokemon(input.value, { megas }); show(); return; }
      active = Math.max(0, Math.min(items.length - 1, active + (e.key === 'ArrowDown' ? 1 : -1))); show();
      $(`[data-i="${active}"]`, list)?.scrollIntoView({ block: 'nearest' });
    } else if (e.key === 'Enter') { e.preventDefault(); if (!list.hidden) pick(active); }
    else if (e.key === 'Escape') { hide(); reset(); }
  });
  list.addEventListener('mousedown', e => { const li = e.target.closest('li[data-i]'); if (li) { e.preventDefault(); pick(+li.dataset.i); } });
  input.addEventListener('blur', () => { hide(); reset(); });
  reset();
  return { reset };
}

/* ================= CHECK ================= */
const IV_NAMES = ['Attack', 'Defense', 'HP'];
function buildAppraisal() {
  const host = $('#appraisal');
  host.innerHTML = IV_NAMES.map((n, j) => `<div class="iv-row"><span class="iv-name" id="ivn-${j}">${n}</span>
    <div class="iv-bar" data-j="${j}" role="slider" tabindex="0" aria-labelledby="ivn-${j}" aria-valuemin="0" aria-valuemax="15">${'<span></span>'.repeat(16)}</div>
    <span class="iv-val" id="ivv-${j}"></span></div>`).join('');
  for (const bar of $$('.iv-bar', host)) {
    const j = +bar.dataset.j;
    const fromX = x => { const r = bar.getBoundingClientRect(); return Math.max(0, Math.min(15, Math.floor((x - r.left) / r.width * 16))); };
    let dragging = false;
    bar.addEventListener('pointerdown', e => { dragging = true; bar.setPointerCapture(e.pointerId); setIv(j, fromX(e.clientX)); });
    bar.addEventListener('pointermove', e => { if (dragging) setIv(j, fromX(e.clientX)); });
    bar.addEventListener('pointerup', () => { dragging = false; });
    bar.addEventListener('keydown', e => {
      const k = { ArrowRight: 1, ArrowUp: 1, ArrowLeft: -1, ArrowDown: -1 }[e.key];
      if (k) { e.preventDefault(); setIv(j, Math.max(0, Math.min(15, check.iv[j] + k))); }
      if (e.key === 'Home') setIv(j, 0); if (e.key === 'End') setIv(j, 15);
    });
  }
}
function paintAppraisal() {
  check.iv.forEach((v, j) => {
    const bar = $(`.iv-bar[data-j="${j}"]`);
    $$('span', bar).forEach((s, i) => s.classList.toggle('on', i > 0 && i <= v));
    bar.classList.toggle('max', v === 15);
    bar.setAttribute('aria-valuenow', v);
    $(`#ivv-${j}`).textContent = v;
  });
  const sum = check.iv[0] + check.iv[1] + check.iv[2];
  $('#iv-sum').textContent = `${sum}/45 · ${Math.round(sum / 45 * 100)}%`;
}
function setIv(j, v) {
  if (check.iv[j] === v) return;
  check.iv[j] = v;
  paintAppraisal(); syncCpFromLevel(); renderCheck();
}
function fillLevelSelect() {
  const max = li(Math.max(settings.lvCapped, settings.lvMaster));
  $('#check-lv').innerHTML = LV.slice(0, max + 1).map((lv, i) => `<option value="${i}">${lv}</option>`).join('');
}
function syncCpFromLevel() {
  const p = POKE.get(check.id);
  $('#check-lv').value = check.lvIdx;
  $('#check-cp').value = cpAt(p, check.iv, check.lvIdx);
  $('#cp-hint').textContent = ''; $('#cp-hint').classList.remove('bad');
}
function onCpInput() {
  const p = POKE.get(check.id), cp = +$('#check-cp').value, hint = $('#cp-hint');
  if (!cp) return;
  const max = li(Math.max(settings.lvCapped, settings.lvMaster));
  const hits = [];
  for (let i = 0; i <= max; i++) if (cpAt(p, check.iv, i) === cp) hits.push(i);
  hint.classList.toggle('bad', !hits.length);
  if (!hits.length) { hint.textContent = `No level gives CP ${cp} with ${check.iv.join('/')} IVs. Check the IVs or the CP.`; return; }
  check.lvIdx = hits[0];
  $('#check-lv').value = check.lvIdx;
  hint.textContent = hits.length > 1 ? `CP ${cp} fits levels ${hits.map(i => LV[i]).join(', ')}. Showing Lv ${LV[hits[0]]}; pick another in Level.` : `Level ${LV[hits[0]]}`;
  renderCheck();
}

function leagueTile(p, L, iv, lvIdx, origin) {
  const t = leagueTable(p, L), k = ivKey(iv);
  const curCp = cpAt(p, iv, lvIdx);
  const r1 = ivOf(t.order[0] ?? 0);
  if (t.sp[k] < 0 || curCp > L.cap) {
    const why = t.sp[k] < 0 ? 'Over cap at Lv 1' : `CP ${curCp} is over ${L.cap}`;
    return `<div class="league off"><span class="lname">${L.name}</span><span class="rank">Not eligible</span><span class="sub">${why}</span></div>`;
  }
  const pct = pctOf(t, k), rank = t.rank[k];
  const cls = rank <= 10 || pct >= 99 ? 'top' : pct >= 90 ? 'mid' : '';
  const tgt = t.lvI[k];
  const dust = tgt > lvIdx ? dustCost(lvIdx, Math.min(tgt, li(50)), origin) : 0;
  const lvTxt = `Lv ${LV[tgt]} · CP ${t.cps[k]}`;
  return `<div class="league ${cls}"><span class="lname">${L.name}</span>
    <span class="rank">#${rank}<small> / ${t.eligible}</small></span>
    <span class="sub"><span class="pct">${fmt(pct, 1)}%</span> · ${lvTxt}</span>
    <span class="sub">${dust ? `${fmtInt(dust)} stardust to power up` : 'No power-up needed'}${LV[tgt] > 50 ? ' + Best Buddy' : ''}</span>
    <span class="sub">Rank 1: ${r1.join('/')}</span>
    <span class="meter"><i style="width:${Math.max(2, pct)}%"></i></span></div>`;
}

function raidRows(p, iv, lvIdx, origin, limit) {
  const ms = movesFor(p, origin);
  const scNow = raidScale(p, iv, lvIdx);
  const rows = ms.map(m => ({ m, now: scaled(m, scNow), ref: refValues(p, m) }));
  rows.sort((a, b) => metricOf(b.now) - metricOf(a.now));
  return { rows: limit ? rows.slice(0, limit) : rows, total: rows.length };
}
/* Each number column shows "now" on top and the Lv40 15/15/15 (LvMax) reference underneath, so the table fits a phone. */
const RAID_HEAD = () => `<th class="num" title="Top: your Pokémon now. Below: Pokébase Lv40 15/15/15, Lv${settings.lvMaster} in brackets">eDPS<span class="th-sub">now · Lv40 (${settings.lvMaster})</span></th><th class="num" title="Top: your Pokémon now. Below: Pokébase Lv40 15/15/15, Lv${settings.lvMaster} in brackets">ER<span class="th-sub">now · Lv40 (${settings.lvMaster})</span></th>`;
const raidCells = (now, ref) => ['edps', 'er'].map(k => `<td class="num stack${settings.metric === k ? ' strong' : ''}"><span class="big">${now ? fmt(now[k], 2) : '—'}</span><span class="later">${ref ? `${fmt(ref[k], 1)} (${fmt(ref[k + 'Hi'], 1)})` : '—'}</span></td>`).join('');
const movesetCell = (m, extra = '') => `<td class="wrap"><div class="mv-cell"><div><span class="mv-line">${moveLabel(m.fast, m.fastStar)} ${typeChip(m.fastType, true)}</span><span class="mv-line">${moveLabel(m.charged, m.chargedStar)} ${typeChip(m.chargedType, true)}</span></div>${extra}</div></td>`;

function formCard(p, iv, lvIdx, origin, expanded) {
  const isMega = p.mega;
  const cpNow = cpAt(p, iv, lvIdx);
  const { rows, total } = raidRows(p, iv, lvIdx, origin, expanded ? 0 : 4);
  const leagues = `<div class="leagues">${LEAGUES.map(L => leagueTile(p, L, iv, lvIdx, origin)).join('')}</div>`;
  const raid = total ? `<div class="table-wrap"><table>
      <thead><tr><th>Moveset</th>${RAID_HEAD()}</tr></thead>
      <tbody>${rows.map(({ m, now, ref }) => `<tr>
        ${movesetCell(m, isMega ? '' : `<button class="btn small mv-save" data-save="${esc(p.id)}" data-fast="${esc(m.fast)}" data-charged="${esc(m.charged)}" data-origin="${origin}" data-iv="${iv.join(',')}" data-lv="${lvIdx}" aria-label="Save ${esc(p.name)} with ${esc(m.fast)} / ${esc(m.charged)}">Save</button>`)}
        ${raidCells(now, ref)}
      </tr>`).join('')}</tbody></table></div>
      ${total > rows.length || expanded ? `<div class="more-row"><button class="btn small" data-expand="${esc(p.id)}">${expanded ? 'Show top 4' : `Show all ${total} movesets`}</button></div>` : ''}`
    : `<p class="fine">No raid data for this form.</p>`;
  return `<article class="form-card${isMega ? ' is-mega' : ''}" id="card-${esc(p.id)}">
    <div class="form-head">
      ${pic(p, 'art')}<h2>${esc(p.name)}</h2>${p.types.map(t => typeChip(t)).join('')}
      ${origin === 'shadow' && !isMega ? '<span class="badge shadow">Shadow</span>' : ''}${origin === 'purified' && !isMega ? '<span class="badge purified">Purified</span>' : ''}
      ${isMega ? '<span class="badge mega">Mega</span>' : ''}${p.estimated ? '<span class="badge est" title="Base stats estimated from the base form so the scaling works; raid numbers are Pokébase\'s">est. stats</span>' : ''}
      <span class="meta">#${p.dex} · ${p.atk}/${p.def}/${p.hp} · CP ${cpNow} at Lv ${LV[lvIdx]}</span>
      <span class="spacer"></span>
      ${isMega ? '' : `<button class="btn small" data-save="${esc(p.id)}" data-origin="${origin}" data-iv="${iv.join(',')}" data-lv="${lvIdx}">Save to box</button>`}
    </div>
    ${leagues}
    ${raid}
  </article>`;
}

/* One row per form: league ranks + raid movesets that clear the eDPS/ER bar (judged on the Lv40 15/15/15 values). */
function leagueInfo(p, L, iv, lvIdx) {
  const t = leagueTable(p, L), k = ivKey(iv);
  return t.sp[k] >= 0 && cpAt(p, iv, lvIdx) <= L.cap ? { rank: t.rank[k], pct: pctOf(t, k) } : null;
}
function summaryTable(forms) {
  const rows = forms.map(({ x, o, iv, lv }) => {
    const leagues = LEAGUES.map(L => `<td data-l="${L.name.replace(' League', '').replace(' Cup', '')}">${pill(leagueInfo(x, L, iv, lv))}</td>`).join('');
    const sc = raidScale(x, iv, lv);
    const good = movesFor(x, o).filter(passesRaidBar)
      .map(m => ({ m, now: scaled(m, sc) })).sort((a, b) => metricOf(b.now) - metricOf(a.now)).slice(0, 2);
    const raid = good.length ? good.map(({ m, now }) => `<div class="sum-move"><span>${moveLabel(m.fast, m.fastStar)} / ${moveLabel(m.charged, m.chargedStar)}</span> ${typeChip(m.chargedType, true)}
        <span class="sum-num">${fmt(now.edps, 2)} <span class="later">eDPS</span> · ${fmt(now.er, 2)} <span class="later">ER</span></span></div>`).join('')
      : `<span class="fine">Below raid bar</span>`;
    return `<tr><td><button type="button" class="link-btn" data-jump="${esc(x.id)}">${pic(x)}<span>${esc(x.name)}</span></button></td>${leagues}<td class="sum-raid">${raid}</td></tr>`;
  }).join('');
  return `<div class="table-wrap summary-table"><table>
    <thead><tr><th>Form</th>${LEAGUES.map(L => `<th>${L.name.replace(' League', '').replace(' Cup', '')}</th>`).join('')}<th title="Shown when Lv40 15/15/15 eDPS ≥ ${settings.minEdps} or ER ≥ ${settings.minEr}; numbers are for your Pokémon now">Raid (now)</th></tr></thead>
    <tbody>${rows}</tbody></table></div>`;
}

const expandedCards = new Set();
let comboCheck = null;
function renderCheck() {
  const p = POKE.get(check.id);
  const out = $('#check-results');
  const hasShadow = p.shadow || (MOVES.get(p.id) || []).some(m => m.shadow);
  $('#check-origin button[data-v="shadow"]').disabled = !hasShadow;
  $('#check-origin button[data-v="purified"]').disabled = !hasShadow;
  if (!hasShadow && check.origin !== 'normal') check.origin = 'normal';
  setSeg($('#check-origin'), check.origin);

  let iv = check.iv, lvIdx = check.lvIdx, origin = check.origin;
  const purView = origin === 'shadow' && check.view === 'purified';
  if (purView) { iv = iv.map(v => Math.min(15, v + 2)); lvIdx = Math.max(lvIdx, li(25)); origin = 'purified'; }

  const line = evoLine(p);
  const forms = line.map(x => {
    const megaFromShadow = x.mega && origin === 'shadow';
    return {
      x, o: x.mega ? (origin === 'shadow' ? 'purified' : 'normal') : origin,
      iv: megaFromShadow ? iv.map(v => Math.min(15, v + 2)) : iv,
      lv: megaFromShadow ? Math.max(lvIdx, li(25)) : lvIdx,
    };
  });
  const head = `<div class="panel summary">
      ${pic(p, 'art')}<strong>${esc(p.name)}</strong>
      <span>IV ${iv.join('/')}</span><span>Lv ${LV[lvIdx]}</span><span>CP ${cpAt(p, iv, lvIdx)}</span>
      ${line.length > 1 ? `<span class="fine">Showing ${line.length} forms in its evolution line</span>` : ''}
      ${check.origin === 'shadow' ? `<span class="spacer" style="flex:1"></span><div class="seg" id="pur-switch" role="radiogroup" aria-label="Shadow or purified">
        <button type="button" data-v="as-is">As shadow</button><button type="button" data-v="purified">If purified (+2 IVs, Lv ≥25)</button></div>` : ''}
    </div>`;
  out.innerHTML = head + summaryTable(forms) + forms.map(f => formCard(f.x, f.iv, f.lv, f.o, expandedCards.has(f.x.id))).join('');
  const sw = $('#pur-switch');
  if (sw) { setSeg(sw, check.view); bindSeg(sw, v => { check.view = v; renderCheck(); }); }
  saveUi();
}

function bindCheck() {
  buildAppraisal(); fillLevelSelect();
  comboCheck = combo($('[data-combo="check"]'), {
    megas: false, getId: () => check.id,
    onPick: p => { check.id = p.id; expandedCards.clear(); syncCpFromLevel(); renderCheck(); },
  });
  bindSeg($('#check-origin'), v => { check.origin = v; check.view = 'as-is'; renderCheck(); });
  $('#check-cp').addEventListener('input', onCpInput);
  $('#check-lv').addEventListener('change', e => { check.lvIdx = +e.target.value; syncCpFromLevel(); renderCheck(); });
  $('#check-form').addEventListener('submit', e => e.preventDefault());
  $$('.quick-ivs [data-iv]').forEach(b => b.addEventListener('click', () => {
    check.iv = b.dataset.iv.split(',').map(Number); paintAppraisal(); syncCpFromLevel(); renderCheck();
  }));
  $('#check-results').addEventListener('click', e => {
    const jump = e.target.closest('[data-jump]');
    if (jump) { document.getElementById(`card-${jump.dataset.jump}`)?.scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block: 'start' }); return; }
    const ex = e.target.closest('[data-expand]');
    if (ex) { const id = ex.dataset.expand; expandedCards.has(id) ? expandedCards.delete(id) : expandedCards.add(id); renderCheck(); return; }
    const sv = e.target.closest('[data-save]');
    if (sv) {
      const entry = { uid: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), id: sv.dataset.save, origin: sv.dataset.origin, iv: sv.dataset.iv.split(',').map(Number), lvIdx: +sv.dataset.lv, fast: sv.dataset.fast || null, charged: sv.dataset.charged || null, added: Date.now() };
      box().push(entry); saveBox();
      toast(`Saved ${POKE.get(entry.id).name}${entry.charged ? ` (${entry.fast} / ${entry.charged})` : ''} to ${boxState.current}'s box`);
    }
  });
  paintAppraisal(); syncCpFromLevel();
}

/* ================= RANKINGS ================= */
let rankShown = 50;
function renderRankings() {
  const p = POKE.get(ui.rankId), L = LEAGUES.find(l => l.key === ui.rankLeague);
  setSeg($('#rank-league'), ui.rankLeague);
  $('#rank-floor').value = ui.rankFloor;
  const t = leagueTable(p, L), floor = +ui.rankFloor;
  const find = ['#find-a', '#find-d', '#find-h'].map(s => $(s).value === '' ? null : Math.max(0, Math.min(15, +$(s).value)));
  const findK = find.every(v => v != null) ? ivKey(find) : null;
  const rows = t.order.filter(k => { const iv = ivOf(k); return iv[0] >= floor && iv[1] >= floor && iv[2] >= floor; });
  // rank within the floor filter (ties share)
  const subRank = new Map();
  rows.forEach((k, i) => { const prev = rows[i - 1]; subRank.set(k, i > 0 && Math.abs(t.sp[k] - t.sp[prev]) <= 1e-9 * t.sp[k] ? subRank.get(prev) : i + 1); });
  const out = $('#rank-out');
  if (!rows.length) { out.innerHTML = `<div class="panel empty"><strong>No IV combination fits</strong><span>${esc(p.name)} is over ${L.cap} CP even at level 1.</span></div>`; return; }
  const best = rows[0], bestIv = ivOf(best);
  let found = '';
  if (findK != null) {
    if (t.sp[findK] < 0) found = `<span>${find.join('/')}: not eligible</span>`;
    else found = `<span>${find.join('/')}: <b>#${t.rank[findK]}</b>${floor ? ` (#${subRank.get(findK) ?? '—'} with floor ${floor})` : ''} · ${fmt(pctOf(t, findK), 2)}% · Lv ${LV[t.lvI[findK]]} · CP ${t.cps[findK]}</span>`;
    const pos = rows.indexOf(findK);
    if (pos >= rankShown) rankShown = Math.ceil((pos + 1) / 50) * 50;
  }
  const head = `<div class="panel rank1"><span class="fine">${esc(p.name)} · ${L.name}${floor ? ` · IV floor ${floor}` : ''}</span>
    <span>Best: <b>${bestIv.join('/')}</b> · Lv ${LV[t.lvI[best]]} · CP ${t.cps[best]}</span>${found}</div>`;
  const shown = rows.slice(0, rankShown);
  out.innerHTML = head + `<div class="table-wrap"><table>
    <thead><tr><th class="num">Rank</th>${floor ? '<th class="num">Overall</th>' : ''}<th>IVs</th><th class="num">%</th><th class="num">Level</th><th class="num">CP</th><th class="num opt">Atk</th><th class="num opt">Def</th><th class="num opt">HP</th><th class="num opt">Stat product</th></tr></thead>
    <tbody>${shown.map(k => {
      const iv = ivOf(k), s = statsAt(p, iv, t.lvI[k]);
      return `<tr class="${k === findK ? 'hl' : ''}"><td class="num strong">${subRank.get(k)}</td>${floor ? `<td class="num">${t.rank[k]}</td>` : ''}
        <td>${iv.join(' / ')}</td><td class="num">${fmt(pctOf(t, k), 2)}</td><td class="num">${LV[t.lvI[k]]}</td><td class="num">${t.cps[k]}</td>
        <td class="num opt">${fmt(s.a, 2)}</td><td class="num opt">${fmt(s.d, 2)}</td><td class="num opt">${s.h}</td><td class="num opt">${fmtInt(t.sp[k])}</td></tr>`;
    }).join('')}</tbody></table>
    ${rows.length > rankShown ? `<div class="more-row"><button class="btn small" id="rank-more">Show 50 more (${rows.length - rankShown} left)</button></div>` : ''}</div>`;
  $('#rank-more')?.addEventListener('click', () => { rankShown += 50; renderRankings(); });
  saveUi();
}
function bindRankings() {
  $('#rank-league').innerHTML = LEAGUES.map(L => `<button data-v="${L.key}">${L.name.replace(' League', '').replace(' Cup', '')}</button>`).join('');
  bindSeg($('#rank-league'), v => { ui.rankLeague = v; rankShown = 50; renderRankings(); });
  combo($('[data-combo="rank"]'), { megas: true, getId: () => ui.rankId, onPick: p => { ui.rankId = p.id; rankShown = 50; renderRankings(); } });
  $('#rank-floor').addEventListener('change', e => { ui.rankFloor = +e.target.value; rankShown = 50; renderRankings(); });
  ['#find-a', '#find-d', '#find-h'].forEach(s => $(s).addEventListener('input', renderRankings));
}

/* ================= RAIDS ================= */
let raidShown = 50;
function typeFilter(el, current, onPick) {
  el.innerHTML = `<button data-t="" aria-pressed="${current === ''}">All types</button>` +
    TYPES.map(t => `<button data-t="${t}" aria-pressed="${current === t}" style="--t:var(--t-${t})"><i></i>${t}</button>`).join('');
  el.onclick = e => { const b = e.target.closest('button'); if (b) onPick(b.dataset.t); };
}
function renderRaids() {
  typeFilter($('#raid-types'), ui.raidType, t => { ui.raidType = t; raidShown = 50; renderRaids(); });
  const megaOk = $('#raid-mega').checked, shOk = $('#raid-shadow').checked, starOk = $('#raid-star').checked, bestOnly = $('#raid-best').checked;
  const q = $('#raid-search').value.trim();
  let rows = [];
  for (const [id, ms] of MOVES) {
    const p = POKE.get(id);
    if (!p || (!megaOk && p.mega)) continue;
    if (q && !nameMatch(p, q)) continue;
    for (const m of ms) {
      if (!shOk && m.shadow) continue;
      if (!starOk && (m.fastStar || m.chargedStar)) continue;
      if (ui.raidType && m.chargedType !== ui.raidType) continue;
      rows.push({ p, m, v: refValues(p, m) });
    }
  }
  rows.sort((a, b) => metricOf(b.v) - metricOf(a.v));
  if (bestOnly) { const seen = new Set(); rows = rows.filter(r => { const k = r.p.id + (r.m.shadow ? '|s' : ''); if (seen.has(k)) return false; seen.add(k); return true; }); }
  // mark box entries
  const mine = new Set(box().map(e => `${e.id}|${e.origin === 'shadow' ? 1 : 0}`));
  const shown = rows.slice(0, raidShown);
  const lvHi = settings.lvMaster;
  $('#raid-out').innerHTML = rows.length ? `<div class="table-wrap"><table>
    <thead><tr><th class="num">#</th><th>Pokémon · moveset</th><th class="num">eDPS<span class="th-sub">Lv40 (${lvHi})</span></th><th class="num">ER<span class="th-sub">Lv40 (${lvHi})</span></th><th class="num opt">DPS</th><th class="num opt">TDO</th></tr></thead>
    <tbody>${shown.map((r, i) => `<tr class="${mine.has(`${r.p.id}|${r.m.shadow ? 1 : 0}`) ? 'yours' : ''}">
      <td class="num">${i + 1}</td>
      <td class="wrap"><span class="name-cell">${pic(r.p)}${r.m.shadow ? '<span class="badge shadow">Shadow</span>' : ''}<b>${esc(r.p.name)}</b>${r.p.estimated ? ' <span class="badge est">est.</span>' : ''}</span>
        <span class="mv-line fine-mv">${moveLabel(r.m.fast, r.m.fastStar)} ${typeChip(r.m.fastType, true)} · ${moveLabel(r.m.charged, r.m.chargedStar)} ${typeChip(r.m.chargedType, true)}</span></td>
      ${['edps', 'er'].map(k => `<td class="num stack${settings.metric === k ? ' strong' : ''}"><span class="big">${fmt(r.v[k], 2)}</span><span class="later">(${fmt(r.v[k + 'Hi'], 2)})</span></td>`).join('')}
      <td class="num opt">${fmt(r.v.dps, 2)}</td><td class="num opt">${fmtInt(r.v.tdo)}</td></tr>`).join('')}</tbody></table>
    ${rows.length > raidShown ? `<div class="more-row"><button class="btn small" id="raid-more">Show 50 more (${rows.length - raidShown} left)</button></div>` : ''}</div>
    <p class="fine">Highlighted rows: species you have in ${esc(boxState.current)}'s box.</p>`
    : `<div class="panel empty"><strong>No attackers match</strong><span>Loosen the filters above.</span></div>`;
  $('#raid-more')?.addEventListener('click', () => { raidShown += 50; renderRaids(); });
  saveUi();
}
function bindRaids() {
  ['#raid-mega', '#raid-shadow', '#raid-star', '#raid-best'].forEach(s => $(s).addEventListener('change', () => { raidShown = 50; renderRaids(); }));
  $('#raid-search').addEventListener('input', () => { raidShown = 50; renderRaids(); });
}

/* ================= BOX RAIDS ================= */
/* Candy per power-up by level (stardust comes from dustCost). Shadow +20%, purified −10%, rounded up. */
const candyAt = lv => lv < 11 ? 1 : lv < 21 ? 2 : lv < 26 ? 3 : lv < 31 ? 4 : lv < 33 ? 6 : lv < 35 ? 8 : lv < 37 ? 10 : lv < 39 ? 12 : 15;
function powerCost(from, to, origin) {
  const k = origin === 'shadow' ? 1.2 : origin === 'purified' ? 0.9 : 1, end = Math.min(to, li(40));
  let candy = 0;
  for (let i = from; i < end; i++) candy += Math.ceil(candyAt(LV[i]) * k - 1e-9);
  return { dust: end > from ? dustCost(from, end, origin) : 0, candy };
}
let braidShown = 50;
/* Like Raids, but only this box's Pokémon: each as its final evolutions (and their Megas) with its own IVs at Lv40. */
function renderBoxRaids() {
  typeFilter($('#braid-types'), ui.braidType, t => { ui.braidType = t; braidShown = 50; renderBoxRaids(); });
  $('#braid-user').textContent = boxState.current;
  const megaOk = $('#braid-mega').checked, bestOnly = $('#braid-best').checked, lowOk = $('#braid-low').checked;
  const q = $('#braid-search').value.trim(), to = li(settings.lvRaid);
  let rows = [];
  for (const raw of box()) {
    const p = POKE.get(raw.id); if (!p) continue;
    const e = effEntry(raw, p);
    for (const F of finalsOf(p)) for (const S of [F, ...(megaOk ? megasOf(F) : [])]) {
      if (q && !nameMatch(p, q) && !nameMatch(S, q)) continue;
      let ms = entryMoves(e, S);
      if (ui.braidType) ms = ms.filter(m => m.chargedType === ui.braidType);
      if (!ms.length) continue;
      const f = asForm(e, S);
      const ml = pctOf(leagueTable(S.mega ? megaBase(S) || S : S, MASTER), ivKey(f.iv));
      const need = e.origin === 'shadow' && !S.mega ? settings.ivRaidShadow : settings.ivRaid;
      if (!(ml >= need) && !lowOk) continue;
      const origin = S.mega && e.origin === 'shadow' ? 'purified' : e.origin;
      const scA = raidScale(S, f.iv, atIdx(f.lv)), scH = raidScale(S, f.iv, Math.max(f.lv, hiIdx()));
      const base = { e, raw, p, S, f, origin, ok: ml >= need, ml, need, cost: powerCost(f.lv, to, origin) };
      let list = ms.map(m => ({ ...base, m, v: scaled(m, scA), h: scaled(m, scH) }));
      if (bestOnly) list = [list.reduce((a, b) => metricOf(b.v) > metricOf(a.v) ? b : a)];
      rows.push(...list);
    }
  }
  rows.sort((a, b) => metricOf(b.v) - metricOf(a.v));
  const shown = rows.slice(0, braidShown), lvA = settings.lvRaid, lvH = settings.lvMaster;
  const costText = r => {
    const extra = [r.S.mega ? 'Mega Energy' : r.S.id !== r.p.id ? 'evolve' : '', r.raw.origin === 'shadow' && r.origin === 'purified' ? 'purify' : ''].filter(Boolean).join(' + ');
    const c = r.cost.dust ? `To Lv${lvA}: <b>${fmtInt(r.cost.dust)}</b> dust · <b>${r.cost.candy}</b> candy` : `Lv${LV[r.f.lv]}, no power-up needed`;
    return `<span class="cost">${c}${extra ? ` <span class="fine">+ ${extra}</span>` : ''}</span>`;
  };
  $('#braid-out').innerHTML = rows.length ? `<div class="table-wrap"><table>
    <thead><tr><th class="num">#</th><th>Pokémon · moveset · cost</th><th class="num">eDPS<span class="th-sub">Lv${lvA} (${lvH})</span></th><th class="num">ER<span class="th-sub">Lv${lvA} (${lvH})</span></th><th class="num opt">DPS</th></tr></thead>
    <tbody>${shown.map((r, i) => `<tr class="${r.ok ? '' : 'dim'}">
      <td class="num">${i + 1}</td>
      <td class="wrap"><span class="name-cell">${pic(r.S)}${originBadge(r.origin)}<b>${esc(r.S.name)}</b></span>
        <span class="fine sub">${r.S.id !== r.p.id ? `from ${esc(r.p.name)} · ` : ''}${r.f.iv.join('/')} · Lv ${LV[r.f.lv]}${r.raw !== r.e || r.S.mega && r.raw.origin === 'shadow' ? ` <span class="was">(shadow ${r.raw.iv.join('/')})</span>` : ''}${r.ok ? '' : ` · Master League ${fmt(r.ml, 0)}%, under ${r.need}%`}</span>
        <span class="mv-line fine-mv">${moveLabel(r.m.fast, r.m.fastStar)} ${typeChip(r.m.fastType, true)} · ${moveLabel(r.m.charged, r.m.chargedStar)} ${typeChip(r.m.chargedType, true)}</span>
        ${costText(r)}</td>
      ${['edps', 'er'].map(k => `<td class="num stack${settings.metric === k ? ' strong' : ''}"><span class="big">${fmt(r.v[k], 2)}</span><span class="later">(${fmt(r.h[k], 2)})</span></td>`).join('')}
      <td class="num opt">${fmt(r.v.dps, 2)}</td></tr>`).join('')}</tbody></table>
    ${rows.length > braidShown ? `<div class="more-row"><button class="btn small" id="braid-more">Show 50 more (${rows.length - braidShown} left)</button></div>` : ''}</div>
    <p class="fine">Each Pokémon in ${esc(boxState.current)}'s box as its final evolutions${megaOk ? ' and their Megas' : ''}, with its own IVs powered up to Lv${lvA} (or its level, if higher); Lv${lvH} in brackets.
      Only Pokémon whose Master League IV % reaches your Settings (${settings.ivRaid}%, shadow ${settings.ivRaidShadow}%) unless "Below IV %" is on. A shadow Mega is counted as purified.
      Cost = stardust and candy to power up from its level to Lv${lvA} (shadow +20%, purified −10%; Lucky, evolution, purification and Mega Energy not included).</p>`
    : `<div class="panel empty"><strong>${box().length ? 'Nothing matches' : `${esc(boxState.current)}'s box is empty`}</strong><span>${box().length ? 'Loosen the filters, or turn on "Below IV %".' : 'Import or save some Pokémon first.'}</span></div>`;
  $('#braid-more')?.addEventListener('click', () => { braidShown += 50; renderBoxRaids(); });
  saveUi();
}
function bindBoxRaids() {
  ['#braid-mega', '#braid-best', '#braid-low'].forEach(s => $(s).addEventListener('change', () => { braidShown = 50; renderBoxRaids(); }));
  $('#braid-search').addEventListener('input', () => { braidShown = 50; renderBoxRaids(); });
}

/* ================= BOX ================= */
const RAID_TOP = 6, RAID_TOP_MEGA = 3;
const cap1 = s => s[0].toUpperCase() + s.slice(1);
const hiIdx = () => li(settings.lvMaster);
/* raid comparison level: powered up to Lv40 (Settings), or its current level if already higher */
const atIdx = lv => Math.max(lv, li(settings.lvRaid));
const lgShort = L => L.name.replace(' League', '').replace(' Cup', '');
const MASTER = LEAGUES.find(L => L.key === 'master');

/* Forms a Pokémon can still become: itself and its evolutions (no going back, no Megas). */
function forwardLine(p) {
  const out = [p], seen = new Set([p.id]);
  for (let i = 0; i < out.length; i++) for (const e of out[i].evolutions || []) {
    const y = POKE.get(e);
    if (y && !y.mega && !seen.has(y.id)) { seen.add(y.id); out.push(y); }
  }
  return out;
}
const isFinal = S => !(S.evolutions || []).some(id => { const y = POKE.get(id); return y && !y.mega; });
const finalsOf = p => forwardLine(p).filter(isFinal);
/* Megas / Primals of a form, by id: charizard → charizard_mega_x / _y, kyogre → kyogre_primal, lucario → mega_lucario_z. */
const MEGAS = new Map();
for (const m of D.pokemon) {
  if (!m.mega || !(MOVES.get(m.id) || []).length) continue;
  const stem = m.id.startsWith('mega_') ? m.id.slice(5) : m.id;
  let base = null;
  for (const b of D.pokemon) if (!b.mega && b.dex === m.dex && (stem === b.id || stem.startsWith(b.id + '_')) && (!base || b.id.length > base.id.length)) base = b;
  if (base) { if (!MEGAS.has(base.id)) MEGAS.set(base.id, []); MEGAS.get(base.id).push(m); }
}
const megasOf = S => MEGAS.get(S.id) || [];
const megaBase = M => D.pokemon.find(b => megasOf(b).includes(M));
const megaName = M => (M.name.match(/\(([^)]*)\)/) || [, 'Mega'])[1];

/* Raid labels rank the Pokémon in this box against each other, each with its own IVs powered up to Lv40 (or its current level if higher), per charged-move type
   (one value per Pokémon: its best final evolution; Megas go in their own pool). `cat` holds per move type x and per
   exact type pair + move type ('Fire/Flying>Fire'; Flying/Fire is the same pair); `dex` keeps the best per species and
   move type, for the distinct ranking (one per species: Shadow Mewtwo and Mewtwo count once). */
const typePair = S => [...S.types].sort().join('/');
function boxPools(rows, mine, lines) {
  const mk = () => ({ cat: new Map(), dex: new Map() }), reg = mk(), meg = mk();
  const put = (m, k, id, v) => { let x = m.get(k); if (!x) m.set(k, x = new Map()); if (!(x.get(id) >= v)) x.set(id, v); };
  for (const r of rows) for (const F of lines.get(r.e.uid).filter(isFinal)) for (const S of [F, ...megasOf(F)]) {
    const v = mine(r, S), pool = S.mega ? meg : reg, pair = typePair(S);
    for (const x in v) {
      if (x === 'all' || v[x] < 0) continue;
      put(pool.cat, x, r.e.uid, v[x]);
      put(pool.cat, pair + '>' + x, r.e.uid, v[x]);
      put(pool.dex, x, S.dex, v[x]);
    }
  }
  return { reg, meg };
}
const above = (o, v) => o > v * (1 + 1e-9);
/* rank of value v among the other Pokémon in a pool category (ties share the rank) */
function boxRank(pool, cat, uid, v) {
  let n = 1;
  for (const [u, o] of pool.cat.get(cat) || []) if (u !== uid && above(o, v)) n++;
  return n;
}
/* rank among species (best of each species only); 0 when another of the same species is better */
function distinctRank(pool, cat, dex, v) {
  const m = pool.dex.get(cat) || new Map();
  if (above(m.get(dex), v)) return 0;
  let n = 1;
  for (const [d, o] of m) if (d !== dex && above(o, v)) n++;
  return n;
}
/* best raid value overall ('all') and per charged-move type, for movesets ms at stat scale sc */
function catValues(p, ms, sc) {
  const out = { all: -1 };
  for (const m of ms) {
    const v = metricOf(scaled(m, sc));
    if (v > out.all) out.all = v;
    if (!(m.chargedType in out) || v > out[m.chargedType]) out[m.chargedType] = v;
  }
  return out;
}
/* A box Pokémon as form S. A shadow has to be purified before it can Mega Evolve (+2 IVs, Lv ≥ 25). */
function asForm(e, S) {
  const pur = S.mega && e.origin === 'shadow';
  return { iv: pur ? e.iv.map(v => Math.min(15, v + 2)) : e.iv, lv: pur ? Math.max(e.lvIdx, li(25)) : e.lvIdx, origin: S.mega ? 'normal' : e.origin };
}
/* Movesets it can use as S: the moveset you picked (for its own form and that form's Megas), otherwise all of S's. */
function entryMoves(e, S) {
  const ms = movesFor(S, asForm(e, S).origin);
  const own = S.id === e.id || (S.mega && megasOf(POKE.get(e.id)).includes(S));
  if (own && e.charged) { const m = ms.find(m => m.fast === e.fast && m.charged === e.charged); if (m) return [m]; }
  return ms;
}
/* Raid numbers as form S with its best moveset (of the move-type filter, if set): now, at LvMax, and Pokébase max IVs. */
function raidForm(e, S) {
  let ms = entryMoves(e, S);
  if (ui.boxMove) ms = ms.filter(m => m.chargedType === ui.boxMove);
  if (!ms.length) return null;
  const f = asForm(e, S);
  const pick = ms.reduce((a, m) => metricOf(m) > metricOf(a) ? m : a);
  return { S, pick, atLv: LV[atIdx(f.lv)], at: scaled(pick, raidScale(S, f.iv, atIdx(f.lv))), now: scaled(pick, raidScale(S, f.iv, f.lv)), hi: scaled(pick, raidScale(S, f.iv, Math.max(f.lv, hiIdx()))), ref: refValues(S, pick) };
}

/* A shadow with its Purified switch on is ranked as purified: +2 IVs (max 15), Lv 25 at least, purified moves.
   The stored shadow IVs never change, so switching back gives exactly the original numbers. */
function effEntry(e, p) {
  if (e.origin !== 'shadow' || !e.purify) return e;
  const x = { ...e, origin: 'purified', iv: e.iv.map(v => Math.min(15, v + 2)), lvIdx: Math.max(e.lvIdx, li(25)) };
  if (x.charged && !movesFor(p, 'purified').some(m => m.fast === x.fast && m.charged === x.charged)) x.fast = x.charged = null;
  return x;
}
/* Box Pokémon at its full potential: raid numbers for its best final evolution, plus that form's Megas. */
function evalEntry(raw) {
  const p = POKE.get(raw.id);
  if (!p) return null;
  const e = effEntry(raw, p);
  const finals = finalsOf(p);
  const opts = finals.map(S => raidForm(e, S)).filter(Boolean).sort((a, b) => metricOf(b.at) - metricOf(a.at));
  const main = opts[0] || null;
  const megas = main ? megasOf(main.S).map(M => raidForm(e, M)).filter(Boolean).sort((a, b) => metricOf(b.at) - metricOf(a.at)) : [];
  return { e, raw, p, main, megas, nFinals: finals.length, best: !e.charged, hasMove: !ui.boxMove || !!main, cp: cpAt(p, e.iv, e.lvIdx) };
}
/* best league % it can reach in L (any form it can still become that fits under the cap at its level) — for sorting */
/* Forms it can use in PvP: itself, its evolutions, and their Megas (a shadow has to be purified to Mega Evolve). */
const pvpForms = p => forwardLine(p).flatMap(S => [S, ...megasOf(S)]);
function pvpAt(e, S, L) {
  const f = asForm(e, S), t = leagueTable(S, L), k = ivKey(f.iv);
  return t.sp[k] < 0 || cpAt(S, f.iv, f.lv) > L.cap ? null : { pct: pctOf(t, k), rank: t.rank[k] };
}
function bestLeaguePct(r, L) {
  let b = -1;
  for (const S of pvpForms(r.p)) { const v = pvpAt(r.e, S, L); if (v) b = Math.max(b, v.pct); }
  return b;
}

/* Labels for every Pokémon in the box.
   Raid, per charged-move type: as its final evolution, with its own IVs at Lv40 (or its level, if higher), it is in the top 6 of this box for
   that move type, or top 6 among distinct species (best of each species only), or #1 among Pokémon with exactly its
   type pair (Fire/Flying with Fire). Its Megas are ranked among the box's Megas only (top 3, top 3 distinct, #1 pair). Full label when the Master League IV % is at least ivRaid (ivRaidShadow for shadows; a Mega
   counts the purified IVs); otherwise a dim label with a note.
   PvP: a form it can still become reaches ivPvp % in Little / Great / Ultra and fits under the cap at its current level.
   In Great / Ultra a form is skipped when one of its evolutions also fits (Machop isn't a Great League pick when Machamp
   fits); Little Cup only counts forms that can still evolve. Megas count too (shadows as purified).
   Master League: final forms and their Megas, only when there's no raid label.
   All: a note when another Pokémon in the box that can become the same form does better. */
let labelsCache = { key: '', map: null };
function boxLabels(rows) {
  const key = JSON.stringify([boxState.current, box(), settings, ui.boxMove]);
  if (labelsCache.key === key) return labelsCache.map;
  const lines = new Map(rows.map(r => [r.e.uid, forwardLine(r.p)]));
  const canBe = (r, S) => lines.get(r.e.uid).some(x => S.mega ? megasOf(x).includes(S) : x.id === S.id);
  const mineCache = new Map();
  const mine = (r, S) => {   // this Pokémon's own values as form S, powered up to Lv40 (or its level, if higher)
    const k = r.e.uid + '|' + S.id;
    if (!mineCache.has(k)) { const f = asForm(r.e, S); mineCache.set(k, catValues(S, entryMoves(r.e, S), raidScale(S, f.iv, atIdx(f.lv)))); }
    return mineCache.get(k);
  };
  const { reg, meg } = boxPools(rows, mine, lines);
  const pvp = (r, S, L) => pvpAt(r.e, S, L);
  const stronger = (self, S, valueOf, own) => {
    let best = null, bv = own + 1e-9;
    for (const o of rows) { if (o === self || !canBe(o, S)) continue; const v = valueOf(o); if (v > bv) { bv = v; best = o; } }
    return best;
  };
  const map = new Map();
  for (const r of rows) {
    const out = [];
    const finals = lines.get(r.e.uid).filter(isFinal);
    for (const S of finals.flatMap(F => [F, ...megasOf(F)])) {
      const v = mine(r, S);
      if (v.all < 0) continue;
      const M = S.mega, pool = M ? meg : reg, top = M ? RAID_TOP_MEGA : RAID_TOP, pre = M ? 'Mega ' : '', uid = r.e.uid;
      const pair = typePair(S), pairName = S.types.length > 1 ? S.types.map(cap1).join('/') : `pure ${cap1(S.types[0])}`;
      const bestType = (entryMoves(r.e, S).reduce((a, m) => !a || metricOf(m) > metricOf(a) ? m : a, null) || {}).chargedType;
      const found = [];
      for (const x of TYPES) {
        if (!(x in v)) continue;
        const rX = boxRank(pool, x, uid, v[x]);
        if (rX <= top) found.push({ cat: x, rank: rX, text: `#${rX} ${pre}${cap1(x)}`, tier: 3, x });
        const rD = distinctRank(pool, x, S.dex, v[x]);   // shown when it adds something (#5 Fire but #2 distinct Fire)
        if (rD && rD <= top && rD !== rX) found.push({ cat: x, rank: rD, text: `#${rD} ${pre}distinct ${cap1(x)}`, tier: 2, x });
        // exact type pair + move type, #1 only: for its own types' moves and its best moveset's type (not every coverage move)
        if (rX !== 1 && (S.types.includes(x) || x === bestType) && boxRank(pool, pair + '>' + x, uid, v[x]) === 1)
          found.push({ cat: x, rank: 1, text: `#1 ${pre}${pairName} with ${cap1(x)}`, tier: 1, x });
      }
      if (!found.length) continue;
      const f = asForm(r.e, S);
      const ml = pctOf(leagueTable(S.mega ? megaBase(S) || S : S, MASTER), ivKey(f.iv));
      const need = r.e.origin === 'shadow' && !S.mega ? settings.ivRaidShadow : settings.ivRaid;
      for (const x of found) out.push({ kind: 'raid', S, mega: S.mega, ...x, ok: ml >= need, ml, need, evolved: S.id !== r.p.id,
        better: stronger(r, S, o => mine(o, S)[x.cat] ?? -1, mine(r, S)[x.cat]) });
    }
    const hasRaid = out.length > 0;
    for (const L of LEAGUES) {
      if (L === MASTER && hasRaid) continue;   // Master League label only for Pokémon without a raid label
      for (const S of pvpForms(r.p)) {
        if (L.key === 'little' ? !(S.evolutions || []).length   // Little Cup: only Pokémon that can still evolve (no Megas)
          : forwardLine(S).some(N => N !== S && cpAt(N, r.e.iv, r.e.lvIdx) <= L.cap)) continue;   // an evolution also fits: label that instead
        const v = pvp(r, S, L);
        if (!v || v.pct < settings.ivPvp) continue;
        out.push({ kind: 'pvp', L, S, pct: v.pct, rank: v.rank, ok: true, evolved: S.id !== r.p.id,
          better: stronger(r, S, o => (pvp(o, S, L) || { pct: -1 }).pct, v.pct) });
      }
    }
    map.set(r.e.uid, out);
  }
  labelsCache = { key, map };
  return map;
}

const pill = l => l ? `<span class="pill ${l.rank <= 10 || l.pct >= 99 ? 'top' : l.pct >= 90 ? 'mid' : ''}" title="Rank ${l.rank}">#${l.rank} · ${fmt(l.pct, 0)}%</span>` : '<span class="pill" title="Over the CP cap">—</span>';
const originBadge = o => o === 'shadow' ? '<span class="badge shadow">Shadow</span>' : o === 'purified' ? '<span class="badge purified">Purified</span>' : '';
const whoLine = o => `${esc(o.p.name)}${o.e.origin !== 'normal' ? ` (${o.e.origin})` : ''} ${o.e.iv.join('/')}`;
const mvText = m => `${esc(m.fast)}${m.fastStar ? '<span class="star">*</span>' : ''} / ${esc(m.charged)}${m.chargedStar ? '<span class="star">*</span>' : ''}`;

/* One line per form for raid labels ("Mega Y: #1 Mega · #1 Mega Psychic"); one line per league for PvP,
   showing the best form it can become (+ how many other forms also qualify). */
function labelRows(labels) {
  const rows = [];
  const raid = new Map();
  for (const l of labels) if (l.kind === 'raid') { if (!raid.has(l.S.id)) raid.set(l.S.id, []); raid.get(l.S.id).push(l); }
  const groups = [...raid.values()].map(g => g.sort((a, b) => b.tier - a.tier || a.rank - b.rank))
    .sort((a, b) => (a[0].ok ? 0 : 2) + (a[0].mega ? 1 : 0) - (b[0].ok ? 0 : 2) - (b[0].mega ? 1 : 0) || b[0].tier - a[0].tier || a[0].rank - b[0].rank);
  for (const g of groups) {
    const l = g[0];
    const head = l.mega ? esc(megaName(l.S)) : l.evolved ? `→ ${esc(l.S.name)}` : '';
    const notes = [];
    if (!l.ok) notes.push(`Master League IV ${fmt(l.ml, 0)}%, under ${l.need}%`);
    const better = [...new Set(g.filter(x => x.better).map(x => whoLine(x.better)))];
    if (better.length) notes.push(`You have a stronger one: ${better.join(', ')}`);
    rows.push({ order: (l.ok ? 0 : 20) + (l.mega ? 5 : 0) - l.tier + l.rank / 100, html: `<li class="${l.ok ? '' : 'dim'}">${head ? `<span class="lbl-form">${head}</span>` : ''}${g.map(x =>
      `<span class="lbl raid t${x.tier}${x.mega ? ' mega' : ''}"${x.x ? ` style="--t:var(--t-${x.x})"` : ''}>${x.text}</span>`).join('')}${notes.length ? `<span class="lbl-note">${notes.map(esc).join(' · ')}</span>` : ''}</li>` });
  }
  for (const L of LEAGUES) {
    const g = labels.filter(l => l.kind === 'pvp' && l.L === L);
    if (!g.length) continue;
    const prod = S => S.atk * S.def * S.hp;
    g.sort((a, b) => b.pct - a.pct || prod(b.S) - prod(a.S));
    const l = g[0];
    rows.push({ order: 10, html: `<li><span class="lbl pvp lg-${L.key}">${lgShort(L)} ${fmt(l.pct, 1)}% · #${l.rank}${l.evolved ? ` <span class="as">as ${esc(l.S.name)}</span>` : ''}</span>${g.length > 1 ? `<span class="lbl-note">+${g.length - 1} other form${g.length > 2 ? 's' : ''} (${g.slice(1).map(x => esc(x.S.name)).join(', ')})</span>` : ''}${l.better ? `<span class="lbl-note">You have a stronger one: ${esc(whoLine(l.better))}</span>` : ''}</li>` });
  }
  return rows.sort((a, b) => a.order - b.order).map(r => r.html).join('');
}

function monCard(r, labels) {
  const raidOk = labels.filter(l => l.kind === 'raid' && l.ok);
  const glow = raidOk.some(l => !l.mega && l.tier >= 2 && l.rank === 1) ? 'glow-3' : raidOk.length ? 'glow-2' : labels.some(l => l.kind === 'pvp') ? 'glow-pvp' : labels.length ? 'glow-dim' : '';
  const num = (k, v) => `<b class="${settings.metric === k ? 'key' : ''}">${v ? fmt(v[k], 2) : '—'}</b>`;
  const m = r.main, own = m && m.S.id === r.p.id;
  const raid = !m ? `<p class="fine">${ui.boxMove ? `No ${esc(ui.boxMove)} moveset.` : 'No raid data.'}</p>` : `
    <div class="mv-pick">${own ? movesetSelect(r) : `<span class="as-form">→ <b>${esc(m.S.name)}</b>${r.nFinals > 1 ? ` <span class="fine">(best of ${r.nFinals})</span>` : ''}</span><span class="fine">${mvText(m.pick)}</span> ${typeChip(m.pick.chargedType, true)}`}</div>
    <div class="mon-nums">
      <span></span><span class="h">eDPS</span><span class="h">ER</span>
      <span class="h">Now</span>${num('edps', m.now)}${num('er', m.now)}
      <span class="h" title="Powered up to Lv${settings.lvRaid}; labels and the Top 6 compare this">Lv${m.atLv}</span>${num('edps', m.at)}${num('er', m.at)}
      <span class="h">Lv${settings.lvMaster}</span>${num('edps', m.hi)}${num('er', m.hi)}
      <span class="h" title="Pokébase Lv40 15/15/15, Lv${settings.lvMaster} 15/15/15 in brackets">Max IV</span><span class="ref">${fmt(m.ref.edps, 1)} (${fmt(m.ref.edpsHi, 1)})</span><span class="ref">${fmt(m.ref.er, 1)} (${fmt(m.ref.erHi, 1)})</span>
    </div>
    ${r.megas.map(x => `<div class="mega-row"><span class="badge mega">${esc(megaName(x.S))}</span><span class="fine">${mvText(x.pick)}${r.e.origin === 'shadow' ? ' · if purified' : ''}</span>
      <span class="mega-val">Lv${x.atLv} <b class="${settings.metric === 'edps' ? 'key' : ''}">${fmt(x.at.edps, 2)}</b> eDPS · <b class="${settings.metric === 'er' ? 'key' : ''}">${fmt(x.at.er, 2)}</b> ER <span class="later">(Lv${settings.lvMaster} ${fmt(metricOf(x.hi), 1)})</span></span></div>`).join('')}`;
  return `<article class="mon ${glow}" id="mon-${esc(r.e.uid)}">
    <div class="mon-head">
      <button type="button" class="link-btn" data-open="${esc(r.e.uid)}" title="Open in Check">${pic(r.p)}<span class="mon-name">${esc(r.p.name)}</span></button>
      <span class="mon-types">${r.p.types.map(t => typeChip(t, true)).join('')}</span>
      <select class="mini origin-${r.raw.origin}" data-origin="${esc(r.e.uid)}" aria-label="Origin of ${esc(r.p.name)}">${['normal', 'shadow', 'purified'].map(o => `<option value="${o}" ${o === r.raw.origin ? 'selected' : ''}>${cap1(o)}</option>`).join('')}</select>
      ${r.raw.origin === 'shadow' ? `<span class="seg sm purify" role="radiogroup" aria-label="Rank ${esc(r.p.name)} as" data-purify="${esc(r.e.uid)}">${[['', 'As shadow'], ['1', 'As purified']].map(([v, t]) => `<button type="button" role="radio" data-v="${v}" aria-checked="${!!v === !!r.raw.purify}">${t}</button>`).join('')}</span>` : ''}
      <span class="spacer"></span>
      <span class="mon-meta"><b>${r.e.iv.join('/')}</b> · Lv ${LV[r.e.lvIdx]} · CP ${r.cp}${r.e !== r.raw ? `<span class="was">shadow ${r.raw.iv.join('/')} · Lv ${LV[r.raw.lvIdx]}</span>` : ''}</span>
      <button class="btn small" data-del="${esc(r.e.uid)}" aria-label="Remove ${esc(r.p.name)}">Remove</button>
    </div>
    <div class="mon-raid">${raid}</div>
    ${labels.length ? `<ul class="mon-labels">${labelRows(labels)}</ul>` : ''}
  </article>`;
}

/* Top 6 of the filtered box by the raid metric at Lv40 (or its level, if higher), each as its best final evolution with its own IVs. */
function top6Panel(rows, desc) {
  const top = rows.filter(r => r.main).sort((a, b) => metricOf(b.main.at) - metricOf(a.main.at)).slice(0, 6);
  if (!top.length) return '';
  return `<section class="panel top6" aria-labelledby="h-top6">
    <div class="title-row"><h2 id="h-top6" class="panel-title">Top 6 at Lv${settings.lvRaid} · ${metricName()}</h2><span class="fine">${desc}</span></div>
    <ol class="top6-list">${top.map((r, i) => `<li><button type="button" class="top6-item" data-goto="${esc(r.e.uid)}">
      <span class="top6-rank">${i + 1}</span>${pic(r.main.S)}
      <span class="top6-main"><span class="top6-name">${esc(r.main.S.name)} ${originBadge(r.e.origin)}</span>
        <span class="fine">${r.main.S !== r.p ? `from ${esc(r.p.name)} · ` : ''}${r.e.iv.join('/')} · Lv ${LV[r.e.lvIdx]} · ${mvText(r.main.pick)}</span></span>
      <span class="top6-val"><b>${fmt(metricOf(r.main.at), 2)}</b><span class="fine">now ${fmt(metricOf(r.main.now), 2)}</span></span>
    </button></li>`).join('')}</ol>
  </section>`;
}

/* Pokémon-type filter: up to two types, "both" (has both types) or "either". Move-type filter: one charged-move type. */
function boxFilters() {
  const pt = ui.boxTypes;
  $('#box-ptypes').innerHTML = `<button data-t="" aria-pressed="${!pt.length}">Any</button>` +
    TYPES.map(t => `<button data-t="${t}" aria-pressed="${pt.includes(t)}" style="--t:var(--t-${t})"><i></i>${t}</button>`).join('');
  $('#box-mtypes').innerHTML = `<button data-t="" aria-pressed="${!ui.boxMove}">Any</button>` +
    TYPES.map(t => `<button data-t="${t}" aria-pressed="${ui.boxMove === t}" style="--t:var(--t-${t})"><i></i>${t}</button>`).join('');
  setSeg($('#box-type-mode'), ui.boxTypeMode);
  $('#box-type-mode').hidden = pt.length < 2;
}
function filterDesc() {
  const parts = [];
  if (ui.boxTypes.length) parts.push(ui.boxTypes.map(cap1).join(ui.boxTypeMode === 'and' ? ' + ' : ' or ') + (ui.boxTypes.length > 1 && ui.boxTypeMode === 'and' ? ' types' : ' type'));
  if (ui.boxMove) parts.push(`${cap1(ui.boxMove)} moves`);
  const q = $('#box-search').value.trim();
  if (q) parts.push(`"${esc(q)}"`);
  return parts.length ? `Filtered: ${parts.join(' · ')}` : `All of ${esc(boxState.current)}'s box`;
}

function renderBox() {
  $('#box-user').textContent = boxState.current;
  boxFilters();
  $('#box-sort').value = ui.boxSort;
  const out = $('#box-out');
  if (!box().length) {
    out.innerHTML = `<div class="panel empty"><strong>${esc(boxState.current)}'s box is empty</strong><span>Use the Import tab to read a screen recording, or press <b>Save to box</b> on the Check tab. Use Import (top right) to load a backup.</span><a class="btn primary" href="#import">Go to Import</a></div>`;
    return;
  }
  const allRows = box().map(evalEntry).filter(Boolean);
  const labels = boxLabels(allRows);
  const q = $('#box-search').value.trim();
  const pt = ui.boxTypes;
  let rows = allRows.filter(r => r.hasMove
    && (!q || nameMatch(r.p, q))
    && (!pt.length || (ui.boxTypeMode === 'and' ? pt.every(t => r.p.types.includes(t)) : pt.some(t => r.p.types.includes(t)))));
  const s = ui.boxSort, L = LEAGUES.find(x => x.key === s);
  const raidKey = k => r => r.main ? metricOf(r.main[k]) : -1;
  const key = s === 'raid-at' ? raidKey('at') : s === 'raid-hi' ? raidKey('hi') : s === 'raid-now' ? raidKey('now') : s === 'raid-ref' ? raidKey('ref')
    : s === 'added' ? r => r.e.added : s === 'dex' ? r => -r.p.dex * 1e5 + r.cp : s === 'labels' ? r => labelScore(labels.get(r.e.uid)) * 1000 + raidKey('at')(r) : r => bestLeaguePct(r, L);
  const keyed = rows.map(r => [key(r), r]).sort((a, b) => b[0] - a[0]);
  rows = keyed.map(x => x[1]);
  out.innerHTML = backupBanner() + top6Panel(rows, filterDesc()) + (rows.length
    ? `<div class="mon-list">${rows.map(r => monCard(r, labels.get(r.e.uid) || [])).join('')}</div>
      <p class="fine">Tap a name to open it in Check. Raid numbers are for the best final evolution (→) and its Megas: now · powered up to Lv${settings.lvRaid} (or its level, if higher) · Lv${settings.lvMaster} · Pokébase max IVs at Lv40 (Lv${settings.lvMaster}).
      "Best" = no moveset picked yet. Raid labels rank this box against itself per charged-move type: each Pokémon as its best final evolution with its own IVs at Lv${settings.lvRaid} (or its level, if higher; the IV % check uses Lv${settings.lvMaster}). "Distinct" counts only the best of each species; "Fire/Flying with Fire" = #1 among that exact type pair. Megas are ranked only with Megas (top 3). Shadows can be ranked as purified with their switch (+2 IVs, Lv 25+).
      League labels show only when a form it can become reaches your % (Settings).</p>`
    : `<div class="panel empty"><strong>Nothing matches</strong><span>Clear a type or name filter.</span></div>`);
  saveUi();
}
const labelScore = ls => (ls || []).reduce((s, l) => s + (l.kind === 'raid' ? (l.ok ? 10 + l.tier : 1) : 3), 0);

/* moveset picker for a box card (its own form is final): "Best" or one of its movesets, sorted by value now */
function movesetSelect(r) {
  const ms = movesFor(r.p, r.e.origin);
  if (!ms.length) return '<span class="fine">No raid data</span>';
  const sc = raidScale(r.p, r.e.iv, r.e.lvIdx);
  const sorted = ms.map(m => ({ m, v: metricOf(scaled(m, sc)) })).sort((a, b) => b.v - a.v);
  const lbl = m => `${m.fast}${m.fastStar ? '*' : ''} / ${m.charged}${m.chargedStar ? '*' : ''}`;
  const pick = r.main && r.main.pick;
  return `<select class="mini mv" data-mv="${esc(r.e.uid)}" aria-label="Moveset of ${esc(r.p.name)}">
    <option value="" ${r.best ? 'selected' : ''}>Best${ui.boxMove ? ` ${cap1(ui.boxMove)}` : ''}: ${esc(lbl(r.best && pick ? pick : sorted[0].m))}</option>
    ${sorted.map(({ m, v }) => `<option value="${esc(m.fast)}|${esc(m.charged)}" ${!r.best && m === pick ? 'selected' : ''}>${esc(lbl(m))} · ${fmt(v, 1)}</option>`).join('')}
  </select>${pick ? ` ${typeChip(pick.chargedType, true)}` : ''}`;
}
/* Backup: on iPhone the share sheet lets you "Save to Files" (iCloud Drive); elsewhere it downloads a .json file. */
async function exportBox() {
  const name = `ivlab-box-${new Date().toISOString().slice(0, 10)}.json`;
  const json = JSON.stringify({ app: 'ivlab', version: 1, exported: new Date().toISOString(), users: boxState.users }, null, 1);
  const file = new File([json], name, { type: 'application/json' });
  const msg = $('#box-io-msg');
  try {
    if (navigator.canShare && navigator.canShare({ files: [file] })) {
      await navigator.share({ files: [file], title: 'IV Lab backup' });
    } else {
      const a = document.createElement('a'); a.href = URL.createObjectURL(file); a.download = name;
      document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 1000);
    }
    boxState.lastBackup = Date.now(); boxState.changesSinceBackup = 0; saveBox(true);
    msg.textContent = `Backed up all trainers' boxes (${name}).`;
    if ($('#view-box') && !$('#view-box').hidden) renderBox();
  } catch (err) {
    msg.textContent = err && err.name === 'AbortError' ? 'Backup cancelled.' : `Backup failed: ${err.message || err}`;
  }
}
function backupBanner() {
  const total = Object.values(boxState.users).reduce((s, l) => s + l.length, 0);
  const changes = boxState.changesSinceBackup || 0;
  const days = boxState.lastBackup ? (Date.now() - boxState.lastBackup) / 864e5 : Infinity;
  if (!total || !changes || (changes < 10 && days < 7)) return '';
  const when = boxState.lastBackup ? `Last backup ${Math.floor(days)} day${Math.floor(days) === 1 ? '' : 's'} ago` : 'No backup yet';
  return `<div class="panel banner"><span><b>${when}.</b> ${changes} change${changes === 1 ? '' : 's'} since. Your box lives only on this device; save a copy to Files or iCloud Drive.</span><button class="btn primary small" id="backup-now">Back up now</button></div>`;
}
let pendingDelete = null;
function bindBox() {
  $('#box-sort').addEventListener('change', e => { ui.boxSort = e.target.value; renderBox(); });
  $('#box-search').addEventListener('input', renderBox);
  $('#box-ptypes').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    const t = b.dataset.t, pt = ui.boxTypes;
    if (!t) ui.boxTypes = [];
    else if (pt.includes(t)) ui.boxTypes = pt.filter(x => x !== t);
    else ui.boxTypes = [...pt, t].slice(-2);   // a third pick replaces the oldest
    renderBox();
  });
  $('#box-mtypes').addEventListener('click', e => { const b = e.target.closest('button'); if (b) { ui.boxMove = ui.boxMove === b.dataset.t ? '' : b.dataset.t; renderBox(); } });
  bindSeg($('#box-type-mode'), v => { ui.boxTypeMode = v; renderBox(); });
  $('#box-out').addEventListener('change', e => {
    const uid = e.target.dataset.mv || e.target.dataset.origin; if (!uid) return;
    const entry = box().find(x => x.uid === uid); if (!entry) return;
    if (e.target.dataset.mv !== undefined) {
      const [fast, charged] = e.target.value ? e.target.value.split('|') : [null, null];
      entry.fast = fast; entry.charged = charged;
    } else {
      entry.origin = e.target.value;
      const p = POKE.get(entry.id);   // a moveset that this origin can't have (e.g. Return on a shadow) goes back to "Best"
      if (entry.charged && !movesFor(p, entry.origin).some(m => m.fast === entry.fast && m.charged === entry.charged)) entry.fast = entry.charged = null;
    }
    saveBox(); renderBox();
  });
  $('#box-out').addEventListener('click', e => {
    const pf = e.target.closest('[data-purify] button');
    if (pf) {   // only a flag: the stored shadow IVs stay as they are
      const entry = box().find(x => x.uid === pf.parentElement.dataset.purify); if (!entry) return;
      const on = !!pf.dataset.v;
      if (!!entry.purify === on) return;
      if (on) entry.purify = true; else delete entry.purify;
      saveBox(true); renderBox();
      return;
    }
    const go = e.target.closest('[data-goto]');
    if (go) {
      const el = document.getElementById(`mon-${go.dataset.goto}`); if (!el) return;
      el.scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block: 'center' });
      el.classList.remove('flash'); void el.offsetWidth; el.classList.add('flash');
      return;
    }
    const open = e.target.closest('[data-open]');
    if (open) {
      const entry = box().find(x => x.uid === open.dataset.open); if (!entry) return;
      Object.assign(check, { id: entry.id, iv: entry.iv.slice(), lvIdx: entry.lvIdx, origin: entry.origin, view: 'as-is' });
      expandedCards.clear(); paintAppraisal(); syncCpFromLevel(); comboCheck.reset();
      location.hash = '#check'; window.scrollTo(0, 0);
      return;
    }
    const b = e.target.closest('[data-del]'); if (!b) return;
    if (pendingDelete !== b.dataset.del) { pendingDelete = b.dataset.del; b.textContent = 'Confirm'; b.classList.add('primary'); return; }
    boxState.users[boxState.current] = box().filter(x => x.uid !== b.dataset.del); pendingDelete = null; saveBox(); renderBox(); toast('Removed');
  });
  $('#box-export').addEventListener('click', exportBox);
  $('#box-out').addEventListener('click', e => { if (e.target.closest('#backup-now')) exportBox(); });
  $('#box-import').addEventListener('change', async e => {
    const f = e.target.files[0]; if (!f) return;
    try {
      const j = JSON.parse(await f.text());
      if (!j.users || typeof j.users !== 'object') throw new Error('no "users" in file');
      let n = 0;
      for (const [u, list] of Object.entries(j.users)) {
        if (!Array.isArray(list)) continue;
        const have = new Set((boxState.users[u] ||= []).map(x => x.uid));
        for (const x of list) if (x && POKE.has(x.id) && Array.isArray(x.iv) && !have.has(x.uid)) { boxState.users[u].push(x); n++; }
      }
      saveBox(); renderUsers(); renderBox();
      $('#box-io-msg').textContent = `Imported ${n} Pokémon. Entries already in your box were skipped.`;
    } catch (err) { $('#box-io-msg').textContent = `Couldn't import that file (${err.message}). Choose a file made with Export.`; }
    e.target.value = '';
  });
}

/* ================= shell ================= */
function renderBoxCount() { $('#box-count').textContent = box().length || ''; }
function renderUsers() {
  $('#user-select').innerHTML = Object.keys(boxState.users).map(u => `<option ${u === boxState.current ? 'selected' : ''}>${esc(u)}</option>`).join('');
  renderBoxCount();
}
const VIEWS = ['check', 'rankings', 'raids', 'box', 'boxraids', 'import'];
const RENDER = { check: renderCheck, rankings: renderRankings, raids: renderRaids, box: renderBox, boxraids: renderBoxRaids, import: () => window.renderImport && window.renderImport() };
function route() {
  const v = VIEWS.includes(location.hash.slice(1)) ? location.hash.slice(1) : 'check';
  for (const x of VIEWS) $(`#view-${x}`).hidden = x !== v;
  $$('.tabs a').forEach(a => { if (a.dataset.tab === v) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current'); });
  RENDER[v]();
}
function rerenderAll() { tableCache.clear(); labelsCache.key = ''; route(); }
function bindShell() {
  $('#settings-btn').addEventListener('click', e => { const s = $('#settings'); s.hidden = !s.hidden; e.currentTarget.setAttribute('aria-expanded', String(!s.hidden)); });
  const seg = (id, key, num) => { setSeg($(id), settings[key]); bindSeg($(id), v => { settings[key] = num ? +v : v; setSeg($(id), settings[key]); saveSettings(); fillLevelSelect(); $('#check-lv').value = check.lvIdx; rerenderAll(); }); };
  seg('#set-lv-capped', 'lvCapped', true); seg('#set-lv-master', 'lvMaster', true); seg('#set-metric', 'metric', false); seg('#set-lv-raid', 'lvRaid', true);
  for (const [id, key] of [['#set-min-edps', 'minEdps'], ['#set-min-er', 'minEr'], ['#set-iv-raid', 'ivRaid'], ['#set-iv-raid-sh', 'ivRaidShadow'], ['#set-iv-pvp', 'ivPvp']]) {
    $(id).value = settings[key];
    $(id).addEventListener('change', e => { const v = parseFloat(e.target.value); if (Number.isFinite(v) && v >= 0 && (id.startsWith('#set-min') || v <= 100)) { settings[key] = v; saveSettings(); route(); } else e.target.value = settings[key]; });
  }
  $('#user-select').addEventListener('change', e => { boxState.current = e.target.value; saveBox(true); route(); });
  $('#add-user-form').addEventListener('submit', e => {
    e.preventDefault(); const n = $('#new-user').value.trim();
    if (!n) return; if (boxState.users[n]) { toast(`${n} already exists`); return; }
    boxState.users[n] = []; boxState.current = n; saveBox(); renderUsers(); $('#new-user').value = ''; toast(`Added trainer ${n}`); route();
  });
  $('#data-meta').textContent = `Data: ${D.meta.pokebase_csv} · PvPoke gamemaster ${D.meta.gamemaster || ''} · ${D.pokemon.length} forms, ${D.moves.length} raid movesets.`;
  window.addEventListener('hashchange', route);
}

/* ================= installed app (home screen) ================= */
const isStandalone = () => matchMedia('(display-mode: standalone)').matches || navigator.standalone === true;
const isIOS = /iP(hone|ad|od)/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);
async function setupApp() {
  if ('serviceWorker' in navigator && location.protocol.startsWith('http')) {
    navigator.serviceWorker.register('sw.js').catch(() => { /* offline support unavailable; the site still works */ });
  }
  let persisted = false;
  try { persisted = navigator.storage && (await navigator.storage.persisted() || await navigator.storage.persist()); } catch { /* not supported */ }
  const where = isStandalone() ? 'Installed app' : 'Browser tab';
  $('#storage-meta').textContent = `${where} · storage ${persisted ? 'marked persistent: the browser will not clear it on its own' : 'not marked persistent: the browser may clear it if space runs low'}. Back up regularly from the Box tab.`;
  const hint = $('#install-hint');
  let dismissed = false; try { dismissed = localStorage.getItem('ivlab.installHint') === 'no'; } catch { /* ignore */ }
  if (hint && isIOS && !isStandalone() && !dismissed) {
    hint.hidden = false;
    $('#install-hint-close').addEventListener('click', () => { hint.hidden = true; try { localStorage.setItem('ivlab.installHint', 'no'); } catch { /* ignore */ } });
  }
}

bindShell(); bindCheck(); bindRankings(); bindRaids(); bindBox(); bindBoxRaids(); renderUsers(); setupApp();
// import.js loads after this file; route once it has registered its view
if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', route); else setTimeout(route);
