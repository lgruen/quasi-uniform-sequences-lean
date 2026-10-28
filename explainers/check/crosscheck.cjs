// crosscheck.cjs -- runs the math of src/core.js under node and compares it with the paper's builders and numbers.
//   node `explainers/check/crosscheck.cjs        (after gen_data.py; ~20 s)
// Checks: (1) the JS ports of the residue / staggered-residue / brick-wall / Faure generators against the Python builders
// (paper/v4/figs/b3_gen.py, make_figs.py) entry by entry (check/ref.json); (2) the in-browser exact separation (incremental
// and static cell lists) against the audited sepx.cpp values in data.json; (3) lambda_jit and the bounds of tab:residue,
// cor:dyadic; (4) the explicit close pairs of rem:faurerate and cor:sobol; (5) prefix-wise minima J of fig:evidence.
const fs = require('fs'), path = require('path');
const H = path.dirname(__dirname);
global.window = { __SQDATA: JSON.parse(fs.readFileSync(path.join(H, 'data.json'))) };
const SQ = require(path.join(H, 'src', 'core.js'));
const REF = JSON.parse(fs.readFileSync(path.join(H, 'check', 'ref.json')));
const D = window.__SQDATA;
let pass = 0, fail = 0;
const ok = (cond, what) => { if (cond) pass++; else { fail++; console.log('FAIL', what); } };
const eqM = (A, B) => A.length <= B.length && A.every((r, n) => r.every((x, k) => x === B[n][k]));
const trunc = (x, k) => Math.floor(x * Math.pow(10, k) + 1e-9) / Math.pow(10, k);

// (1) generators
for (const r of REF.res) {
  const rows = r.C[0].length, cols = r.C[0][0].length;
  const J = SQ.residue(r.p, r.a, r.theta, r.v, rows, cols);
  ok(J.every((M, c) => eqM(M, r.C[c])), `residue p=${r.p} a=${r.a} v=${r.v}`);
}
for (const r of REF.stag) {
  const rows = r.C[0].length, cols = r.C[0][0].length;
  const J = SQ.staggered(r.p, r.a, r.theta, r.cstar, r.mu, rows, cols);
  ok(J.every((M, c) => eqM(M, r.C[c])), `staggered p=${r.p} a=${r.a}`);
}
for (const [key, p] of [['wf5', 5], ['wf7', 7], ['wf13', 13]]) {
  const C = REF[key], J = SQ.brickwall(p, C[0].length, C[0][0].length);
  ok(J.every((M, c) => eqM(M, C[c])), `brick wall p=${p}`);
}
{ const C = REF.faure5, J = SQ.faure(5, 2, C[0].length, C[0][0].length); ok(J.every((M, c) => eqM(M, C[c])), 'Faure p=5'); }
ok(eqM(D.nets.wf7.C[0], SQ.brickwall(7, 18, 16)[0]) && eqM(D.nets.wf7.C[1], SQ.brickwall(7, 18, 16)[1]), 'exported wf7 = JS brick wall');

// (2) exact separation in the browser vs sepx
const net = (key, C, q, M) => SQ.addNet(key, { q, D: C[0].length, M, C });
function sepFull(key, m, s) { const N = Math.pow(SQ.nets[key].q, m), P = SQ.points(key, N), r = SQ.closest(P, N); return { c: r.d * Math.pow(N, 1 / s), i: r.i, j: r.j }; }
function sepInc(key, m, s) { const N = Math.pow(SQ.nets[key].q, m), ev = SQ.sepEvents(key, N); return SQ.sepAt(ev, N).c; }
net('wf13', SQ.brickwall(13, 14, 6), 13, 6);
for (const m of [2, 4]) { ok(Math.abs(sepFull('wf13', m, 2).c - D.sep[`wf13_m${m}`][0]) < 2e-6, `wf13 m=${m} static`); ok(Math.abs(sepInc('wf13', m, 2) - D.sep[`wf13_m${m}`][0]) < 2e-6, `wf13 m=${m} incremental`); }
net('res11', SQ.residue(11, [0, 1], 1, [3, 10], 15, 8), 11, 8);
for (const m of [3, 5]) ok(Math.abs(sepFull('res11', m, 2).c - D.sep[`res11_m${m}`][0]) < 2e-6, `res11 m=${m}`);
net('res311', SQ.residue(11, [0, 1, 2], 1, [9, 4, 10], 15, 6), 11, 6);
for (const m of [2, 5]) { const t = sepFull('res311', m, 3).c; ok(Math.abs(t - D.sep[`res311_m${m}`][0]) < 2e-6, `res311 m=${m} static ${t}`); }
ok(Math.abs(sepInc('res311', 5, 3) - D.sep.res311_m5[0]) < 2e-6, 'res311 m=5 incremental');
for (const p of [3, 5, 7]) for (const m of [4, 6]) {
  const k = `block${p}_m${m}`; if (!D.sep[k]) continue;
  ok(Math.abs(sepFull(`block${p}`, m, 2).c - D.sep[k][0]) < 2e-6, k);
}
SQ.addNet('fa5', { q: 5, D: 22, M: 8, C: SQ.faure(5, 2, 22, 8) });
ok(Math.abs(sepFull('fa5', 5, 2).c - D.sep.faure5_m5[0]) < 2e-6, 'faure5 m=5');
{ const P = SQ.points('fa5', 3125); ok(Math.abs(Math.sqrt(SQ.td2(P, 1, 3120)) - Math.sqrt(17) / 3125) < 1e-12, 'fig:carry pair (1, 3120) at sqrt(17) 5^-5'); }
SQ.addNet('fa7', { q: 7, D: 18, M: 8, C: SQ.faure(7, 2, 18, 8) });
for (const [m, v] of [[2, .8690], [4, .3115], [6, .2463]]) ok(Math.round(sepFull('fa7', m, 2).c * 1e4) / 1e4 === v, `tab:faure m=${m}`);
// levels_p5 (fig:levels (b)): residue, brick wall, block columns for m <= 8 (in the browser's range)
SQ.addNet('r5', { q: 5, D: 22, M: 10, C: SQ.residue(5, [0, 1], 1, [2, 4], 22, 10) });
SQ.addNet('w5', { q: 5, D: 22, M: 10, C: SQ.brickwall(5, 22, 10) });
for (const row of D.levels_p5) {
  const m = row[0]; if (m < 2 || m > 7) continue;
  ok(Math.abs(sepFull('r5', m, 2).c - row[1]) < 6e-5, `levels_p5 residue m=${m}`);
  ok(Math.abs(sepFull('w5', m, 2).c - row[2]) < 6e-5, `levels_p5 brick wall m=${m}`);
  ok(Math.abs(sepFull('block5', m, 2).c - row[3]) < 6e-5, `levels_p5 block m=${m}`);
}
// hexagonal brick wall p = 401, P_2 (fig:HB): exact .9922 from the graph form
{ const P = SQ.points('hb401', 401 * 401), r = SQ.closest(P, 401 * 401); ok(Math.abs(r.d * 401 - D.sep.hb401_m2[0]) < 2e-6, `hb401 P_2 ${r.d * 401}`); }

// (3) lambda_jit, tab:residue (bounds truncated to 3 digits) and Korobov
const tabRes = [[11, [3, 10], 4, .603], [17, [4, 16], 9, .727], [37, [6, 36], 25, .821], [101, [30, 100], 85, .917], [1009, [122, 1008], 1060, 1.024],
  [11, [9, 4, 10], 1, .449], [17, [6, 2, 16], 1, .388], [37, [9, 3, 36], 4, .600], [101, [35, 13, 100], 13, .774], [1009, [105, 11, 1008], 89, .940],
  [10007, [7775, 9087, 10006], 498, 1.035], [17, [9, 15, 4, 16], 1, .492], [37, [14, 4, 2, 36], 1, .405], [101, [27, 9, 3, 100], 4, .630]];
for (const [p, v, l2, b] of tabRes) {
  const r = SQ.ljit2(v, p), s = v.length;
  ok(r.l2 === l2, `ljit2 p=${p} v=${v}: ${r.l2} vs ${l2}`);
  ok(trunc(Math.sqrt(l2) * Math.pow(p, -1 / s), 3) === b, `tab:residue bound p=${p} s=${s}`);
}
// exhaustive best x for s = 2 (column "best v found", search E)
for (const [p, l2] of [[11, 4], [17, 9], [37, 25], [101, 85], [1009, 1060]]) {
  let best = 0; for (let x = 1; x < p; x++) best = Math.max(best, SQ.ljit2([x, p - 1], p).l2); ok(best === l2, `exhaustive s=2 p=${p}: ${best}`);
}
// Korobov column: lambda_jit = rho - 1
for (const [s, p, b] of [[3, 101, .644], [3, 1009, .897], [4, 1009, .709], [5, 1009, .501], [2, 101, .895]]) {
  const rho = Math.floor(Math.pow(p, 1 / s) + 1e-9), v = []; for (let c = 1; c < s; c++) v.push(Math.pow(rho, c) % p); v.push(p - 1);
  const r = SQ.ljit2(v, p); ok(r.l2 === (rho - 1) * (rho - 1), `Korobov ljit s=${s} p=${p}`); ok(trunc((rho - 1) * Math.pow(p, -1 / s), 3) === b, `Korobov bound s=${s} p=${p}`);
}
// cor:dyadic: beta = (floor(p/2^{s-1}) - 1)/p, and a brute force over all weights for small cases confirms the cap
function beta(k, p) { const s1 = k.length; let best = Infinity; const e = new Array(s1).fill(-1);
  for (let t = 0; t < Math.pow(3, s1); t++) { let x = t, dot = 0, nz = false; for (let i = 0; i < s1; i++) { const d = x % 3 - 1; x = Math.floor(x / 3); if (d) nz = true; dot += d * k[i]; } if (!nz) continue; best = Math.min(best, Math.abs(SQ.cen(dot, p)) - 1); }
  return best / p; }
for (const [s, p, num] of [[3, 11, 1], [4, 37, 3], [5, 211, 12], [3, 41, 9], [3, 101, 24], [3, 1009, 251]]) {
  const k = []; for (let i = 1; i < s; i++) k.push(SQ.inv(Math.pow(2, s - i), p));
  ok(Math.abs(beta(k, p) - num / p) < 1e-12, `cor:dyadic s=${s} p=${p}`);
}
for (const [s, p] of [[3, 11], [3, 17], [3, 37]]) { let best = -1; for (let a = 1; a < p; a++) for (let b = 1; b < p; b++) best = Math.max(best, beta([a, b], p)); ok(Math.abs(best - (Math.floor(p / 4) - 1) / p) < 1e-12, `dyadic cap s=3 p=${p}`); }

// (4) explicit close pairs: rem:faurerate (p = 5, Q = 5: indices 3120 and 1) and cor:sobol (Q = 1: 4 and 26) via the points
{ const P = SQ.points('fa5', 3125); ok(SQ.td2(P, 3120, 1) * 3125 < (25 + 4) / 3125, 'rem:faurerate bound p=5 Q=5'); }
SQ.addNet('sob2', { q: 2, D: 30, M: 20, C: SQ.faure(2, 2, 30, 20) });
{ const P = SQ.points('sob2', 32); const d = Math.sqrt(SQ.td2(P, 4, 26)) * 8; ok(Math.abs(d - D.sobolpairs[0].dscaled) < 1e-9, `cor:sobol Q=1 pair distance*2^L ${d}`); }
// 3D Sobol' matrices: first direction numbers of x+1 (Pascal) and x^2+x+1 (Joe-Kuo 1, 3)
{ const u = SQ.sobolDirs([1, 1, 1], [1, 3], 8); ok(u.slice(1).join(',') === '1,3,3,9,29,23,71,197', 'Sobol dim 3 directions (same recurrence as figs_bs/bslib.py): ' + u.slice(1).join(',')); }

// (5) J from the drop files (fig:evidence): rebuild sepEvents-like objects
for (const [k, c, N] of [['res31', .267, 208652], ['fa31', .095, 53879]]) {
  const ev = { evN: D.practice[k].map(a => a[0]), evD: D.practice[k].map(a => a[1]), s: 3 }, r = SQ.minSepRange(ev, 64, 1 << 23);
  ok(Math.round(r.c * 1000) / 1000 === c && r.N === N, `J ${k}: ${r.c} at ${r.N}`);
}
// the residue sequence of tab:practice at p = 13 regenerated in JS: certified bound .425 at P_2 (lambda_jit of v)
{ const r = SQ.ljit2([5, 3, 6], 13); ok(trunc(Math.sqrt(r.l2) * Math.pow(13, -1 / 3), 3) === .425, 'tab:practice p=13 bound'); }
for (const [p, v, b] of [[17, [4, 10, 16], .388], [23, [4, 14, 20], .497], [31, [10, 30, 7], .636]]) { const r = SQ.ljit2(v, p); ok(trunc(Math.sqrt(r.l2) * Math.pow(p, -1 / 3), 3) === b, `tab:practice p=${p} bound`); }

console.log(`${pass} checks passed, ${fail} failed`);
process.exit(fail ? 1 : 0);
