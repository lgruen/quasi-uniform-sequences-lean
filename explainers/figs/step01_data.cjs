// step01_data.cjs -- data for the figures of step 1: four 2D sequences, their first points, and the exact
// separation constant sep(P_[N]) = delta(P_[N]) * sqrt(N) (toroidal) for every N up to NMAX.
// Uses ../src/core.js (checked against the paper by ../check/crosscheck.cjs). Output: step01_data.json.
const fs = require('fs'), path = require('path');
global.window = { __SQDATA: JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'data.json'))) };
const SQ = require(path.join(__dirname, '..', 'src', 'core.js'));
const NMAX = 5 ** 7;                       // 78125 points
const id = (n) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, k) => +(i === k)));
SQ.addNet('rand', { kind: 'random', s: 2, seed: 7 });
SQ.addNet('sobol', { q: 2, D: 30, M: 20, C: SQ.sobol3Matrices(30).slice(0, 2) });
SQ.addNet('faure5', { q: 5, D: 16, M: 8, C: [id(16), SQ.pascal(1, 5, 16, 16)] });
SQ.addNet('res5', { q: 5, D: 22, M: 8, C: SQ.residue(5, [0, 1], 1, [2, 4], 22, 8) });   // v = (2, -1): cor:korobov at p = 5
const out = {};
for (const key of ['rand', 'sobol', 'faure5', 'res5']) {
  const P = SQ.points(key, NMAX), ev = SQ.sepEvents(key, NMAX);
  const Ns = [], seps = [];
  for (let N = 2; N <= NMAX; N = Math.max(N + 1, Math.floor(N * 1.01))) { Ns.push(N); seps.push(SQ.sepAt(ev, N).c); }
  const pts = [Array.from(P.X[0].slice(0, 625)), Array.from(P.X[1].slice(0, 625))];
  out[key] = { Ns, seps, pts, events: { N: Array.from(ev.evN), i: Array.from(ev.evI), j: Array.from(ev.evJ), d: Array.from(ev.evD) } };
  console.log(key, 'sep at 125:', SQ.sepAt(ev, 125).c.toFixed(3), ' at 3125:', SQ.sepAt(ev, 3125).c.toFixed(3), ' at 78125:', SQ.sepAt(ev, NMAX).c.toFixed(3));
}
fs.writeFileSync(path.join(__dirname, 'step01_data.json'), JSON.stringify(out));
