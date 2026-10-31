// step01_checkpoints.cjs -- separation at the checkpoints N = 5^m (m = 1..7) and 2^m for Sobol',
// exact for the digital sequences; for random points the median over 41 seeds. Output: step01_checkpoints.json.
const fs = require('fs'), path = require('path');
global.window = { __SQDATA: JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'data.json'))) };
const SQ = require(path.join(__dirname, '..', 'src', 'core.js'));
const id = (n) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, k) => +(i === k)));
SQ.addNet('sobol', { q: 2, D: 30, M: 20, C: SQ.sobol3Matrices(30).slice(0, 2) });
SQ.addNet('faure5', { q: 5, D: 16, M: 8, C: [id(16), SQ.pascal(1, 5, 16, 16)] });
SQ.addNet('res5', { q: 5, D: 22, M: 8, C: SQ.residue(5, [0, 1], 1, [2, 4], 22, 8) });
const out = {}, N5 = [1, 2, 3, 4, 5, 6, 7].map(m => 5 ** m), N2 = []; for (let m = 1; m <= 17; m++) N2.push(2 ** m);
for (const [key, Ns] of [['faure5', N5], ['res5', N5], ['sobol', N2]]) {
  const ev = SQ.sepEvents(key, Ns[Ns.length - 1]); out[key] = { N: Ns, sep: Ns.map(N => SQ.sepAt(ev, N).c) };
}
const med = [];
for (const N of N5) {
  const v = [];
  for (let seed = 1; seed <= 41; seed++) { SQ.addNet('r', { kind: 'random', s: 2, seed }); v.push(SQ.sepAt(SQ.sepEvents('r', N), N).c); }
  v.sort((a, b) => a - b); med.push(v[20]);
}
out.rand = { N: N5, sep: med };
fs.writeFileSync(path.join(__dirname, 'step01_checkpoints.json'), JSON.stringify(out));
for (const k in out) console.log(k, out[k].sep.map(x => x.toFixed(4)).join(' '));
