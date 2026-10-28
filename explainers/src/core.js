/* core.js -- shared math + drawing helpers of the geoseq explainers (inlined into every page by build_page.py).
   Point sets are rebuilt here from generator matrices: digit n of coordinate c of the point with index digits v_k is
   y_{c,n} = sum_k C_c[n][k] v_k (mod q), and y_c = sum_n y_{c,n} q^{-n-1} (prime q). Some matrices are exported by
   gen_data.py from the paper's builders; the residue, staggered-residue and Faure matrices are generated here by a port
   of paper/v4/figs/b3_gen.py (checked entry by entry against it by check/crosscheck.mjs). Distances are toroidal.
   No DOM access at load time except window listeners, so node can run the math (check/crosscheck.mjs). */
const SQ = (() => {
  const DATA = (typeof window !== 'undefined' && window.__SQDATA) || {};
  const nets = DATA.nets || {};

  // ------------------------------------------------------------------ F_p arithmetic and truncated power series
  const mod = (x, p) => ((x % p) + p) % p;
  function inv(x, p) { x = mod(x, p); let r = 1, b = x, e = p - 2; while (e > 0) { if (e & 1) r = r * b % p; b = b * b % p; e >>= 1; } return r; }
  function smul(A, B, R, p) {
    const C = new Array(R).fill(0);
    for (let i = 0; i < Math.min(R, A.length); i++) { const a = A[i]; if (!a) continue; for (let j = 0; j < Math.min(B.length, R - i); j++) C[i + j] = (C[i + j] + a * B[j]) % p; }
    return C;
  }
  function sinv(A, R, p) {
    const i0 = inv(A[0], p), B = new Array(R).fill(0); B[0] = i0;
    for (let n = 1; n < R; n++) { let s = 0; for (let k = 1; k <= Math.min(n, A.length - 1); k++) s += A[k] * B[n - k]; B[n] = mod(-(s % p) * i0, p); }
    return B;
  }
  function Wc(a, c, R, p) {                               // w_c(z) = prod_{b != c}(z - a_b) as a series in t = z - a_c
    let W = [1].concat(new Array(R - 1).fill(0));
    for (let b = 0; b < a.length; b++) if (b !== c) W = smul(W, [mod(a[c] - a[b], p), 1], R, p);
    return W;
  }
  // Definition def:residue (kind 'U') and def:residuestar (kind 'R'), exactly as paper/v4/figs/b3_gen.py:
  //   R_v : C_c[n][i] = v_c^{-1} th^{n+1} [t^n] (t+a_c)^i / W_c(t)^{n+1}
  //   R*_v: C_c[n][i] = mu_c th^{n+1} [t^n] (t+a_c)^i / ((t+a_c-a_*) W_c(t)^{n+1}) (c != c*),  C_*[n][i] = mu_* th^n [t^n] (t+a_*)^i / W_*(t)^n
  function residueMatrices(kind, p, a, theta, rows, cols, opt) {
    const s = a.length, R = rows, th = mod(theta, p), C = [];
    for (let c = 0; c < s; c++) {
      const Winv = sinv(Wc(a, c, R, p), R, p), lin = [mod(a[c], p), 1];
      const colS = [[1].concat(new Array(R - 1).fill(0))];
      for (let i = 1; i < cols; i++) colS.push(smul(colS[i - 1], lin, R, p));
      const M = Array.from({ length: rows }, () => new Array(cols).fill(0));
      let ker = [1].concat(new Array(R - 1).fill(0)), extra = null, base;
      if (kind === 'U') base = 1;
      else if (c === opt.cstar) base = 0;
      else { extra = sinv([mod(a[c] - a[opt.cstar], p), 1], R, p); base = 1; }
      for (let e = 0; e < base; e++) ker = smul(ker, Winv, R, p);
      let thp = 1; for (let e = 0; e < base; e++) thp = thp * th % p;
      const sc = kind === 'U' ? inv(opt.v[c], p) : mod(opt.mu[c], p);
      for (let n = 0; n < rows; n++) {
        const kk = extra ? smul(ker, extra, R, p) : ker, f = sc * thp % p;
        for (let i = 0; i < cols; i++) { const col = colS[i]; let acc = 0; for (let j = 0; j <= n; j++) if (col[j] && kk[n - j]) acc += col[j] * kk[n - j]; M[n][i] = f * (acc % p) % p; }
        ker = smul(ker, Winv, R, p); thp = thp * th % p;
      }
      C.push(M);
    }
    return C;
  }
  const residue = (p, a, theta, v, rows, cols) => residueMatrices('U', p, a, theta, rows, cols, { v });
  const staggered = (p, a, theta, cstar, mu, rows, cols) => residueMatrices('R', p, a, theta, rows, cols, { cstar, mu });
  function brickwall(p, rows, cols) { return staggered(p, [0, 1], mod(-inv(4, p), p), 1, [mod(-4, p), 2], rows, cols); }
  function pascal(a, p, rows, cols) {                     // Pas_a[n][k] = binom(k, n) a^{k-n}
    const M = Array.from({ length: rows }, () => new Array(cols).fill(0));
    const B = [[1]]; for (let k = 1; k < cols; k++) { const r = [1]; for (let n = 1; n < k; n++) r.push((B[k - 1][n - 1] + B[k - 1][n]) % p); r.push(1); B.push(r); }
    for (let n = 0; n < rows; n++) for (let k = n; k < cols; k++) { let x = B[k][n]; for (let e = 0; e < k - n; e++) x = x * mod(a, p) % p; M[n][k] = x; }
    return M;
  }
  const faure = (p, s, rows, cols) => Array.from({ length: s }, (_, c) => pascal(c, p, rows, cols));
  const Dfor = q => Math.floor(52 / Math.log2(q));       // digits kept per coordinate: q^D < 2^52 (exact in float64)

  // ------------------------------------------------------------------ nets: register, generate points
  function addNet(key, obj) { nets[key] = Object.assign({ s: obj.C ? obj.C.length : obj.s }, obj); delete cache[key]; delete evCache[key]; return nets[key]; }
  function mulberry(seed) { let a = seed >>> 0; return () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
  function hash32(a, b, c, d) {                          // integer hash (for the Owen scramble)
    let h = Math.imul(a ^ 0x9e3779b9, 0x85ebca6b) ^ Math.imul(b + 0x7f4a7c15, 0xc2b2ae35) ^ Math.imul(c + 0x165667b1, 0x27d4eb2f) ^ Math.imul(d + 0x61c88647, 0x9e3779b1);
    h ^= h >>> 16; h = Math.imul(h, 0x85ebca6b); h ^= h >>> 13; h = Math.imul(h, 0xc2b2ae35); h ^= h >>> 16; return h >>> 0;
  }
  function sobolDirs(poly, init, K) {                    // eq:sobrec, poly = [1, a_1, .., a_{e-1}, 1]; returns u_1..u_K (index 1..K)
    const e = poly.length - 1, u = [0].concat(init);
    for (let k = e + 1; k <= K; k++) { let x = u[k - e] ^ (u[k - e] * Math.pow(2, e)); for (let i = 1; i < e; i++) if (poly[i]) x ^= u[k - i] * Math.pow(2, i); u.push(x); }
    return u;
  }
  function sobol3Matrices(D) {                           // van der Corput, z+1, z^2+z+1 (Joe-Kuo init 1, 3): C[n][k] = bit n of 2^{-(k+1)} u_{k+1}
    const dirs = [null, sobolDirs([1, 1], [1], D), sobolDirs([1, 1, 1], [1, 3], D)];
    return [0, 1, 2].map(c => Array.from({ length: D }, (_, n) => Array.from({ length: D }, (_, k) => {
      if (c === 0) return +(n === k);
      const u = dirs[c][k + 1]; const sh = k - n; return sh < 0 ? 0 : (Math.floor(u / Math.pow(2, sh)) & 1);
    })));
  }
  const cache = {};
  function points(key, N) {
    const c0 = cache[key]; if (c0 && c0.N >= N) return c0;
    const nt = nets[key], s = nt.s, X = Array.from({ length: s }, () => new Float64Array(N));
    if (nt.kind === 'random') {
      const rnd = mulberry(nt.seed || 1); for (let i = 0; i < N; i++) for (let c = 0; c < s; c++) X[c][i] = rnd();
    } else if (nt.kind === 'halton') {
      for (let c = 0; c < s; c++) { const b = nt.bases[c]; for (let i = 0; i < N; i++) { let v = i, f = 1 / b, x = 0; while (v > 0) { x += (v % b) * f; v = Math.floor(v / b); f /= b; } X[c][i] = x; } }
    } else {                                              // digital over F_q (prime q), optional Owen scramble (q = 2)
      const q = nt.q, D = nt.D, C = nt.C;
      let m = 1; while (Math.pow(q, m) < N) m++;
      if (m > nt.M) throw new Error(key + ': prefix too long for exported columns');
      const S = C.map(Cc => Cc.slice(0, D).map(row => { const r = new Int32Array(m); let a = 0; for (let k = 0; k < m; k++) { a = (a + row[k]) % q; r[k] = a; } return r; }));
      const y = Array.from({ length: s }, () => new Int32Array(D)), vd = new Int32Array(m + 1);
      const pw = new Float64Array(D); pw[0] = 1 / q; for (let n = 1; n < D; n++) pw[n] = pw[n - 1] / q;
      const owen = nt.owen != null;
      for (let v = 0; v < N; v++) {
        if (v > 0) { let k = 0; while (vd[k] === q - 1) { vd[k] = 0; k++; } vd[k]++; for (let c = 0; c < s; c++) { const Sc = S[c], yc = y[c]; for (let n = 0; n < D; n++) { const t = yc[n] + Sc[n][k]; yc[n] = t >= q ? t - q : t; } } }
        for (let c = 0; c < s; c++) {
          const yc = y[c]; let val = 0;
          if (owen) { let pre = 1; for (let n = 0; n < D; n++) { const b = yc[n] ^ (hash32(nt.owen, c, n, pre) & 1); pre = (pre * 2 + yc[n]) >>> 0; if (b) val += pw[n]; } }
          else if (nt.shift) { const sh = nt.shift[c]; for (let n = 0; n < D; n++) { const t = (yc[n] + sh[n]) % q; if (t) val += t * pw[n]; } }
          else for (let n = 0; n < D; n++) if (yc[n]) val += yc[n] * pw[n];
          X[c][v] = val;
        }
      }
    }
    return (cache[key] = { N, X, s, x: X[0], y: X[1], z: X[2] });
  }
  function td2(P, i, j) { let d2 = 0; for (let c = 0; c < P.s; c++) { let d = Math.abs(P.X[c][i] - P.X[c][j]); if (d > 0.5) d = 1 - d; d2 += d * d; } return d2; }

  // ------------------------------------------------------------------ exact delta of EVERY prefix (incremental cell list, s = 2, 3)
  // delta(P_[N]) = min(delta(P_[N-1]), distance of point N-1 to its nearest predecessor); only the drops are stored.
  const evCache = {};
  function sepEvents(key, N) {
    const e0 = evCache[key]; if (e0 && e0.N >= N) return e0;
    const P = points(key, N), s = P.s, X = P.X;
    const G = Math.max(3, Math.floor(s === 2 ? Math.sqrt(N) / 1.5 : Math.cbrt(N) / 1.3)), Gs = Math.pow(G, s);
    const head = new Int32Array(Gs).fill(-1), next = new Int32Array(N).fill(-1);
    const bin = (i, c) => Math.min(G - 1, Math.floor(X[c][i] * G));
    const cellOf = i => { let id = 0; for (let c = 0; c < s; c++) id = id * G + bin(i, c); return id; };
    const evN = [], evD = [], evI = [], evJ = [];
    let best = Infinity;
    const ins = i => { const b = cellOf(i); next[i] = head[b]; head[b] = i; };
    ins(0);
    const cc = new Int32Array(s);
    for (let i = 1; i < N; i++) {
      const r = isFinite(best) ? Math.ceil(Math.sqrt(best) * G) + 1 : G;
      let nb = best, nj = -1;
      if (2 * r + 1 >= G) { for (let j = 0; j < i; j++) { const d = td2(P, i, j); if (d < nb) { nb = d; nj = j; } } }
      else {
        for (let c = 0; c < s; c++) cc[c] = bin(i, c);
        if (s === 2) {
          for (let a = -r; a <= r; a++) { const gx = ((cc[0] + a) % G + G) % G; for (let b = -r; b <= r; b++) { let j = head[gx * G + ((cc[1] + b) % G + G) % G]; while (j >= 0) { const d = td2(P, i, j); if (d < nb) { nb = d; nj = j; } j = next[j]; } } }
        } else {
          for (let a = -r; a <= r; a++) { const gx = ((cc[0] + a) % G + G) % G; for (let b = -r; b <= r; b++) { const gy = ((cc[1] + b) % G + G) % G; for (let e = -r; e <= r; e++) { let j = head[(gx * G + gy) * G + ((cc[2] + e) % G + G) % G]; while (j >= 0) { const d = td2(P, i, j); if (d < nb) { nb = d; nj = j; } j = next[j]; } } } }
        }
      }
      if (nj >= 0) { best = nb; evN.push(i + 1); evD.push(Math.sqrt(nb)); evI.push(nj); evJ.push(i); }
      ins(i);
    }
    return (evCache[key] = { N, evN, evD, evI, evJ, s });
  }
  function sepAt(ev, N) {                                  // delta, closest pair and sep = delta N^{1/s} of the first N points
    let lo = 0, hi = ev.evN.length - 1;
    while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (ev.evN[mid] <= N) lo = mid; else hi = mid - 1; }
    return { d: ev.evD[lo], i: ev.evI[lo], j: ev.evJ[lo], c: ev.evD[lo] * Math.pow(N, 1 / (ev.s || 2)) };
  }
  function minSepRange(ev, N0, N1) {                       // min over N0 <= N <= N1 of sep(P_[N]) (exact: sep rises between drops)
    const s = ev.s || 2; let best = Infinity, at = 0;
    for (let k = 0; k < ev.evN.length; k++) {
      const a = ev.evN[k], b = k + 1 < ev.evN.length ? ev.evN[k + 1] - 1 : Infinity;
      if (b < N0 || a > N1) continue; const n = Math.max(a, N0), c = ev.evD[k] * Math.pow(n, 1 / s);
      if (c < best) { best = c; at = n; }
    }
    return { c: best, N: at };
  }
  // exact closest pair of a static set (first N points of P): cell list with ~1 point per cell, radius grown until exact
  function closest(P, N) {
    const s = P.s, X = P.X; let G = Math.max(1, Math.floor(Math.pow(N, 1 / s)));
    let best = Infinity, bi = 0, bj = 1;
    for (let pass = 0; pass < 6; pass++) {
      const r = pass === 0 ? 1 : Math.ceil(Math.sqrt(best) * G);
      if (2 * r + 1 >= G) {                               // brute force
        for (let i = 0; i < N; i++) for (let j = i + 1; j < N; j++) { const d = td2(P, i, j); if (d < best) { best = d; bi = i; bj = j; } }
        return { d: Math.sqrt(best), i: bi, j: bj };
      }
      const Gs = Math.pow(G, s), head = new Int32Array(Gs).fill(-1), next = new Int32Array(N);
      const cell = new Int32Array(N * s);
      for (let i = 0; i < N; i++) { let id = 0; for (let c = 0; c < s; c++) { const b = Math.min(G - 1, Math.floor(X[c][i] * G)); cell[i * s + c] = b; id = id * G + b; } next[i] = head[id]; head[id] = i; }
      const offs = []; const rec = (pre, d) => { if (d === s) { offs.push(pre.slice()); return; } for (let a = -r; a <= r; a++) { pre.push(a); rec(pre, d + 1); pre.pop(); } }; rec([], 0);
      for (let i = 0; i < N; i++) for (const o of offs) {
        let id = 0; for (let c = 0; c < s; c++) id = id * G + (((cell[i * s + c] + o[c]) % G) + G) % G;
        let j = head[id]; while (j >= 0) { if (j > i) { const d = td2(P, i, j); if (d < best) { best = d; bi = i; bj = j; } } j = next[j]; }
      }
      if (Math.sqrt(best) * G <= r) return { d: Math.sqrt(best), i: bi, j: bj };
    }
    return { d: Math.sqrt(best), i: bi, j: bj };
  }

  // ------------------------------------------------------------------ F_p linear algebra: graph form of a 2D full level
  function invMod(A, p) {
    const n = A.length, M = A.map((r, i) => r.slice().concat(Array.from({ length: n }, (_, j) => +(i === j))));
    for (let col = 0; col < n; col++) {
      let piv = col; while (piv < n && M[piv][col] % p === 0) piv++;
      if (piv === n) throw new Error('singular');
      [M[col], M[piv]] = [M[piv], M[col]];
      const f = inv(M[col][col], p); for (let j = 0; j < 2 * n; j++) M[col][j] = M[col][j] * f % p;
      for (let r = 0; r < n; r++) if (r !== col && M[r][col]) { const g = M[r][col]; for (let j = 0; j < 2 * n; j++) M[r][j] = mod(M[r][j] - g * M[col][j], p); }
    }
    return M.map(r => r.slice(n));
  }
  const solvers = {};
  function level(key, K) {                                 // the level-K graph form of a 2D net (prime q): cell -> point
    const id = key + ':' + K; if (solvers[id]) return solvers[id];
    const nt = nets[key], q = nt.q, m = 2 * K, C = nt.C;
    if (m > nt.M || K + 2 > nt.D) throw new Error('level too deep for exported matrices');
    const B = []; for (let c = 0; c < 2; c++) for (let i = 0; i < K; i++) B.push(C[c][i].slice(0, m));
    const Binv = invMod(B, q);
    const pw = []; let t = 1 / q; for (let n = 0; n < nt.D; n++) { pw.push(t); t /= q; }
    const apply = cell => { const v = []; for (let k = 0; k < m; k++) { let s = 0; for (let r = 0; r < m; r++) s += Binv[k][r] * cell[r]; v.push(s % q); } return v; };
    const g = Math.pow(q, K);
    function at(n0, n1) {                                  // the point of P_2K in cell (n0, n1): index, coordinates, digits
      n0 = mod(n0, g); n1 = mod(n1, g);
      const cell = []; for (const n of [n0, n1]) for (let i = 0; i < K; i++) cell.push(Math.floor(n / Math.pow(q, K - 1 - i)) % q);
      const v = apply(cell), y = [0, 0], dig = [[], []];
      for (let c = 0; c < 2; c++) for (let n = 0; n < nt.D; n++) { let s = 0; for (let k = 0; k < m; k++) s += C[c][n][k] * v[k]; s %= q; dig[c].push(s); y[c] += s * pw[n]; }
      let idx = 0; for (let k = m - 1; k >= 0; k--) idx = idx * q + v[k];
      return { v: idx, x: y[0], y: y[1], dig, r: [dig[0][K], dig[1][K]], n: [n0, n1] };
    }
    function law(l, cp, j = 1) {                           // carry response D_i(l)[c][cp], i < j, from the matrices
      const e = new Array(m).fill(0); for (let a = K - l; a < K; a++) e[cp * K + a] = 1;
      const v = apply(e), out = [[], []];
      for (let c = 0; c < 2; c++) for (let i = 0; i < j; i++) { let s = 0; for (let k = 0; k < m; k++) s += C[c][K + i][k] * v[k]; out[c].push(s % q); }
      return out;
    }
    return (solvers[id] = { K, q, g, at, law });
  }

  // ------------------------------------------------------------------ lattices: lambda_jit of the Construction-A lattice Lambda_v
  // lambda_jit(Lambda)^2 = min over b != 0 in Lambda of ||(|b| - 1)_+||^2 (exact integer; thm:residue). Enumeration in a box
  // [-B, B]^s grown until every vector outside it (some |b_c| >= B + 1, so value >= B^2) cannot win.
  function ljit2(v, p) {
    const s = v.length, last = inv(v[s - 1], p);
    const val = b => { let t = 0; for (const x of b) { const a = Math.abs(x) - 1; if (a > 0) t += a * a; } return t; };
    let best = (p - 1) * (p - 1), arg = [p].concat(new Array(s - 1).fill(0));
    let B = Math.max(2, Math.ceil(2 * Math.pow(p, 1 / s)) + 1);
    for (;;) {
      const b = new Array(s).fill(0);
      const rec = (d, part) => {
        if (d === s - 1) {
          let r = mod(-part * last, p); if (r > p / 2) r -= p;
          for (let x = r - Math.ceil((B + r) / p) * p; x <= B; x += p) {
            if (x < -B) continue; b[s - 1] = x;
            if (b.every(z => z === 0)) continue;
            const t = val(b); if (t < best) { best = t; arg = b.slice(); }
          }
          return;
        }
        for (let x = -B; x <= B; x++) { b[d] = x; rec(d + 1, (part + v[d] * x) % p); }
      };
      rec(0, 0);
      if (best <= B * B) return { l2: best, b: arg };
      B = Math.ceil(Math.sqrt(best)) + 1;
    }
  }

  // ------------------------------------------------------------------ the digit relaxation in one coordinate (lem:cert, rem:onedigit)
  const cen = (v, p) => { v = mod(v, p); return v > p / 2 ? v - p : v; };
  function f1(e, sigma, p) {                               // guaranteed gap in one coordinate, one geometric digit
    sigma = mod(sigma, p); let best = Infinity;
    for (let R = 0; R < p; R++) { const d = Math.abs(e * p + ((R + sigma) % p) - R); if (d < best) best = d; }
    return Math.max(0, best - 1) / p;
  }

  // ------------------------------------------------------------------ formatting + drawing helpers
  const fmt = (c, k = 4) => (c < 0 ? '−' : '') + Math.abs(c).toFixed(k);
  const fmtDown = (c, k = 4) => (Math.floor(c * Math.pow(10, k) + 1e-9) / Math.pow(10, k)).toFixed(k);   // truncate (sec:conventions)
  const fmtN = N => String(N).replace(/\B(?=(\d{3})+(?!\d))/g, ' ');
  const css = name => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  function fitCanvas(cv) {
    const r = cv.getBoundingClientRect(), dpr = Math.min(2, window.devicePixelRatio || 1);
    const w = Math.max(10, Math.round(r.width)), h = Math.max(10, Math.round(r.height));
    if (cv.width !== w * dpr || cv.height !== h * dpr) { cv.width = w * dpr; cv.height = h * dpr; }
    const ctx = cv.getContext('2d');
    if (!ctx.__safeArc) { const arc0 = ctx.arc; ctx.arc = function (x, y, r, a, b) { return arc0.call(this, x, y, Math.max(0, r), a, b); }; ctx.__safeArc = true; }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0); ctx.clearRect(0, 0, w, h);
    return { ctx, w, h };
  }
  const redrawers = [];
  function onRedraw(fn) { redrawers.push(fn); }
  let rq = 0, lastW = 0;
  function redrawAll() { cancelAnimationFrame(rq); rq = requestAnimationFrame(() => redrawers.forEach(f => f())); }
  if (typeof window !== 'undefined' && window.addEventListener) {
    window.addEventListener('resize', () => { if (window.innerWidth !== lastW) { lastW = window.innerWidth; redrawAll(); } });
    if (window.matchMedia) window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', redrawAll);
  }
  function seg(el, onPick) {                               // a group of toggle buttons with aria-pressed
    const bs = [...el.querySelectorAll('button')];
    bs.forEach(b => b.addEventListener('click', () => { bs.forEach(x => x.setAttribute('aria-pressed', String(x === b))); onPick(b.dataset.v, b); }));
    return v => bs.forEach(x => x.setAttribute('aria-pressed', String(x.dataset.v === String(v))));
  }
  const svgNS = 'http://www.w3.org/2000/svg';
  function svgEl(tag, attrs, parent) {
    const e = document.createElementNS(svgNS, tag); for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e); return e;
  }
  const later = fn => setTimeout(fn, 0);                   // let the browser paint a "computing" note first
  return { DATA, nets, mod, inv, smul, sinv, residue, staggered, brickwall, pascal, faure, sobol3Matrices, sobolDirs, Dfor, addNet,
    mulberry, points, td2, sepEvents, sepAt, minSepRange, closest, invMod, level, ljit2, cen, f1, fmt, fmtDown, fmtN, css, fitCanvas,
    onRedraw, redrawAll, seg, svgEl, later };
})();
if (typeof module !== 'undefined') module.exports = SQ;
