# gen_data.py -- data of the interactive explainers (index, residue, limits, certificate, practice): data.json and the
# reference matrices check/ref.json (read by check/crosscheck.cjs, not shipped in the pages).
# Everything comes from the builders of the paper's figures (the directory scripts/ of the paper):
#   residue / staggered residue sequences   b3_gen.py   (Definitions def:residue, def:residuestar)
#   block-periodic residue sequences        audit_gen.block_matrices (independent implementation, thm:block)
#   brick wall W^-, B2, hexagonal brick wall make_figs.py (wbuild, b2core, hlib/hverify/dlib)
# The browser regenerates the residue, staggered-residue and Faure matrices itself (src/core.js ports b3_gen.py); the
# other matrices are exported here. Exact separations quoted on the pages are recomputed here with the cell-list
# program sepx.cpp (bin/sepx of the scripts directory) and asserted against the paper's printed values. Data read from
# the scripts' data/: levels_p5.txt, drops_res31.txt, drops_fa31.txt, drops_sob{1,2,3}.txt, freediag.json.
#   run (from the repository root, after building bin/sepx as in paper/scripts/README.md):
#     uv run --no-project --with numpy --with matplotlib==3.11.0 python explainers/gen_data.py      (~5 s, foreground)
# output: data.json next to this file, check/ref.json; then build_page.py, then check/crosscheck.cjs (node).
import os, sys, json, math, time, subprocess, tempfile, re
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
for _d in (os.path.join(HERE, '..', 'paper', 'scripts'),            # deposit layout
           os.path.join(HERE, '..', 'paper', 'v4', 'scripts')):     # development layout
    if os.path.exists(os.path.join(_d, '_paths.py')):
        sys.path.insert(0, os.path.abspath(_d)); break
import _paths                                            # paths of the scripts directory (data/, bin/)
import make_figs as mf                                   # builders + law_D of the paper's figures
from b3_gen import brickwall, matrices                   # residue formulas (Section sec:residue)
from audit_gen import block_matrices                     # thm:block (independent implementation)
DATA = _paths.DATA
t0 = time.time()
out = {"nets": {}, "law": {}, "checks": {}, "sep": {}}
ref = {}

# ---------------------------------------------------------------- sepx: exact toroidal separation of a digital prefix
SEPX = _paths.exe('sepx')


def sepx(C, p, m, R=None):
    """exact sep(P_m) = delta(P_m) p^{m/s} and the closest pair (integer indices), via sepx.cpp."""
    s = len(C)
    R = R or min(len(C[0]), mf.Dfor(p) if p > 2 else 52)
    with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as f:
        f.write('%d %d %d %d\n' % (p, s, m, R))
        for c in range(s):
            for n in range(R):
                f.write(' '.join(str(int(C[c][n][k]) % p) for k in range(m)) + '\n')
        name = f.name
    o = subprocess.run([SEPX, name], capture_output=True, text=True).stdout
    os.unlink(name)
    mo = re.search(r'sep=([0-9.]+)\s+\(exact if delta<cell side: (\w+).*pair (\d+) (\d+)', o)
    assert mo and mo.group(2) == 'yes', o
    return float(mo.group(1)), int(mo.group(3)), int(mo.group(4))


def sep_brute(C, p, m, R=None):
    """exact toroidal sep(P_m) by brute force over all pairs (small N; sepx needs at least one digit per cell)."""
    s = len(C); R = R or min(len(C[0]), mf.Dfor(p)); N = p ** m
    V = np.array([[(i // p ** k) % p for k in range(m)] for i in range(N)], dtype=np.int64).T
    w = float(p) ** -(np.arange(R) + 1)
    X = np.array([w @ ((np.array([[C[c][n][k] for k in range(m)] for n in range(R)], dtype=np.int64) @ V) % p)
                  for c in range(s)])
    best = (9.0, 0, 0)
    for i in range(N - 1):
        d = np.abs(X[:, i + 1:] - X[:, [i]]); d = np.minimum(d, 1 - d); dd = (d * d).sum(0); k = int(np.argmin(dd))
        if dd[k] < best[0]: best = (float(dd[k]), i, i + 1 + k)
    return math.sqrt(best[0]) * N ** (1 / s), best[1], best[2]


def tr4(x): return math.floor(x * 1e4 + 1e-9) / 1e4   # truncation as in the paper (sec:conventions)


def export(key, C, q, D, M, label, **extra):
    Cs = [[[int(C[c][n][k]) % q for k in range(M)] for n in range(D)] for c in range(len(C))]
    out["nets"][key] = dict(q=q, s=len(C), D=D, M=M, label=label, C=Cs, **extra)


# ---------------------------------------------------------------- 1. brick wall W^- (p = 7: running example; p = 13: fig:residue(a))
wfB = brickwall(7, 21, 40)
assert [r[:4] for r in wfB[0][:4]] == [[1, 0, 0, 0], [6, 2, 0, 0], [5, 2, 4, 0], [0, 1, 5, 1]]       # ex:running
assert [r[:4] for r in wfB[1][:4]] == [[2, 2, 2, 2], [4, 0, 3, 6], [3, 1, 0, 0], [6, 1, 2, 0]]
wfM = mf.mats_wf(7, 40)                                  # v3 builder (wbuild) -- must be the same sequence
assert all(int(wfM['C'][c][n][k]) % 7 == wfB[c][n][k] for c in range(2) for n in range(18) for k in range(36))
export("wf7", wfB, 7, 18, 16, "brick wall W⁻, base 7")
# laws: carry responses D(l) at levels 19 and 20 (prop:law: the same at every level), tab:running
def lawlist(net, K, L, j=1):
    A = mf.law_D(net, K, L, j)
    return [[[[int(A[l, i, c, cp]) for cp in range(2)] for c in range(2)] for i in range(j)] for l in range(1, L + 1)]
W1 = lawlist(wfM, 19, 18); assert W1 == lawlist(wfM, 20, 18)
assert [W1[l][0][0][0] for l in range(8)] == [4, 1, 3, 6, 6, 6, 4, 5]          # tab:running, O_0
assert [W1[l][0][1][0] for l in range(8)] == [4] * 8                          # X_{1<-0} = 1/2
assert [W1[l][0][1][1] for l in range(8)] == [0] * 8                          # O_1 = 0
assert [W1[l][0][0][1] for l in range(8)] == [1, 5, 4, 4, 4, 0, 2, 6]          # X_{0<-1}
out["law"]["wf7"] = W1
# W^- p = 13: thm:WF bound (p-3)/(2p) = 5/13; fig:residue(a) exact sep(P_2) = .4726 (also at m = 4)
wf13 = brickwall(13, 14, 6)
for m in (2, 4):
    v, i, j = sepx(wf13, 13, m); out["sep"][f"wf13_m{m}"] = [v, i, j]
    assert round(v, 4) == 0.4726, (m, v)
wf5 = brickwall(5, 22, 12)
ref["wf5"] = wf5; ref["wf13"] = wf13; ref["wf7"] = wfB
print(f"brick wall ok ({time.time() - t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- 2. Faure (I, P): tab:faure, fig:carry
fa7 = mf.mats_faure(7, 40)
export("faure7", fa7['C'], 7, 18, 12, "Faure (I, P), base 7")
FL = {K: lawlist(fa7, K, K) for K in range(1, 9)}
# depth-one cross coefficient (-1)^K (K+1) of ex:faurelaw = X^{(2)} - X^{(1)} of coordinate 0 <- 1, tab:faure row 2
dep1 = [(FL[K][1][0][0][1] - FL[K][0][0][0][1]) % 7 for K in range(2, 9)]
assert dep1 == [3, 3, 5, 1, 0, 6, 2], dep1
out["law"]["faure7"] = {str(K): FL[K] for K in FL}
for m, val in ((2, .8690), (4, .3115), (6, .2463)):                            # tab:faure, sep(P_2K)
    v, _, _ = sepx(fa7['C'], 7, m); assert round(v, 4) == val, (m, v); out["sep"][f"faure7_m{m}"] = v
fa5 = mf.mats_faure(5, 22)
v, i, j = sepx(fa5['C'], 5, 5); assert round(v, 4) == 0.0738, (v, i, j)   # fig:carry (several pairs attain it; (1, 3120) is one)
out["sep"]["faure5_m5"] = [v, i, j]
ref["faure5"] = [[[int(x) for x in r[:10]] for r in Cc[:22]] for Cc in fa5['C']]
# rem:faurerate pair (p = 5, Q = 5): V1 = -(z + ... + z^{Q-1}), V2 = V1 + (z-1)^{Q-1}; indices 3120 and 1
print(f"faure ok ({time.time() - t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- 3. B2 (certificate page: lem:octave, thm:B2)
b2 = mf.mats_b2(D=64)
export("b2", b2['C'], 2, 32, 20, "base-2 sequence of thm:B2")
v, _, _ = sepx(b2['C'], 2, 12, R=40); assert round(v, 4) == 0.3968, v      # exact sep(P_12) (fig:B2)
NT = 700
def mul2(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r & ((1 << NT) - 1)
def inv2(a):
    r = 1
    for n in range(1, NT):
        if (mul2(a, r) >> n) & 1: r |= 1 << n
    return r
u = 0; k = 1
while k < NT: u |= 1 << k; k *= 2
g0 = mul2(3, 1 ^ u); g1 = u >> 1
Mx = [[g0, mul2(g0, u)], [g1, mul2(g1, 1 ^ u)]]
dinv = inv2(mul2(g0, g1))
Gx = [[mul2(dinv, Mx[1][1]), mul2(dinv, Mx[0][1])], [mul2(dinv, Mx[1][0]), mul2(dinv, Mx[0][0])]]
inv1x = (1 << NT) - 1
Gh = [[mul2(Gx[a][b], inv1x) for b in range(2)] for a in range(2)]
bit = lambda s_, n: (s_ >> n) & 1
def D2(i, l):                                            # D_i(l) = I - sum_{a<=i} M_a Ghat_{l+i-a} (prop:law)
    Rm = [[1, 0], [0, 1]]
    for a in range(i + 1):
        for c in range(2):
            for b_ in range(2):
                Rm[c][b_] ^= sum(bit(Mx[c][t], a) & bit(Gh[t][b_], l + i - a) for t in range(2)) & 1
    return Rm
B2law = [[D2(i, l) for i in range(12)] for l in range(1, 161)]
Dlin, _ = mf.b2core.law(mf.b2core.B2, 72, 12)
for l in range(1, 71):
    for c in range(2):
        for src in range(2):
            assert Dlin(c, src, l) == [B2law[l - 1][i][c][src] for i in range(12)], (l, c, src)
tuples = {json.dumps(B2law[l - 1]) for l in range(1, 64)}
assert len(tuples) == 35                                 # lem:octave: 35 distinct 12-digit tuples
assert all(json.dumps(B2law[l - 1]) in tuples for l in range(64, 161))
out["law"]["b2"] = B2law
print(f"B2 ok ({time.time() - t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- 4. residue sequences: exact values of the paper
# 2D, p = 11, places (0,1), theta = 1, v = (3,-1) (fig:residue(b,c)): sep(P_3) = .7651, sep(P_5) = .6238
R11 = matrices('U', 11, [0, 1], 1, 15, 8, v=[3, 10])
for m, val in ((3, .7651), (5, .6238)):
    v, i, j = sepx(R11, 11, m); assert round(v, 4) == val, (m, v); out["sep"][f"res11_m{m}"] = [v, i, j]
# 3D, p = 11, places (0,1,2), theta = 1, v = (9,4,-1) (rem:residueexact): sep(P_2) = .7686, sep(P_5) = .6144
R311 = matrices('U', 11, [0, 1, 2], 1, 15, 6, v=[9, 4, 10])
for m, val in ((2, .7686), (5, .6144)):
    v, i, j = (sepx if m >= 3 else sep_brute)(R311, 11, m); assert round(v, 4) == val, (m, v)
    out["sep"][f"res311_m{m}"] = [v, i, j]
# 2D, p = 5, Korobov v = (2,-1): the fig:levels(b) column (data/levels_p5.txt), spot-check m = 3, 10
R5 = matrices('U', 5, [0, 1], 1, 22, 10, v=[2, 4])
lv = [l.split() for l in open(os.path.join(DATA, 'levels_p5.txt')) if l[0].isdigit()]
out["levels_p5"] = [[int(r[0]), float(r[1]), float(r[2]), float(r[3])] for r in lv]
v, _, _ = sepx(R5, 5, 3); assert abs(v - out["levels_p5"][2][1]) < 1e-4, v
v, _, _ = sepx(R5, 5, 10); assert round(v, 4) == 0.2460, v
assert [r[3] for r in out["levels_p5"] if r[0] in (9,)] == [0.0920]       # fig:levels caption: block .092 at m = 9
ref["res"] = []
for (p, a, th, vv, rows, cols) in ((11, [0, 1], 1, [3, 10], 14, 8), (5, [0, 1], 1, [2, 4], 22, 10),
                                   (11, [0, 1, 2], 1, [9, 4, 10], 14, 6), (13, [2, 9, 10], 12, [5, 3, 6], 14, 7),
                                   (31, [8, 0, 16], 9, [10, 30, 7], 10, 5), (17, [0, 1, 2, 3], 1, [9, 15, 4, 16], 8, 5)):
    ref["res"].append(dict(p=p, a=a, theta=th, v=vv, C=matrices('U', p, a, th, rows, cols, v=vv)))
ref["stag"] = []
for (p, a, th, cst, mu, rows, cols) in ((13, [0, 1, 2], 1, 2, None, 10, 8), (7, [0, 1], (-pow(4, 5, 7)) % 7, 1, [3, 2], 18, 8)):
    if mu is None:                                       # dyadic weights k = (1/4, 1/2), mu_* = 1, mu_c = -1/k_c
        k_ = [pow(4, p - 2, p), pow(2, p - 2, p)]; mu = [(-pow(k_[0], p - 2, p)) % p, (-pow(k_[1], p - 2, p)) % p, 1]
    ref["stag"].append(dict(p=p, a=a, theta=th, cstar=cst, mu=mu, C=matrices('R', p, a, th, rows, cols, cstar=cst, mu=mu)))
print(f"residue ok ({time.time() - t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- 5. block-periodic residue sequences, thm:block(a)
Fd = [[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]]
blk = {}
for p in (3, 5, 7):
    D = mf.Dfor(p)
    Cb, vals = block_matrices(p, 2, 2, [0, 1], 1, [1, 1], Fd, None, rows=D, cols=8)
    assert vals == [[1, 0], [1, 0]]
    blk[p] = Cb
    export(f"block{p}", Cb, p, D, 8, f"block-periodic residue sequence, base {p}", LB=1 - 2 / p)
ref["block5"] = blk[5]
# exact values (rem:blockexact, fig:block): p=3: P_4 .5730, P_8 .3862; p=5: P_4 = P_8 = .6237, P_6 .159; p=7: P_4 .7613,
# P_6 .1117, P_8 .7416 with the pair (1085326, 4241291)
for p, m, val in ((3, 4, .5730), (3, 8, .3862), (5, 4, .6237), (5, 6, .1585), (5, 8, .6237), (7, 4, .7613), (7, 6, .1117),
                  (7, 8, .7416)):
    v, i, j = sepx(blk[p], p, m); assert round(v, 4) == val, (p, m, v)
    out["sep"][f"block{p}_m{m}"] = [v, i, j]
assert set(out["sep"]["block7_m8"][1:]) == {1085326, 4241291}
print(f"block ok ({time.time() - t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- 6. hexagonal brick wall, p = 401, (b, e) = (5, 1) (thm:HB, fig:HB)
hb = mf.mats_window(401, mf.Dfor(401), 'hb', 5, 1)
assert math.floor(hb['LB'] * 1e4) / 1e4 == 0.9054, hb['LB']
export("hb401", hb['C'], 401, mf.Dfor(401), 4, "hexagonal brick wall, base 401", LB=hb['LB'])
v, i, j = sepx(hb['C'], 401, 2, R=mf.Dfor(401)); assert round(v, 4) == 0.9922, v
out["sep"]["hb401_m2"] = [v, i, j]
print(f"hexagonal brick wall ok ({time.time() - t0:.1f}s)", flush=True)

# ---------------------------------------------------------------- 7. Sobol' close pairs (cor:sobol, tab:sobolpar), exact
def sobol_dirs(poly, init, K):
    """direction numbers u_1..u_K (Sobol's recurrence eq:sobrec); poly = [1, a_1, ..., a_{e-1}, 1] (degree e)."""
    e = len(poly) - 1; u = [0] + list(init)
    for k in range(e + 1, K + 1):
        x = u[k - e] ^ (u[k - e] << e)
        for i in range(1, e): x ^= (poly[i] * u[k - i]) << i
        u.append(x)
    return u
def sobol_point(V, dirs, R):                             # coordinate as an integer in units of 2^-R
    y = 0; k = 1
    while V:
        if V & 1: y ^= dirs[k] << (R - k)
        V >>= 1; k += 1
    return y
def pmul2(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def pmod2(a, m):
    dm = m.bit_length()
    while a and a.bit_length() >= dm: a ^= m << (a.bit_length() - dm)
    return a
def subst(T, e):                                         # Theta(z^e)
    r = 0; i = 0
    while T:
        if T & 1: r |= 1 << (i * e)
        T >>= 1; i += 1
    return r
SOB = []                                                 # (s, Q, L, m, V1, V2, dist * 2^L, sep upper value)
for s_, polys in ((2, [0b11]), (3, [0b11, 0b111])):
    degs = [P.bit_length() - 1 for P in polys]
    E = 1
    for d in degs: E = E * d // math.gcd(E, d)
    Th = 1
    for P, d in zip(polys, degs):
        for _ in range(E // d): Th = pmul2(Th, P)
    Rm = pmul2(0b11, Th); nu = 1
    while pmod2((1 << nu) ^ 1, Rm): nu += 1
    j = 0
    while (1 << j) < nu: j += 1
    eta = E * ((1 << j) + 1) - nu
    inits = {0b11: [1], 0b111: [1, 3]}                   # Joe-Kuo initial direction numbers (dims 2, 3)
    for Q in ((1, 2, 4, 8) if s_ == 2 else (1,)):
        L = Q * E * ((1 << j) + 1); m = Q * (s_ * E * ((1 << j) + 1) - (s_ - 1) * E)
        S = (1 << (Q * nu)) - 1                          # 1 + z + ... + z^{Q nu - 1}
        Dq = pmul2(pmul2(1 << (Q * eta), S), subst(Th, (1 << j) * Q))
        V1 = (1 << L) - (1 << (Q * eta + 1)); V2 = V1 ^ Dq
        assert Dq.bit_length() <= m and V2 < (1 << m)
        Rb = m + 8; d2 = 0
        dirs_vdc = [0] + [1] * (Rb + 2)
        coords = [dirs_vdc] + [sobol_dirs([int(b) for b in bin(P)[2:]][::-1], inits[P], Rb + 2) for P in polys]
        for dirs in coords:
            a_, b_ = sobol_point(V1, dirs, Rb), sobol_point(V2, dirs, Rb); d2 += (a_ - b_) ** 2
        dist_scaled = math.sqrt(d2) / 2 ** (Rb - L)       # distance * 2^L
        assert dist_scaled < math.sqrt(s_ + 3), (s_, Q, dist_scaled)
        sepv = dist_scaled * 2 ** (m / s_ - L)
        SOB.append(dict(s=s_, Q=Q, L=L, m=m, nu=nu, k=1 << j, V1=str(V1), V2=str(V2), dscaled=dist_scaled, sep=sepv,
                        bound=math.sqrt(s_ + 3) * 2 ** (-Q * (s_ - 1) * E / s_)))
    if s_ == 2: assert (nu, 1 << j, eta) == (2, 2, 1)
    else: assert (nu, 1 << j, E) == (12, 16, 2)          # tab:sobolpar row s = 3
assert SOB[0]['V1'] == '4' and SOB[0]['V2'] == '26' and SOB[-1]['L'] == 34 and SOB[-1]['m'] == 98
out["sobolpairs"] = SOB
print(f"Sobol' pairs ok ({time.time() - t0:.1f}s)", SOB[-1], flush=True)

# ---------------------------------------------------------------- 8. practice (tab:practice, fig:evidence): drop events, J
def drops(fn):
    ev = [l.split() for l in open(fn) if l.strip() and l[0].isdigit()]
    return [[int(a), math.sqrt(float(b))] for a, b in ev]
def Jof(ev, N0=64, N1=2 ** 23, s_=3):
    best = (9, 0)
    for k, (N, d) in enumerate(ev):
        Nn = ev[k + 1][0] - 1 if k + 1 < len(ev) else N1
        if Nn < N0 or N > N1: continue
        a = max(N, N0); c = d * a ** (1 / s_)
        if c < best[0]: best = (c, a)
    return best
FB = DATA
out["practice"] = {"res31": drops(os.path.join(DATA, 'drops_res31.txt')),
                   "fa31": drops(os.path.join(FB, 'drops_fa31.txt'))}
for k_ in (1, 2, 3): out["practice"][f"sob{k_}"] = drops(os.path.join(FB, f'drops_sob{k_}.txt'))
J = {k_: Jof(v) for k_, v in out["practice"].items()}
assert round(J['res31'][0], 3) == 0.267 and J['res31'][1] == 208652, J['res31']     # tab:practice / fig:evidence
assert round(J['fa31'][0], 3) == 0.095 and J['fa31'][1] == 53879, J['fa31']
sj = sorted(round(J[f'sob{k_}'][0], 3) for k_ in (1, 2, 3)); assert sj[0] == 0.015 and sj[-1] == 0.039, sj
out["checks"]["J"] = {k_: [round(v[0], 6), v[1]] for k_, v in J.items()}
print(f"practice ok ({time.time() - t0:.1f}s)", J, flush=True)

# ---------------------------------------------------------------- free diagonal of thm:block(d) vs U*_s (b8_freediag_data.py)
out["freediag"] = json.load(open(os.path.join(DATA, "freediag.json")))
assert out["freediag"]["A"] == {"4": 3, "5": 7, "6": 14, "7": 59}

json.dump(out, open(os.path.join(HERE, "data.json"), "w"), separators=(",", ":"))
os.makedirs(os.path.join(HERE, 'check'), exist_ok=True)
json.dump(ref, open(os.path.join(HERE, 'check', 'ref.json'), 'w'), separators=(",", ":"))
print(f"wrote data.json ({os.path.getsize(os.path.join(HERE, 'data.json')) // 1024} KB) and check/ref.json "
      f"({time.time() - t0:.1f}s)")
