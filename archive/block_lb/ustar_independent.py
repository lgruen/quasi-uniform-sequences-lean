"""ustar_independent.py -- an independent implementation (written by an audit of the nets paper [Gru26geo]) of the
design U*_s defined there (def:Ustar): exact rationals; own integer kernel by unimodular column reduction; own Lagrange
lead functional; Babai rounding with ties up, kappa = +gamma_j. The places are those of [Gru26geo] (infinity, 0, 1,
..., s-2), in this order. run(s) returns (places, {place d: (rows, [E_0, ..., E_{s-2}])}), the columns of the
partial sums M^(j) of U*_s at the place d. Used by block_lb/ustar_compare.py (no command-line use; the summary
printout of the audit version, a*_s and the largest entry for s <= SMAX, is done by ustar_compare.py)."""
import sys
from fractions import Fraction as Fr
from math import gcd
def lcm(a, b): return a * b // gcd(a, b)
def rat_kernel(A, ncols):  # rational nullspace basis of rows A
    M = [r[:] for r in A]; piv = []; r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; iv = 1 / M[r][c]; M[r] = [x * iv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(ncols) if c not in piv]; B = []
    for f in free:
        v = [Fr(0)] * ncols; v[f] = Fr(1)
        for i, c in enumerate(piv): v[c] = -M[i][f]
        B.append(v)
    return B
def to_int(v):
    den = 1
    for x in v: den = lcm(den, x.denominator)
    w = [int(x * den) for x in v]; g = 0
    for x in w: g = gcd(g, x)
    return [x // g for x in w] if g else w
def int_kernel(P, N):  # basis of {x in Z^N : P x = 0} via unimodular column ops
    A = [r[:] for r in P]; U = [[int(i == j) for j in range(N)] for i in range(N)]  # columns of U track ops
    col = 0
    for row in range(len(A)):
        # gcd-reduce entries A[row][col..N-1] into column col
        while True:
            nz = [c for c in range(col, N) if A[row][c] != 0]
            if len(nz) <= 1: break
            cmin = min(nz, key=lambda c: abs(A[row][c]))
            for c in nz:
                if c != cmin:
                    f = A[row][c] // A[row][cmin]
                    for r in range(len(A)): A[r][c] -= f * A[r][cmin]
                    for r in range(N): U[r][c] -= f * U[r][cmin]
        nz = [c for c in range(col, N) if A[row][c] != 0]
        if nz:
            c = nz[0]
            for r in range(len(A)): A[r][c], A[r][col] = A[r][col], A[r][c]
            for r in range(N): U[r][c], U[r][col] = U[r][col], U[r][c]
            col += 1
    return [[U[r][c] for r in range(N)] for c in range(col, N)]
def run(s):
    n = s - 2; places = ['inf'] + list(range(n + 1)); N = s - 1
    E_all = {}; ties = 0
    for di, d in enumerate(places):
        rows = [c for c in places if c != d]
        rho, y = [], []
        for c in rows:
            if d == 'inf': rho.append(Fr(1)); y.append(Fr(c))
            elif c == 'inf': rho.append(Fr(1)); y.append(Fr(0))
            else: rho.append(Fr(1, c - d)); y.append(Fr(1, c - d))
        Es = []
        for j in range(n + 1):
            Vb = [[rho[i] * y[i] ** t for i in range(N)] for t in range(j + 1)]
            perp = [to_int(v) for v in rat_kernel(Vb, N)]
            basis = int_kernel(perp, N) if perp else [[int(i == t) for i in range(N)] for t in range(N)]
            assert len(basis) == j + 1
            def kappa(x):  # lead coeff of degree<=j interpolant through first j+1 rows
                tot = Fr(0)
                for b in range(j + 1):
                    den = rho[b]
                    for b2 in range(j + 1):
                        if b2 != b: den *= (y[b] - y[b2])
                    tot += x[b] / den
                return tot
            ks = [kappa(x) for x in basis]
            # check kappa is the lead functional on the whole vector (degree exactly <= j): interpolation consistency
            # extended gcd over rationals: gamma = gcd(nums)/lcm(dens)
            Dn = 1
            for kv in ks: Dn = lcm(Dn, kv.denominator)
            ints = [int(kv * Dn) for kv in ks]
            g, coef = 0, [0] * len(ints)
            for i, a in enumerate(ints):   # running extended gcd
                if a == 0: continue
                if g == 0: g, coef = abs(a), [0] * len(ints); coef[i] = 1 if a > 0 else -1; continue
                # g = sum coef*ints ; combine with a
                x0, x1, r0, r1 = 1, 0, g, a
                y0, y1 = 0, 1
                while r1: qq = r0 // r1; r0, r1 = r1, r0 - qq * r1; x0, x1 = x1, x0 - qq * x1; y0, y1 = y1, y0 - qq * y1
                if r0 < 0: r0, x0, y0 = -r0, -x0, -y0
                coef = [c * x0 for c in coef]; coef[i] += y0; g = r0
            v = [sum(coef[t] * basis[t][i] for t in range(len(basis))) for i in range(N)]
            assert kappa(v) == Fr(g, Dn) and g > 0
            if j == 0:
                E = v
            else:
                G = [[sum(Fr(a) * b for a, b in zip(Es[i2], Es[i1])) for i1 in range(j)] for i2 in range(j)]
                rhs = [Fr(sum(a * b for a, b in zip(Es[i1], v))) for i1 in range(j)]
                # solve G c = rhs
                Mx = [G[i][:] + [rhs[i]] for i in range(j)]
                for cc in range(j):
                    p = next(i for i in range(cc, j) if Mx[i][cc] != 0); Mx[cc], Mx[p] = Mx[p], Mx[cc]
                    iv = 1 / Mx[cc][cc]; Mx[cc] = [x * iv for x in Mx[cc]]
                    for i in range(j):
                        if i != cc and Mx[i][cc] != 0:
                            f = Mx[i][cc]; Mx[i] = [x - f * yv for x, yv in zip(Mx[i], Mx[cc])]
                cvec = [Mx[i][j] for i in range(j)]
                rnd = []
                for cv in cvec:
                    t = cv + Fr(1, 2); fl = t.numerator // t.denominator
                    if t.denominator == 1: ties += 1
                    rnd.append(fl)
                E = [v[i] - sum(rnd[t] * Es[t][i] for t in range(j)) for i in range(N)]
            Es.append(E)
        E_all[d] = (rows, Es)
    return places, E_all
