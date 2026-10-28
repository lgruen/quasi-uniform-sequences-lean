# gen.py -- audit: independent generator (written from the definitions of the paper, no search code reused).
# Block residue scramble (thm:block / thm:blocktwo):  W' = w^L/theta, germs phi_{c,b} at place a_c,
#     y_{c,Ln+b}(V) = Res_{a_c}( V phi_{c,b} W'^{-(n+1)} dz ),   C_c[Ln+b][k] = [t^{L(n+1)-1}] (a_c+t)^k phi_{c,b}(t) What_c(t)^{-n-1}
# with W'(a_c+t) = t^L What_c(t).  Germs:
#   unit germs  b = L-s+1..L-1 :  (phi_{c,b})_b = B_c^{-1} (u_i)_{i!=c},  B_c[i][b] = -v_i F_{L-1-b}[i][c],  u_i = 1/(z-a_i)
#   skeleton    b = 1..L-s     :  phi_{c,b} = w^{L-1-b} / v'_c
#   own         b = 0          :  phi_{c,0} (1 - F_{L-1}[c][c] W') = W'/(v_c (z-a_c)) + W' sum_{b>=1} F_{L-1-b}[c][c] phi_{c,b}
# Also: residue sequences (def:residue): y_{c,n} = mu_c Res_{a_c}(V (theta/w)^{n+1} dz); random lower-triangular frame scrambles.
import random
from fractions import Fraction

def inv(x, p): return pow(x % p, p - 2, p)
def modq(fr, p):
    if isinstance(fr, Fraction): return fr.numerator % p * inv(fr.denominator, p) % p
    return fr % p

# ---- truncated power series mod p (lists of length P) ----
def smul(A, B, P, p):
    C = [0] * P
    for i, a in enumerate(A[:P]):
        if a:
            for j in range(min(len(B), P - i)):
                C[i + j] = (C[i + j] + a * B[j]) % p
    return C
def sinv(A, P, p):
    assert A[0] % p
    i0 = inv(A[0], p); B = [0] * P; B[0] = i0
    for n in range(1, P):
        s = 0
        for k in range(1, min(n, len(A) - 1) + 1): s += A[k] * B[n - k]
        B[n] = (-s * i0) % p
    return B
def spoly_shift(coeffs, a, P, p):
    """polynomial sum coeffs[k] z^k  -> series in t = z - a"""
    out = [0] * P
    # Horner: f(a+t)
    for c in reversed(coeffs):
        # out = out*(a+t) + c
        new = [0] * P
        for i in range(P):
            if out[i]:
                new[i] = (new[i] + out[i] * a) % p
                if i + 1 < P: new[i + 1] = (new[i + 1] + out[i]) % p
        new[0] = (new[0] + c) % p
        out = new
    return out
def pmul(A, B, p):
    C = [0] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, b in enumerate(B): C[i + j] = (C[i + j] + a * b) % p
    return C
def wpoly(a, p):
    w = [1]
    for ac in a: w = pmul(w, [(-ac) % p, 1], p)
    return w
def ppow(A, e, p):
    R = [1]
    for _ in range(e): R = pmul(R, A, p)
    return R
def matinv(M, p):
    n = len(M); A = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] % p), None)
        if piv is None: return None
        A[c], A[piv] = A[piv], A[c]
        iv = inv(A[c][c], p); A[c] = [x * iv % p for x in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [(x - f * y) % p for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]

def block_germs(p, s, L, a, theta, v, F, vprime=None, P=40):
    """returns germs[c][b] (series in t at a_c, length P) and What[c] (series), F[n][i][c] ints/Fractions, n<L"""
    a = [modq(x, p) for x in a]; v = [modq(x, p) for x in v]
    Fm = [[[modq(F[n][i][c], p) for c in range(s)] for i in range(s)] for n in range(L)]
    w = wpoly(a, p); thinv = inv(modq(theta, p), p)
    Wp = [x * thinv % p for x in ppow(w, L, p)]           # W' = w^L/theta as polynomial
    germs = []; What = []
    for c in range(s):
        Wt = spoly_shift(Wp, a[c], P + L + 2, p)
        assert all(x == 0 for x in Wt[:L]) and Wt[L] != 0
        What.append(Wt[L:L + P])
        ph = [None] * L
        unit_b = list(range(L - s + 1, L))
        others = [i for i in range(s) if i != c]
        B = [[(-v[i] * Fm[L - 1 - b][i][c]) % p for b in unit_b] for i in others]
        Bi = matinv(B, p)
        if Bi is None: raise ValueError('B_c singular at c=%d' % c)
        U = [sinv([(a[c] - a[i]) % p, 1], P, p) for i in others]   # 1/(t + a_c - a_i)
        for bi, b in enumerate(unit_b):
            ser = [0] * P
            for ii in range(s - 1):
                coef = Bi[bi][ii]
                if coef:
                    ser = [(x + coef * y) % p for x, y in zip(ser, U[ii])]
            ph[b] = ser
        for b in range(1, L - s + 1):
            vp = modq(vprime[c], p)
            ph[b] = [x * inv(vp, p) % p for x in spoly_shift(ppow(w, L - 1 - b, p), a[c], P, p)]
        # own germ
        Wser = Wt[:P]                                   # W' as series at a_c
        WovT = Wt[1:P + 1]                              # W'/t
        rhs = [x * inv(v[c], p) % p for x in WovT]
        for b in range(1, L):
            f = Fm[L - 1 - b][c][c]
            if f:
                rhs = [(x + f * y) % p for x, y in zip(rhs, smul(Wser, ph[b], P, p))]
        den = [(-Fm[L - 1][c][c] * x) % p for x in Wser]; den[0] = (den[0] + 1) % p
        ph[0] = smul(rhs, sinv(den, P, p), P, p)
        germs.append(ph)
    return germs, What, a

def valuation(ser):
    for i, x in enumerate(ser):
        if x: return i
    return None

def block_matrices(p, s, L, a, theta, v, F, vprime=None, rows=20, cols=16):
    P = rows + L + cols + 5
    germs, What, aa = block_germs(p, s, L, a, theta, v, F, vprime, P)
    vals = [[valuation(germs[c][b]) for b in range(L)] for c in range(s)]
    C = []
    for c in range(s):
        Wi = sinv(What[c], P, p)
        Cc = []
        powW = Wi[:]                                     # What^{-(n+1)}
        n = 0
        while L * n < rows:
            for b in range(L):
                N = L * n + b
                if N >= rows: break
                S = smul(germs[c][b], powW, P, p)
                e = L * (n + 1) - 1
                row = []
                ak = [1]                                  # (a_c+t)^k as series
                for k in range(cols):
                    val = 0
                    for j, coef in enumerate(ak):
                        if coef and e - j >= 0: val += coef * S[e - j]
                    row.append(val % p)
                    ak = pmul(ak, [aa[c], 1], p)
                Cc.append(row)
            powW = smul(powW, Wi, P, p); n += 1
        C.append(Cc)
    return C, vals

def U_matrices(p, s, a, theta, v, rows=20, cols=16):
    """residue sequence: y_{c,n} = mu_c Res_{a_c}(V (theta/w)^{n+1} dz)"""
    a = [modq(x, p) for x in a]; th = modq(theta, p); v = [modq(x, p) for x in v]
    w = wpoly(a, p); P = rows + cols + 5; C = []
    for c in range(s):
        wt = spoly_shift(w, a[c], P + 1, p); What = wt[1:P + 1]   # w = t*What
        Wi = sinv(What, P, p); mu = inv(v[c], p); Cc = []; powW = Wi[:]
        for n in range(rows):
            row = []; ak = [1]; fac = mu * pow(th, n + 1, p) % p
            for k in range(cols):
                val = sum(coef * powW[n - j] for j, coef in enumerate(ak) if n - j >= 0)
                row.append(val * fac % p); ak = pmul(ak, [a[c], 1], p)
            Cc.append(row); powW = smul(powW, Wi, P, p)
        C.append(Cc)
    return C

def pascal(a, rows, cols, p):
    from math import comb
    return [[(comb(k, n) * pow(a, k - n, p)) % p if k >= n else 0 for k in range(cols)] for n in range(rows)]

def random_scramble(p, s, a, rows, cols, rng, dense=True):
    C = []
    for c in range(s):
        Lc = [[(rng.randrange(p) if (k < n and dense) else 0) for k in range(rows)] for n in range(rows)]
        for n in range(rows): Lc[n][n] = rng.randrange(1, p)
        Pc = pascal(a[c] % p, rows, cols, p)
        C.append([[sum(Lc[n][k] * Pc[k][j] for k in range(n + 1)) % p for j in range(cols)] for n in range(rows)])
    return C

# ---------- designs ----------
def design(name, p):
    """returns (s, a, v, F list of s x s int matrices for depths 0..s-1) for L = s"""
    if name == 'rot2':
        return 2, [0, 1], [1, 1], [[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]]
    if name == 'geo3':
        M = [[-1, -1, 1], [1, -1, -1], [-1, 1, -1]]; J = [[0, 0, -1], [-1, 0, 0], [0, -1, 0]]
        return 3, [0, 2, 1], [Fraction(1, 2), Fraction(1, 2), -1], [M, J, [[0] * 3 for _ in range(3)]]
    raise KeyError(name)
