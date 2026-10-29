"""b2core.py -- the base-2 sequence of Theorem thm:B2: generator matrices over F_2 from the closed form, Sobol' (I,P),
carry law D(l). Used by make_figs.py (fig:B2). Unchanged copy of the development library."""
import numpy as np
NT = 200  # series truncation degree

def mul(a, b, nt=NT):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r & ((1 << nt) - 1)

u = 0; k = 1
while k < NT: u |= 1 << k; k *= 2          # u = sum_{k>=0} x^{2^k}
one_u = 1 ^ u
g0 = mul(1 | 2, one_u)                       # (1+x)(1+u)
g1 = u >> 1                                  # u/x

def cols(g, t, ncol):
    out = []; p = g
    for _ in range(ncol):
        out.append(p); p = mul(p, t)
    return out                               # column k as int: bit n = C[n,k]

COLS = ncols = 180
B2 = [cols(g0, u, ncols), cols(g1, one_u, ncols)]
SOB = [[1 << k for k in range(ncols)], [sum(1 << n for n in range(k + 1) if (n & k) == n) for k in range(ncols)]]

def dirnums(C, bits=32):
    return [sum(((C[k] >> n) & 1) << (bits - 1 - n) for n in range(bits)) for k in range(bits)]

def points(C, m, bits=32):
    M = [dirnums(Cc, bits) for Cc in C]
    N = 1 << m; X = np.zeros((N, 2), dtype=np.int64)
    idx = np.arange(N)
    for c in range(2):
        v = np.zeros(N, dtype=np.int64)
        for k in range(m):
            v ^= np.where((idx >> k) & 1, M[c][k], 0)
        X[:, c] = v
    return X / float(1 << bits)

def min_dist_torus(P):
    best = 9.0
    for s in range(0, len(P), 512):
        d = np.abs(P[s:s+512, None, :] - P[None, :, :]); d = np.minimum(d, 1 - d)
        d2 = (d ** 2).sum(-1)
        for a in range(d2.shape[0]): d2[a, s + a] = 9
        best = min(best, d2.min())
    return np.sqrt(best)

def row(C, n, ncol):  # row n of matrix as int over columns 0..ncol-1
    return sum(((C[k] >> n) & 1) << k for k in range(ncol))

def inv_f2(rows, n):
    """rows: list of n ints (bit k = entry [r,k]); returns inverse rows."""
    A = [(rows[r], 1 << r) for r in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if (A[r][0] >> col) & 1)
        A[col], A[piv] = A[piv], A[col]
        for r in range(n):
            if r != col and (A[r][0] >> col) & 1:
                A[r] = (A[r][0] ^ A[col][0], A[r][1] ^ A[col][1])
    return [a[1] for a in A]

def law(C, K, j):
    """Lambda: cell digits (n_0 digits 0..K-1, n_1 digits 0..K-1; vector index c*K+d) -> offset digits
    (coord c, digit K+i). Returns function D(c, src, l) -> list of j bits (i=0..j-1)."""
    n = 2 * K
    Arows = [row(C[c], d, n) for c in range(2) for d in range(K)]   # cell digit = Arows . i
    Ainv = inv_f2(Arows, n)   # i = Ainv . celldigits  (Ainv rows indexed by index bit)
    # convert Ainv rows (bit r = entry [k, r]) into columns: col r = vector over k
    Acols = [sum(((Ainv[k] >> r) & 1) << k for k in range(n)) for r in range(n)]
    Brows = {(c, i): row(C[c], K + i, n) for c in range(2) for i in range(j)}
    def D(c, src, l):
        v = 0
        for d in range(K - l, K): v ^= Acols[src * K + d]   # index-bit vector for flipping finest l digits of n_src
        return [bin(Brows[(c, i)] & v).count('1') & 1 for i in range(j)]
    def lam_row(c, i):  # which cell digits feed offset digit K+i of coord c
        return [[bin(Brows[(c, i)] & Acols[s * K + d]).count('1') & 1 for d in range(K)] for s in range(2)]
    return D, lam_row
