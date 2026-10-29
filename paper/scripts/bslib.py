"""bslib.py -- point sets for the window-system figures: the staggered window system p = 101 (in the development
version "brick-star"), Faure, and digital sequences given by generator matrices; exact nearest neighbours via mdist.

The generator matrices C'_c = L_c C_c of the staggered window system are not rebuilt here: they were dumped by the
verifier of the window systems of the development repository (data/bs3_p101.txt; first line p R C, then the 3*R*C
matrix entries), and points are formed by digit expansion  x_c = sum_{i<R} (sum_j C'_c[i][j] n_j mod p) p^{-i-1}
(n_j = base-p digits of the index, least significant first), exactly in int64 (p^R < 2^52).
Faure: C_c[i][j] = binom(j,i) c^{j-i} mod p (places 0,1,2[,3]; c=0 is the identity).
"""
import _paths
import os, math, subprocess
import numpy as np

WORK = _paths.DATA                       # input: generator matrices

# instances: (dump file, brick axis, window LB all K (lem:cert j=1), source)
BS3 = {101: ('bs3_p101.txt', 2, 0.5148, 'staggered window system p = 101 (app:LFdata)')}


def Dfor(q):
    return int(52 / math.log2(q))


def load_dump3(fn):
    t = open(os.path.join(WORK, fn)).read().split()
    p, R, C = int(t[0]), int(t[1]), int(t[2]); v = np.array(t[3:3 + 3 * R * C], dtype=np.int64)
    return p, v.reshape(3, R, C)


def faure_mats(p, s, R, C):
    M = np.zeros((s, R, C), dtype=np.int64)
    for c in range(s):
        for i in range(R):
            for j in range(i, C):
                M[c, i, j] = (math.comb(j, i) % p) * pow(c, j - i, p) % p
    return M


def digit_points(p, M, N, start=0):
    """first N points (indices start..start+N-1) of the digital sequence with matrices M[c][i][j]; float64 in [0,1)."""
    s, R, C = M.shape
    assert p ** C >= start + N and p ** R < 2 ** 53
    n = np.arange(start, start + N, dtype=np.int64)
    dig = np.empty((N, C), dtype=np.int64)
    for j in range(C):
        dig[:, j] = n % p; n //= p
    X = np.empty((N, s))
    for c in range(s):
        Y = (dig @ M[c].T) % p                 # N x R
        w = p ** np.arange(R - 1, -1, -1, dtype=np.int64)
        X[:, c] = (Y @ w).astype(np.float64) / float(p ** R)
    return X


def bs3_points(p, N):
    fn = BS3[p][0]; q, M = load_dump3(fn); assert q == p
    return digit_points(p, M, N)


def faure_points(p, s, N):
    C = 1
    while p ** C < N: C += 1
    return digit_points(p, faure_mats(p, s, Dfor(p), max(C, 1)), N)


# ------------------------------------------------------------------ Sobol' + Owen
# ------------------------------------------------------------------ min distance (C++)
def write_bin(X, fn):
    np.ascontiguousarray(X, dtype=np.float64).tofile(fn)


def nn_dist(X, tag):
    fn = os.path.join(_paths.TMP, f'_pts_{tag}.bin'); out = os.path.join(_paths.TMP, f'_nn_{tag}.bin')
    write_bin(X, fn); subprocess.run([_paths.exe('mdist'), 'nn', fn, str(X.shape[1]), str(len(X)), out], check=True, capture_output=True)
    d = np.fromfile(out, dtype=np.float64); os.remove(fn); os.remove(out); return d


def load_drops(fn):
    ev = [l.split() for l in open(fn) if l.strip() and not l.startswith('#')]
    Ns = np.array([int(e[0]) for e in ev if e[0] != 'END']); d2 = np.array([float(e[1]) for e in ev if e[0] != 'END'])
    Nmax = int(next(e[1] for e in ev if e[0] == 'END'))
    return Ns, d2, Nmax


def c_at(dr, N, s=3):
    Ns, d2, Nmax = dr; k = np.searchsorted(Ns, N, side='right') - 1
    return float(np.sqrt(d2[k]) * N ** (1.0 / s))
