"""brute_check.py FILE -- independent exact O(N^2) toroidal separation (integer arithmetic, numpy) of a digital point set
in the liftsep/sepx input format; prints c = delta * N^{1/d}.  Only for small N."""
import sys, numpy as np, itertools
t = open(sys.argv[1]).read().split(); p, d, m, R = map(int, t[:4]); a = np.array(list(map(int, t[4:])), dtype=np.int64).reshape(d, R, m)
N = p ** m; idx = np.arange(N); V = np.stack([(idx // p ** k) % p for k in range(m)])          # m x N index digits
Y = np.einsum('crk,kn->crn', a, V) % p                                                     # digits
w = np.array([p ** (R - 1 - n) for n in range(R)], dtype=object)
X = np.array([[int(sum(int(Y[c, n, i]) * w[n] for n in range(R))) for i in range(N)] for c in range(d)], dtype=object)
Xf = np.array(X.tolist(), dtype=np.int64)  # < p^R <= 2^62
PR = p ** R; best = None
for i in range(N - 1):
    D = np.abs(Xf[:, i + 1:] - Xf[:, i:i + 1]); D = np.minimum(D, PR - D).astype(np.float64)   # exact ints up to 2^53
    s = (D * D).sum(0).min()
    best = s if best is None or s < best else best
print('brute c=%.6f' % (np.sqrt(best) / PR * N ** (1.0 / d)))
