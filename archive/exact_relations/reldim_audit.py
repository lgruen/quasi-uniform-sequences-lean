# cor:nodesign sharpness: dimension of the space of exact digit relations of top index K, depth <= J,
# on P_{sK}, among the residue digits  yhat_{c,n}(V) = Res_{a_c}(V w^{-n-1} dz).
# Method A: rows from the residue definition, left-kernel dimension.
# Method B: lem:reltype criterion: polynomials A, deg A <= s-1, whose w-adic expansion at every a_c has
#           nu_k = 0 for J < k <= K  (dimension = s - rank of those linear conditions).
import sys
from fp import *

def resrow(p, places, c, n, m):
    """vector (yhat_{c,n}(z^i))_{i<m}"""
    a = places[c]
    w = w_poly(places, p)
    # w_c = w/(z-a): synthetic division
    wc = w_poly([b for j, b in enumerate(places) if j != c], p)
    N = n + 1
    wcs = shift_poly(wc + [0] * N, a, p)[:N]
    g = spow(sinv(wcs, p, N), n + 1, p, N)
    row = []
    zi = [1] + [0] * (N - 1)          # (t+a)^i truncated
    for i in range(m):
        row.append(sum(zi[k] * g[n - k] for k in range(N)) % p)
        zi = smul(zi, [a % p, 1], p, N)
    return row

def dimA(p, places, J, K):
    s = len(places)
    m = s * K
    rows = [resrow(p, places, c, n, m) for c in range(s) for n in range(K - J, K + 1)]
    return len(rows) - rank_mod(rows, p)

def wadic(p, places, c, P, N):
    """coefficients nu_0..nu_{N-1} of P = sum nu_k w^k as power series at a_c"""
    s = len(places)
    a = places[c]
    w = w_poly(places, p)
    ws = shift_poly(w + [0] * N, a, p)[:N]   # w(t+a) = t*unit
    Ps = shift_poly(list(P) + [0] * N, a, p)[:N]
    # invert t -> w: successive subtraction
    nu = []
    rem = Ps[:]
    wk = [1] + [0] * (N - 1)
    for k in range(N):
        # leading coeff of w^k is (ws[1])^k at t^k
        lead = wk[k]
        coef = rem[k] * pow(lead, p - 2, p) % p
        nu.append(coef)
        rem = [(x - coef * y) % p for x, y in zip(rem, wk)]
        wk = smul(wk, ws, p, N)
    return nu

def dimB(p, places, J, K):
    s = len(places)
    conds = []
    for c in range(s):
        cols = []
        for j in range(s):
            P = [0] * j + [1]
            nu = wadic(p, places, c, P, K + 1)
            cols.append(nu)
        for k in range(J + 1, K + 1):
            conds.append([cols[j][k] for j in range(s)])
    if not conds:
        return s
    return s - rank_mod(conds, p)

if __name__ == "__main__":
    for (p, places, J) in [(11, [0, 1, 2, 3], 3), (13, [0, 1, 2, 3], 3), (17, [0, 1, 2, 3], 3),
                           (11, [0, 1, 2], 2), (11, [0, 1, 2, 3], 2), (11, [0, 1, 2, 3], 1)]:
        out = []
        for K in range(J, J + 6):
            out.append((K, dimA(p, places, J, K), dimB(p, places, J, K)))
        print(p, places, "J=%d" % J, out)
    # over Q-like large prime
    for p in [101, 1009, 10007]:
        print(p, [0, 1, 2, 3], [(K, dimB(p, [0, 1, 2, 3], 3, K)) for K in range(3, 8)])
