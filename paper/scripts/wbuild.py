# wbuild.py -- the brick wall W^- (Theorem thm:WF; eps = -1, theta = -1/4) and W^+ from the formulas: generator
# matrices, identities, t = 0 and the series law against direct linear algebra (builder of make_figs.mats_wf).
# Unchanged copy of the development builder (except the name of its library, w_alib.py).
import sys
from w_alib import *

CONF = {5: dict(eps=1, s=4), 7: dict(eps=-1, s=5)}

def build(p, eps, s, line=None):
    one = F(p, eps, [1], [], [1]); x = F(p, eps, [0, 1], [], [1])
    rho = F(p, eps, [], [1, eps % p], [1])          # rho = u * r
    t1 = (1 + rho) / 2; t0 = (1 - rho) / 2
    if line == 'eps-1':   # the uniform eps=-1 line: g0 = 2/(rho(1+rho))
        g0 = 2 / (rho * (1 + rho))
    else:
        g0 = 2 * rho / ((1 - x) * (1 + rho))
    g1 = (1 + rho) / rho
    return dict(one=one, x=x, rho=rho, t0=t0, t1=t1, g0=g0, g1=g1)

def checks(p, eps, s, E):
    x, rho, t0, t1, g0, g1 = E['x'], E['rho'], E['t0'], E['t1'], E['g0'], E['g1']
    out = {}
    out['t^2-t=sx'] = all((t*t - t - s*x).iszero() for t in (t0, t1))
    out['rho^2=1+4sx'] = (rho*rho - (1 + 4*s*x)).iszero()
    out['g0g1=2/(1-x)'] = (g0*g1 - 2/(1 - x)).iszero()
    if eps == 1: out['g0 closed'] = (g0 - 2*(1 + x - rho)/(x*(1 - x))).iszero()
    else:        out['g0 closed'] = (g0 - 5*(1 - x - rho)/(x*(1 - x))).iszero() and (g0 - 2/(rho*(1+rho))).iszero()
    out['g1 closed'] = (g1 - (1 + eps*x + rho)/(1 + eps*x)).iszero()
    return out

def series_all(p, eps, s, E, n):
    u = [1, eps % p]
    rser = sinv(ssqrt1(u, p, n), p, n)
    assert rser == lucas_r(p, eps, n), "Lucas != series inverse sqrt"
    S = {k: E[k].series(n-10, rser) for k in ('t0', 't1', 'g0', 'g1')}
    return rser, S

def genmats(p, S, n):
    C = []
    for c in (0, 1):
        g, t = S['g%d' % c], S['t%d' % c]
        cols = []; tk = [1] + [0]*(n-1)
        for k in range(n):
            cols.append(smul(g, tk, p, n)); tk = smul(tk, t, p, n)
        C.append([[cols[k][r] for k in range(n)] for r in range(n)])  # C[c][row][col]
    return C

def rank(M, p):
    M = [r[:] for r in M]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c] % p), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; iv = pow(M[rk][c], p-2, p)
        M[rk] = [(v*iv) % p for v in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]; M[i] = [(a - f*b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def solve_inv(M, p):
    n = len(M); A = [M[i][:] + [int(i == j) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if A[i][c] % p); A[c], A[piv] = A[piv], A[c]
        iv = pow(A[c][c], p-2, p); A[c] = [(v*iv) % p for v in A[c]]
        for i in range(n):
            if i != c and A[i][c]:
                f = A[i][c]; A[i] = [(a - f*b) % p for a, b in zip(A[i], A[c])]
    return [r[n:] for r in A]

def tvalue_ok(C, p, m):
    for a in range(m+1):
        rows = [C[0][r][:m] for r in range(a)] + [C[1][r][:m] for r in range(m-a)]
        if rank(rows, p) < m: return False
    return True

def direct_law(C, p, K, j):
    """D[src][l] = tuple(D[0][src](l) (j digits), D[1][src](l)) for l=1..K by direct linear algebra."""
    m = 2*K
    Mc = [C[0][r][:m] for r in range(K)] + [C[1][r][:m] for r in range(K)]
    Fm = [C[0][r][:m] for r in range(K, K+j)] + [C[1][r][:m] for r in range(K, K+j)]
    Mi = solve_inv(Mc, p)
    Law = [[sum(Fm[a][b]*Mi[b][c] for b in range(m)) % p for c in range(m)] for a in range(2*j)]
    D = {0: {}, 1: {}}
    for src in (0, 1):
        for l in range(1, K+1):
            cols = [src*K + n for n in range(K-l, K)]
            D[src][l] = tuple(sum(Law[a][c] for c in cols) % p for a in range(2*j))
    return D

if __name__ == '__main__':
    for p in (5, 7):
        eps, s = CONF[p]['eps'], CONF[p]['s']
        E = build(p, eps, s)
        print(p, checks(p, eps, s, E))
        n = 30; rser, S = series_all(p, eps, s, E, n+10)
        C = genmats(p, S, n)
        lt = all(C[c][r][k] == 0 for c in (0,) for r in range(n) for k in range(r+1, n))
        diag0 = [C[0][r][r] for r in range(6)]
        print(' C0 lower-tri:', lt, 'diag C0:', diag0, 'g0(0),g1(0)=', S['g0'][0], S['g1'][0])
        # C1 = L1 P: L1 = C1 P^{-1}; check lower-triangular
        P = [[math.comb(k, r) % p for k in range(n)] for r in range(n)]
        Pi = solve_inv(P, p)
        L1 = [[sum(C[1][r][b]*Pi[b][k] for b in range(n)) % p for k in range(n)] for r in range(n)]
        print(' L1=C1 P^-1 lower-tri:', all(L1[r][k] == 0 for r in range(n) for k in range(r+1, n)), 'diag', [L1[r][r] for r in range(5)])
        mmax = 12 if p == 5 else 10
        print(' t=0 for m<=%d:' % mmax, all(tvalue_ok(C, p, m) for m in range(1, mmax+1)))
