"""t2d_alib.py -- independent implementation of the two-dimensional window rules (written from the definitions only):
the scramble of 2D Faure (I,P) over F_p, the generator matrices, the direct level-K law by linear algebra, the
one-digit certificate, and the t-value of every prefix. Unchanged copy of the development library.
"""
import math, random

def inv(a, p): return pow(a % p, p - 2, p)

def gamma_series(p, n):
    # t^2 expanded in w = t(t-1) at t=1: u=t-1, w=u+u^2 -> revert: u = w - u^2
    u = [0] * n
    if n > 1: u[1] = 1
    for k in range(2, n):
        u[k] = (-sum(u[i] * u[k - i] for i in range(1, k))) % p
    # t^2 = (1+u)^2 = 1 + 2u + u^2
    u2 = [sum(u[i] * u[k - i] for i in range(k + 1)) % p for k in range(n)]
    g = [((1 if k == 0 else 0) + 2 * u[k] + u2[k]) % p for k in range(n)]
    return g

def series_inv(a, p, n):
    b = [0] * n; b[0] = inv(a[0], p)
    for k in range(1, n):
        b[k] = (-b[0] * sum(a[i] * b[k - i] for i in range(1, k + 1) if i < len(a))) % p
    return b

def greedy_X(p, c, Wo, Wx, n, mode='first', rng=None):
    """X[l] for l=1..n+1 (index 0 unused = 0). Theorem G greedy. mode: first/last/random."""
    g = gamma_series(p, n + 2)
    Wo = set(w % p for w in Wo); Wxl = sorted(set(w % p for w in Wx))
    assert (-c) % p in Wxl, "(i) fails"
    X = [0] * (n + 2); X[1] = (-c) % p
    ci = inv(c, p)
    Os = [None] * (n + 2)
    for l in range(1, n + 1):
        s = sum(g[l - k] * pow(c, l - k, p) * X[k + 1] for k in range(0, l)) % p
        cand = [x for x in Wxl if (1 + ci * (x + s)) % p in Wo]
        if not cand: raise RuntimeError(f"covering fails at l={l}")
        if mode == 'first': x = cand[0]
        elif mode == 'last': x = cand[-1]
        else: x = rng.choice(cand)
        X[l + 1] = x; Os[l] = (1 + ci * (x + s)) % p
    return X, Os

def build_L(p, c, X, D):
    xi = [(X[n + 1] - X[n]) % p for n in range(D)]          # X(x) coefficients
    ci = inv(c, p)
    Y = [xi[n] * pow(ci, n, p) % p for n in range(D)]       # X(y/c)
    Yi = series_inv(Y, p, D)
    tau = [(-c * v) % p for v in Yi]                        # tau_hat(y) = -c / X(y/c)
    assert tau[0] == 1
    E = [[((-1) ** (j - k) * math.comb(2 * j + 1 - k, j - k)) % p if k <= j else 0 for k in range(D)] for j in range(D)]
    TE = [[sum(tau[j - i] * E[i][k] for i in range(k, j + 1)) % p for k in range(D)] for j in range(D)]
    L1 = [[pow(c, j, p) * TE[j][k] % p for k in range(D)] for j in range(D)]
    L0 = [[L1[j][k] * (1 if k % 2 == 0 else p - 1) % p for k in range(D)] for j in range(D)]
    return L0, L1, tau

def gen_mats(p, L0, L1, D, M):
    """C_c: D rows x M cols. Place 0 Taylor digits = identity; place 1: [(t-1)^k] t^l = C(l,k)."""
    C0 = [[L0[j][l] if l < D else 0 for l in range(M)] for j in range(D)]
    C1 = [[sum(L1[j][k] * math.comb(l, k) for k in range(min(j, l) + 1)) % p for l in range(M)] for j in range(D)]
    return C0, C1

def rank_mod(rows, p):
    A = [r[:] for r in rows]; rk = 0; ncol = len(A[0]) if A else 0
    for col in range(ncol):
        piv = next((r for r in range(rk, len(A)) if A[r][col] % p), None)
        if piv is None: continue
        A[rk], A[piv] = A[piv], A[rk]; iv = inv(A[rk][col], p)
        A[rk] = [v * iv % p for v in A[rk]]
        for r in range(len(A)):
            if r != rk and A[r][col]:
                f = A[r][col]; A[r] = [(a - f * b) % p for a, b in zip(A[r], A[rk])]
        rk += 1
    return rk

def t_value(C0, C1, p, m):
    """Niederreiter: largest rho with all d0+d1=rho (first d0 rows of C0, d1 rows of C1, first m cols) independent."""
    for rho in range(m, -1, -1):
        ok = True
        for d0 in range(rho + 1):
            rows = [r[:m] for r in C0[:d0]] + [r[:m] for r in C1[:rho - d0]]
            if rows and rank_mod(rows, p) < rho: ok = False; break
        if ok: return m - rho
    return m

def solve_left(row, B, p):
    """x with x B = row (B square nonsingular)."""
    n = len(B)
    M = [[B[j][i] for j in range(n)] + [row[i]] for i in range(n)]   # B^T x = row
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] % p)
        M[col], M[piv] = M[piv], M[col]; iv = inv(M[col][col], p); M[col] = [v * iv % p for v in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]; M[r] = [(a - f * b) % p for a, b in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]

def direct_law(C0, C1, p, K):
    """r_c = ell_c . (cell digits of coord0 [0..K-1], coord1 [0..K-1]). Returns ell0, ell1."""
    B = [C0[j][:2 * K] for j in range(K)] + [C1[j][:2 * K] for j in range(K)]
    ell0 = solve_left(C0[K][:2 * K], B, p); ell1 = solve_left(C1[K][:2 * K], B, p)
    return ell0, ell1

def partial_sums(ell, K, p):
    """own[l], cross[l] for l=1..K: sums over the finest l cell digits (digits K-l..K-1)."""
    a, b = ell[:K], ell[K:]
    own = [None] + [sum(a[K - l:]) % p for l in range(1, K + 1)]
    crs = [None] + [sum(b[K - l:]) % p for l in range(1, K + 1)]
    return own, crs

def T(e, D, p):
    D %= p
    return max(0.0, min(abs(e + (((r + D) % p) - r) / p) for r in range(p)) - 1 / p)

def cert_LB(ell0, ell1, K, p):
    o0, x0 = partial_sums(ell0, K, p)   # x0[l]: change of r0 from carry length l in coord-1 cell index
    x1, o1 = partial_sums(ell1, K, p)   # ell1 = [coord0 digits | coord1 digits]: first block is CROSS for r1
    best = 1.0
    for l in range(1, K + 1):
        best = min(best, math.hypot(T(1, o0[l], p), T(0, x1[l], p)))   # step in coord 0
        best = min(best, math.hypot(T(0, x0[l], p), T(1, o1[l], p)))   # step in coord 1
    for l0 in range(1, K + 1):
        for l1 in range(1, K + 1):
            best = min(best, math.hypot(T(1, o0[l0] + x0[l1], p), T(1, o1[l1] + x1[l0], p)))
            best = min(best, math.hypot(T(1, o0[l0] - x0[l1], p), T(-1, -o1[l1] + x1[l0], p)))
    return best

def LB_W(Wo, Wx, p):
    t1o = min(T(1, o, p) for o in Wo); t0x = min(T(0, x, p) for x in Wx)
    dp = min(T(1, o + x, p) for o in Wo for x in Wx); dm = min(T(1, o - x, p) for o in Wo for x in Wx)
    return math.sqrt(min(t1o ** 2 + t0x ** 2, 2 * dp ** 2, 2 * dm ** 2))

WIT = {5: (2, [0, 1, 2], [2, 3]), 7: (2, [-3, -2], [-2, -1, 0, 1, 2]), 11: (2, [-5, -4, -3, -2], [-2, -1, 0, 1, 2]),
       13: (3, [-5, -4, -3], [-3, -2, -1, 0, 1, 2, 3]), 19: (3, [-7, -6, -5, -4, -3], [-3, -2, -1, 0, 1, 2, 3]),
       37: (6, [-10, -9, -8, -7, -6], list(range(-6, 7)))}
