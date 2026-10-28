"""alib3.py -- audit library, written from the WRITTEN definitions only
(no import of roots/ code).  Pure Python, F_p arithmetic.

Conventions:
  places a_0,a_1,a_2 in F_p, w = prod (t - a_c), index place oo.
  unscrambled digit k of coord c = [(t-a_c)^k] V  ->  Pc[k][i] = C(i,k) a_c^(i-k)
  scrambled row j = polar part at a_c of  omega_j^(c) = lam_c theta^j w^(-j-1) rho_c(w) dt,
     in basis (t-a_c)^(-k-1) dt  ->  L_c[j][k];  generator C_c = L_c * Pc.
  LI law (Prop LI_3): Q_c = 1/rho_hat_c ; we take rho_c(0)=1, lam_c = mu_c.
"""
from math import comb


def inv(a, p):
    return pow(a % p, p - 2, p)


# ---------- truncated power series mod p (lists of length N) ----------
def smul(a, b, p, N):
    r = [0] * N
    for i, x in enumerate(a[:N]):
        if x:
            for j in range(min(len(b), N - i)):
                r[i + j] = (r[i + j] + x * b[j]) % p
    return r


def sinv(a, p, N):
    a0 = inv(a[0], p)
    r = [0] * N
    r[0] = a0
    for n in range(1, N):
        s = 0
        for k in range(1, min(n, len(a) - 1) + 1):
            s += a[k] * r[n - k]
        r[n] = (-s * a0) % p
    return r


def local_u(places, c, p, N):
    """u(w) = t - a_c as a power series in w near a_c (w = prod(t-a)).
    w = u * h(u), h(u) = prod_{c''!=c}(a_c - a_c'' + u) = h0 + h1 u + u^2."""
    a = places[c]
    others = [places[k] for k in range(3) if k != c]
    d1, d2 = (a - others[0]) % p, (a - others[1]) % p
    h0, h1 = d1 * d2 % p, (d1 + d2) % p
    u = [0] * N
    u2 = [0] * N
    u3 = [0] * N
    ih0 = inv(h0, p)
    for n in range(1, N):
        # [w^n]: h0 u_n + h1 [u^2]_n + [u^3]_n = [n==1]; u2,u3 at n do not involve u_n
        s2 = sum(u[i] * u[n - i] for i in range(1, n)) % p
        s3 = sum(u[i] * u2[n - i] for i in range(1, n)) % p
        u[n] = (((1 if n == 1 else 0) - h1 * s2 - s3) * ih0) % p
        u2[n] = (s2 + 0) % p  # u_n * u_0 terms vanish (u_0 = 0)
        u3[n] = s3
    # recompute u2,u3 cleanly
    return u


def poly_in_u(coeffs, u, p, N):
    """sum_k coeffs[k] u(w)^k as a w-series"""
    r = [0] * N
    pw = [1] + [0] * (N - 1)
    for k, ck in enumerate(coeffs):
        if k > 0:
            pw = smul(pw, u, p, N)
        for i in range(N):
            r[i] = (r[i] + ck * pw[i]) % p
    return r


def kernels(places, p, N):
    """Hhat_c (own, at a_c) and G[c][cp] = (a_cp - a_c)/(t - a_c) as w-series at a_cp, plus h_c(a_c)."""
    U = [local_u(places, c, p, N) for c in range(3)]
    H, h0 = [], []
    for c in range(3):
        a = places[c]
        others = [places[k] for k in range(3) if k != c]
        d1, d2 = (a - others[0]) % p, (a - others[1]) % p
        hc = poly_in_u([d1 * d2 % p, (d1 + d2) % p, 1], U[c], p, N)
        h0.append(hc[0])
        ih = inv(hc[0], p)
        H.append([x * ih % p for x in hc])
    G = [[None] * 3 for _ in range(3)]
    for c in range(3):
        for cp in range(3):
            if c == cp:
                continue
            # t - a_c at a_cp = (a_cp - a_c) + u_cp
            den = [(places[cp] - places[c]) % p] + U[cp][1:]
            g = sinv(den, p, N)
            G[c][cp] = [x * ((places[cp] - places[c]) % p) % p for x in g]
    return U, H, G, h0


def kappa(places, mu, h0, p, c, cp):
    return mu[c] * inv(mu[cp] * h0[c] * (places[cp] - places[c]), p) % p


def predicted_law(places, mu, theta, Q, p, N):
    """Prop LI_3: own[c][n] (n>=1) and cross[c][cp][n] (n>=0) coefficient series."""
    U, H, G, h0 = kernels(places, p, N)
    own, cross = [None] * 3, [[None] * 3 for _ in range(3)]
    for c in range(3):
        HQ = smul(H[c], Q[c], p, N)
        own[c] = [0] + [(-pow(theta, n, p) * HQ[n]) % p for n in range(1, N)]
    for c in range(3):
        for cp in range(3):
            if c == cp:
                continue
            k = kappa(places, mu, h0, p, c, cp)
            GQ = smul(G[c][cp], Q[cp], p, N)
            cross[c][cp] = [(-k * pow(theta, n + 1, p) * GQ[n]) % p for n in range(N)]
    return own, cross


# ---------- scramble matrices from the definition ----------
def scramble_L(places, c, lam, theta, Q, p, M):
    """L_c[j][k] (j,k<M): polar part of lam theta^j w^{-j-1} rho(w) dt at a_c, rho = 1/Q,
    in basis (t-a_c)^{-k-1} dt.  w = u h(u)  =>  w^{-j-1} = u^{-j-1} h(u)^{-j-1};
    rho(w(u)) a u-series.  coefficient of u^{-k-1}: [u^{j-k}] h(u)^{-j-1} rho(w(u))."""
    a = places[c]
    others = [places[k] for k in range(3) if k != c]
    d1, d2 = (a - others[0]) % p, (a - others[1]) % p
    hpoly = [d1 * d2 % p, (d1 + d2) % p, 1]
    rho = sinv(Q, p, M)
    # w as u-series: u*h(u)
    wu = [0, hpoly[0], hpoly[1], hpoly[2]] + [0] * max(0, M - 4)
    wu = wu[:M]
    # rho(w(u))
    rw = [0] * M
    pw = [1] + [0] * (M - 1)
    for k in range(M):
        if k > 0:
            pw = smul(pw, wu, p, M)
        if rho[k]:
            for i in range(M):
                rw[i] = (rw[i] + rho[k] * pw[i]) % p
    hinv = sinv(hpoly, p, M)
    L = [[0] * M for _ in range(M)]
    hp = [1] + [0] * (M - 1)
    for j in range(M):
        hp = smul(hp, hinv, p, M)  # h^{-j-1}
        F = smul(hp, rw, p, M)
        tj = pow(theta, j, p) * lam % p
        for k in range(j + 1):
            L[j][k] = tj * F[j - k] % p
    return L


def gen_matrix(L, a, p, rows, cols):
    """C = L * Pa, Pa[k][i] = C(i,k) a^(i-k)."""
    C = [[0] * cols for _ in range(rows)]
    for j in range(rows):
        Lj = L[j]
        for i in range(cols):
            s = 0
            for k in range(min(j, i) + 1):
                if Lj[k]:
                    s += Lj[k] * comb(i, k) * pow(a, i - k, p)
            C[j][i] = s % p
    return C


# ---------- linear algebra mod p ----------
def rank(Mat, p):
    A = [r[:] for r in Mat]
    n, m = len(A), len(A[0]) if A else 0
    r = 0
    for col in range(m):
        piv = None
        for i in range(r, n):
            if A[i][col] % p:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        iv = inv(A[r][col], p)
        A[r] = [x * iv % p for x in A[r]]
        for i in range(n):
            if i != r and A[i][col]:
                f = A[i][col]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r


def solve_left(B, R, p):
    """x with x B = R  (B square nonsingular)."""
    n = len(B)
    # solve B^T x^T = R^T
    A = [[B[j][i] for j in range(n)] + [R[i]] for i in range(n)]
    for col in range(n):
        piv = next(i for i in range(col, n) if A[i][col] % p)
        A[col], A[piv] = A[piv], A[col]
        iv = inv(A[col][col], p)
        A[col] = [x * iv % p for x in A[col]]
        for i in range(n):
            if i != col and A[i][col]:
                f = A[i][col]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[col])]
    return [A[i][n] for i in range(n)]


def direct_law(Cs, K, p):
    """law[c][(cp,i)] = coefficient of cell digit i (<K) of coord cp in r_c = digit K of coord c, for P_{3K}."""
    m = 3 * K
    B = [Cs[c][j][:m] for c in range(3) for j in range(K)]
    out = []
    for c in range(3):
        x = solve_left(B, Cs[c][K][:m], p)
        out.append([[x[cp * K + i] for i in range(K)] for cp in range(3)])
    return out


def tvalue_zero_upto(Cs, M, p):
    """sequence criterion: for every m<=M, every (d0,d1,d2) with sum m, rows 0..d_c-1 of C_c restricted to
    columns 0..m-1 are independent.  returns first failing (m,d) or None."""
    for m in range(1, M + 1):
        for d0 in range(m + 1):
            for d1 in range(m - d0 + 1):
                d2 = m - d0 - d1
                rows = [Cs[0][j][:m] for j in range(d0)] + [Cs[1][j][:m] for j in range(d1)] + \
                       [Cs[2][j][:m] for j in range(d2)]
                if rank(rows, p) < m:
                    return (m, (d0, d1, d2))
    return None


# ---------- certificate (own implementation from first principles) ----------
def T(e, D, p):
    D %= p
    best = None
    for r in range(p):
        v = abs(e + (((r + D) % p) - r) / p) - 1.0 / p
        if best is None or v < best:
            best = v
    return max(0.0, best)


def Ttab(p):
    return {e: [T(e, D, p) for D in range(p)] for e in (-1, 0, 1)}


def certificate(partial, K, p, TT=None):
    """partial[c][cp][l] (l=1..K): change of r_c under a +1 carry of length l in coord cp's cell index.
    returns LB_K = min(1, min over e in {-1,0,1}^3\\0, carry lengths, of sqrt(sum_c T(e_c, D_c)^2))."""
    import itertools
    if TT is None:
        TT = Ttab(p)
    best = 1.0
    for e in itertools.product((-1, 0, 1), repeat=3):
        if e == (0, 0, 0):
            continue
        nz = [c for c in range(3) if e[c]]
        for ls in itertools.product(range(1, K + 1), repeat=len(nz)):
            L = dict(zip(nz, ls))
            s = 0.0
            for c in range(3):
                D = sum(e[cp] * partial[c][cp][L[cp]] for cp in nz) % p
                s += TT[e[c]][D] ** 2
            v = s ** 0.5
            if v < best:
                best = v
    return best


def partial_from_direct(law, K, p):
    """carry of length l in coord cp: cell digits K-1..K-l of cp each +1."""
    P = [[[0] * (K + 1) for _ in range(3)] for _ in range(3)]
    for c in range(3):
        for cp in range(3):
            for l in range(1, K + 1):
                P[c][cp][l] = sum(law[c][cp][K - i] for i in range(1, l + 1)) % p
    return P
