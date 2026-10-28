# gen7.py -- audit: independent generator / law / nullspace code, written from the definitions
# (residue form of the paper).  Reuses only the series helpers of gen.py.
#   Row n of coordinate c is a principal part psi = sum_{k<=n} l_k (z-a_c)^{-k-1};  y_{c,n}(V) = Res_{a_c}(V psi dz),
#   so C_c[n][j] = sum_k l_k binom(j,k) a_c^{j-k}   (C_c = L_c P_{a_c}).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen import inv, smul, sinv, spoly_shift, pmul, wpoly
from math import comb

def row_from_pp(l, a, cols, p):
    """l[k] = coeff of (z-a)^{-k-1}"""
    return [sum(l[k] * comb(j, k) * pow(a, j - k, p) for k in range(min(len(l), j + 1))) % p for j in range(cols)]

def what(a, c, P, p):
    """w(a_c + t) = t * what(t); returns what as series of length P"""
    w = wpoly(a, p); wt = spoly_shift(w, a[c] % p, P + 1, p)
    assert wt[0] == 0 and wt[1] != 0
    return wt[1:P + 1]

def pp_coeffs(series, n, p):
    """principal part of t^{-n-1} * series: l_k = [t^{n-k}] series, k = 0..n"""
    return [series[n - k] % p for k in range(n + 1)]

def U_rho_rows(p, a, c, rows, cols):
    """rho_{c,n} = Res_{a_c}(V w^{-n-1} dz), n < rows"""
    P = rows + 2; wh = what(a, c, P, p); wi = sinv(wh, P, p); pw = wi[:]; R = []
    for n in range(rows):
        R.append(row_from_pp(pp_coeffs(pw, n, p), a[c], cols, p)); pw = smul(pw, wi, P, p)
    return R

def digit_scaled_U(p, a, mu, rows, cols):
    """C_c[n] = mu[n][c] * rho_{c,n}"""
    s = len(a); C = []
    for c in range(s):
        R = U_rho_rows(p, a, c, rows, cols)
        C.append([[x * mu[n][c] % p for x in R[n]] for n in range(rows)])
    return C

def compose_w(chi, wser, P, p):
    """chi(w(t)) for chi a polynomial/series in w, w(t) series with valuation 1"""
    out = [0] * P
    for co in reversed(chi):
        out = smul(out, wser, P, p); out[0] = (out[0] + co) % p
    return out

def selfsim_rows(p, a, theta, chis, rows, cols):
    """residue normal form: y_{c,n} = Res_{a_c}(V phi_c (theta/w)^{n+1} dz), phi_c = 1/chi_c(w), chi_c series in w at a_c"""
    s = len(a); P = rows + 2; C = []
    for c in range(s):
        wh = what(a, c, P, p); wser = [0] + wh[:P - 1]
        phi = sinv(compose_w(chis[c][:P], wser, P, p), P, p)
        wi = sinv(wh, P, p); pw = wi[:]; Cc = []
        for n in range(rows):
            ser = smul(phi, pw, P, p); f = pow(theta, n + 1, p)
            Cc.append([x * f % p for x in row_from_pp(pp_coeffs(ser, n, p), a[c], cols, p)])
            pw = smul(pw, wi, P, p)
        C.append(Cc)
    return C

# ---- linear algebra mod p ----
def rref(M, p):
    A = [r[:] for r in M]; piv = []; rk = 0
    ncol = len(A[0]) if A else 0
    for c in range(ncol):
        r0 = next((r for r in range(rk, len(A)) if A[r][c] % p), None)
        if r0 is None: continue
        A[rk], A[r0] = A[r0], A[rk]; iv = inv(A[rk][c], p); A[rk] = [x * iv % p for x in A[rk]]
        for r in range(len(A)):
            if r != rk and A[r][c]:
                f = A[r][c]; A[r] = [(x - f * y) % p for x, y in zip(A[r], A[rk])]
        piv.append(c); rk += 1
    return A[:rk], piv

def rank(M, p): return len(rref(M, p)[0])

def left_nullspace(M, p):
    """basis of {f : f^T M = 0}, M = list of rows"""
    nr = len(M); T = [[M[i][j] for i in range(nr)] for j in range(len(M[0]))]   # transpose
    R, piv = rref(T, p); free = [j for j in range(nr) if j not in piv]; basis = []
    for fj in free:
        v = [0] * nr; v[fj] = 1
        for i, pc in enumerate(piv): v[pc] = (-R[i][fj]) % p
        basis.append(v)
    return basis

def matinv(M, p):
    n = len(M); A = [M[i][:] + [int(i == j) for j in range(n)] for i in range(n)]
    R, piv = rref(A, p)
    if piv[:n] != list(range(n)): return None
    return [r[n:] for r in R]

def law(C, s, K, p):
    """full-level law of P_{sK}: geometric digit y_{c,K} = sum_{c',n<K} Law[c][(c',n)] y_{c',n}; returns Law (s x sK)"""
    m = s * K
    A = [C[c][n][:m] for c in range(s) for n in range(K)]          # cell digits = A V
    Ai = matinv(A, p); assert Ai is not None, 'P_sK not a net'
    B = [C[c][K][:m] for c in range(s)]
    return [[sum(B[c][k] * Ai[k][j] for k in range(m)) % p for j in range(m)] for c in range(s)]

def responses(Lw, s, K, p):
    """D[l][c][c'] = change of y_{c,K} for a +1 carry of length l (1..K) in cell c' (digits K-1..K-l of c' +1)"""
    D = {}
    for l in range(1, K + 1):
        D[l] = [[sum(Lw[c][cp * K + n] for n in range(K - l, K)) % p for cp in range(s)] for c in range(s)]
    return D

def write_mat(C, p, s, m, R, path):
    with open(path, 'w') as f:
        f.write('%d %d %d %d\n' % (p, s, m, R))
        for c in range(s):
            for n in range(R): f.write(' '.join(str(x) for x in C[c][n][:m]) + '\n')
