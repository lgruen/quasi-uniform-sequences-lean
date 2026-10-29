"""b3_gen.py -- generator matrices of the residue sequences of Section sec:residue, from the residue formulas of
Definitions def:residuestar and def:residue, by truncated power series over F_p (t = z - a_c).

  staggered residue sequence  R*_v:  C_c[n][i] = mu_c th^{n+1} [t^n] (t+a_c)^i / ((t+a_c-a_*) W_c(t)^{n+1})   (c != c*)
                                     C_*[n][i] = mu_* th^n     [t^n] (t+a_*)^i / W_*(t)^n
  residue sequence            R_v :  C_c[n][i] = v_c^{-1} th^{n+1} [t^n] (t+a_c)^i / W_c(t)^{n+1}
  with W_c(t) = prod_{b != c} (t + a_c - a_b)  (= w_c(z) = w(z)/(z - a_c) at z = a_c + t).

Self-test (python3 scripts/b3_gen.py): (1) the brick wall over F_7 (theta = -1/4, mu = (-4, 2)) reproduces the 4x4
blocks of Example ex:running; (2) R_v agrees with the independent generator audit_gen.U_matrices; (3) the relations of
Lemmas lem:residuestar-rel and lem:residue-rel hold on the monomial basis.  Runtime < 1 s.
"""
import os, sys

def inv(x, p): return pow(x % p, p - 2, p)

def smul(A, B, R, p):
    C = [0] * R
    for i, a in enumerate(A[:R]):
        if a:
            for j in range(min(len(B), R - i)):
                C[i + j] = (C[i + j] + a * B[j]) % p
    return C

def sinv(A, R, p):
    i0 = inv(A[0], p); B = [0] * R; B[0] = i0
    for n in range(1, R):
        s = sum(A[k] * B[n - k] for k in range(1, min(n, len(A) - 1) + 1))
        B[n] = (-s * i0) % p
    return B

def spow(A, e, R, p):
    out = [1] + [0] * (R - 1)
    for _ in range(e): out = smul(out, A, R, p)
    return out

def Wc(a, c, R, p):
    W = [1] + [0] * (R - 1)
    for b in range(len(a)):
        if b != c: W = smul(W, [(a[c] - a[b]) % p, 1], R, p)
    return W

def matrices(kind, p, a, theta, rows, cols, v=None, cstar=None, mu=None):
    """kind 'U' (residue sequence, check vector v) or 'R' (staggered, mu = list of row scalars, mu[cstar] = mu_*)."""
    s = len(a); R = rows; th = theta % p
    C = []
    for c in range(s):
        W = Wc(a, c, R, p); Winv = sinv(W, R, p)
        lin = [a[c] % p, 1]                     # t + a_c
        cols_ser = [[1] + [0] * (R - 1)]
        for i in range(1, cols): cols_ser.append(smul(cols_ser[-1], lin, R, p))
        M = [[0] * cols for _ in range(rows)]
        if kind == 'U':
            sc = inv(v[c], p)
            for n in range(rows):
                ker = spow(Winv, n + 1, R, p); f = sc * pow(th, n + 1, p) % p
                for i in range(cols): M[n][i] = f * smul(cols_ser[i], ker, R, p)[n] % p
        else:
            if c == cstar:
                for n in range(rows):
                    ker = spow(Winv, n, R, p); f = mu[c] * pow(th, n, p) % p
                    for i in range(cols): M[n][i] = f * smul(cols_ser[i], ker, R, p)[n] % p
            else:
                extra = sinv([(a[c] - a[cstar]) % p, 1], R, p)   # 1/(t + a_c - a_*)
                for n in range(rows):
                    ker = smul(spow(Winv, n + 1, R, p), extra, R, p); f = mu[c] * pow(th, n + 1, p) % p
                    for i in range(cols): M[n][i] = f * smul(cols_ser[i], ker, R, p)[n] % p
        C.append(M)
    return C

def brickwall(p, rows, cols):
    th = (-inv(4, p)) % p
    return matrices('R', p, [0, 1], th, rows, cols, cstar=1, mu=[(-4) % p, 2])

if __name__ == '__main__':
    C = brickwall(7, 4, 4)
    ex0 = [[1,0,0,0],[6,2,0,0],[5,2,4,0],[0,1,5,1]]; ex1 = [[2,2,2,2],[4,0,3,6],[3,1,0,0],[6,1,2,0]]
    print('brick wall p=7 = ex:running:', C[0] == ex0 and C[1] == ex1)
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from audit_gen import U_matrices
    ok = True
    for (p, a, th, v) in [(11, [0, 1, 2], 1, [9, 4, 10]), (13, [3, 9, 5], 5, [1, 7, 11]), (11, [0, 1], 3, [3, 10])]:
        A = matrices('U', p, a, th, 8, 8, v=v); B = U_matrices(p, len(a), a, th, v, rows=8, cols=8)
        B = [[[x % p for x in row[:8]] for row in M[:8]] for M in B]
        ok = ok and A == B
    print('R_v = audit_gen.U_matrices:', ok)
    # relations on the monomial basis
    p, a, th, v = 11, [0, 1, 2], 1, [9, 4, 10]; s = 3
    C = matrices('U', p, a, th, 8, 12, v=v); bad = 0
    for K in range(1, 4):
        for i in range(s * K - 1):
            bad += sum(v[c] * C[c][K - 1][i] for c in range(s)) % p != 0
    print('lem:residue-rel failures (p=11, s=3, K<=3):', bad)
    k = [inv(4, 13), inv(2, 13)]; mu = [(-1 * inv(k[0], 13)) % 13, (-1 * inv(k[1], 13)) % 13, 1]
    C = matrices('R', 13, [0, 1, 2], 1, 8, 12, cstar=2, mu=mu); bad = 0
    for K in range(1, 4):
        for i in range(3 * K):
            bad += (C[2][K][i] - k[0] * C[0][K - 1][i] - k[1] * C[1][K - 1][i]) % 13 != 0
    print('lem:residuestar-rel failures (p=13, s=3, K<=3):', bad)
