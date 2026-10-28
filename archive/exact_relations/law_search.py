# law_search.py (lawU.py of the search) -- the law of the unscaled residue digits rho_{c,n}(V) = Res_{a_c}(V w^{-n-1} dz) (residue sequence, theta=1, v=1)
# and of DIGIT-SCALED U: y_{c,n} = mu_{c,n} rho_{c,n} (the general sequence with an exact pure skeleton at every m = -1 mod s,
# a lemma of the research notes; Remark rem:skelsearch).  Exact F_p linear algebra.
#   Lam[c][c'][d] = coefficient of the cell digit rho_{c',K-1-d} in the geometric digit rho_{c,K} (K-independent, self-similar).
#   Digit-scaled response at full level K, carry length l in column c':  D_K(l)[c][c'] = mu_{c,K} sum_{d<l} Lam[c][c'][d] u_{c',K-1-d},
#   u = 1/mu.   validate(): compares this formula with the law solved directly from the generator matrices of a random
#   digit-scaled U (no formula used there).
import sys, random
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gen import U_matrices, inv, matinv

def law_from_C(C, p, s, K):
    """level-K law from generator matrices: geometric digit (row K) of every c as combination of the cell digits.
    returns coef[c][c'][n] = coefficient of y_{c',n} (n<K) in y_{c,K}."""
    m = s * K
    A = [C[c][n][:m] for c in range(s) for n in range(K)]      # cell digits = A V
    Ai = matinv(A, p)
    assert Ai is not None
    coef = []
    for c in range(s):
        g = C[c][K][:m]                                        # y_{c,K} = g.V = g Ai (cells)
        row = [sum(g[k] * Ai[k][j] for k in range(m)) % p for j in range(m)]
        coef.append([[row[cp * K + n] for n in range(K)] for cp in range(s)])
    return coef

def Lam(p, s, a, K0=24):
    C = U_matrices(p, s, a, 1, [1] * s, rows=K0 + 1, cols=s * K0)
    coef = law_from_C(C, p, s, K0)
    return [[[coef[c][cp][K0 - 1 - d] for d in range(K0)] for cp in range(s)] for c in range(s)]

def scaled_C(p, s, a, mu, rows, cols):
    C = U_matrices(p, s, a, 1, [1] * s, rows=rows, cols=cols)
    return [[[x * mu[c][n] % p for x in C[c][n]] for n in range(rows)] for c in range(s)]

def resp_formula(L, mu, p, s, K, l):
    u = [[inv(x, p) for x in mu[c]] for c in range(s)]
    return [[mu[c][K] * sum(L[c][cp][d] * u[cp][K - 1 - d] for d in range(l)) % p for cp in range(s)] for c in range(s)]

def resp_direct(C, p, s, K, l):
    coef = law_from_C(C, p, s, K)
    return [[sum(coef[c][cp][K - 1 - d] for d in range(l)) % p for cp in range(s)] for c in range(s)]

def validate(p, s, a, K=6, seed=1):
    rng = random.Random(seed)
    L = Lam(p, s, a)
    # self-similarity check: law at K=10 equals law at K=24 on common depths
    C = U_matrices(p, s, a, 1, [1] * s, rows=11, cols=s * 10)
    c10 = law_from_C(C, p, s, 10)
    ok_ss = all(c10[c][cp][9 - d] == L[c][cp][d] for c in range(s) for cp in range(s) for d in range(10))
    mu = [[rng.randrange(1, p) for _ in range(K + 2)] for c in range(s)]
    C = scaled_C(p, s, a, mu, K + 2, s * (K + 1))
    ok = all(resp_formula(L, mu, p, s, KK, l) == resp_direct(C, p, s, KK, l) for KK in range(1, K + 1) for l in range(1, KK + 1))
    return ok_ss, ok

if __name__ == '__main__':
    p = int(sys.argv[1]); s = int(sys.argv[2]); a = [int(x) for x in sys.argv[3].split(',')]
    print('validate (self-similar law, digit-scaled formula):', validate(p, s, a))
    if len(sys.argv) > 4:
        L = Lam(p, s, a, int(sys.argv[5]) if len(sys.argv) > 5 else 24)
        with open(sys.argv[4], 'w') as f:
            D = len(L[0][0]); f.write('%d %d %d\n' % (p, s, D))
            for c in range(s):
                for cp in range(s): f.write(' '.join(map(str, L[c][cp])) + '\n')
        print('wrote', sys.argv[4])
