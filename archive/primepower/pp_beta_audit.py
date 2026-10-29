# Independent recomputation of beta_q(k) of prop:primepower (one-digit bound, staggered coordinate only),
# power-basis encoding of F_p[x]/(f): element sum c_i x^i <-> code sum c_i p^i. Written by the audit of the Lean stage.
# usage: python3 primepower/pp_beta_audit.py p f_0,...,f_r s [k_1,...,k_{s-1}]   (without k: max over all weights);
# also imported by primepower/rows_check.py.
import itertools, sys
from functools import lru_cache
def mk(p, f):  # f: list of coefficients low->high, monic, degree r
    r = len(f) - 1; q = p ** r
    def dig(a): return [(a // p ** i) % p for i in range(r)]
    def code(v): return sum(c * p ** i for i, c in enumerate(v))
    def add(a, b): return code([(x + y) % p for x, y in zip(dig(a), dig(b))])
    def neg(a): return code([(-x) % p for x in dig(a)])
    def mul(a, b):
        A, B = dig(a), dig(b); prod = [0] * (2 * r - 1)
        for i, x in enumerate(A):
            for j, y in enumerate(B): prod[i + j] = (prod[i + j] + x * y) % p
        for d in range(2 * r - 2, r - 1, -1):
            c = prod[d]
            if c:
                for i in range(r + 1): prod[d - r + i] = (prod[d - r + i] - c * f[i]) % p
        return code(prod[:r])
    ADD = [[add(a, b) for b in range(q)] for a in range(q)]
    NEG = [neg(a) for a in range(q)]
    MUL = [[mul(a, b) for b in range(q)] for a in range(q)]
    # irreducibility check: every nonzero element has an inverse
    irr = all(any(MUL[a][b] == 1 for b in range(1, q)) for a in range(1, q))
    Ds = [sum(p ** i for i in range(t + 1)) for t in range(r)]
    # sanity: digit increments of the code are exactly Ds
    inc = set()
    for y in range(q):
        y2 = (y + 1) % q; inc.add(ADD[y2][NEG[y]])
    assert inc == set(Ds), (inc, Ds)
    gap = {}
    for e in (-1, 0, 1):
        for sg in range(q):
            m = min(abs(e * q + ADD[R][sg] - R) for R in range(q))
            gap[(e, sg)] = max(0, m - 1)
    return q, ADD, NEG, MUL, Ds, gap, irr
def beta(F, s, k):  # k: list of s-1 weight codes; staggered coordinate is the last one
    q, ADD, NEG, MUL, Ds, gap, irr = F
    best = q
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e): continue
        mov = [c for c in range(s - 1) if e[c]]
        for ds in itertools.product(Ds, repeat=len(mov)):
            sg = 0
            for c, d in zip(mov, ds):
                t = MUL[k[c]][d]
                if e[c] < 0: t = NEG[t]
                sg = ADD[sg][t]
            g = gap[(e[s - 1], sg)]
            if g < best: best = g
    return best
if __name__ == "__main__":
    p = int(sys.argv[1]); f = list(map(int, sys.argv[2].split(','))); s = int(sys.argv[3])
    F = mk(p, f); print("q=%d irreducible=%s" % (F[0], F[6]))
    if len(sys.argv) > 4:
        k = list(map(int, sys.argv[4].split(','))); print("beta numerator", beta(F, s, k), "/", F[0])
    else:
        q = F[0]; best = max((beta(F, s, list(k)), k) for k in itertools.product(range(1, q), repeat=s - 1))
        print("max over weights:", best)
