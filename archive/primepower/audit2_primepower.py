# Second audit: prop:primepower, beta_q(k) for the power-basis encoding of f, written from the definitions in sec 10 / lem:cert.
import sys, itertools

def mk_field(p, f):
    """f: list of coefficients low->high, monic, degree r. elements = codes 0..q-1"""
    r = len(f) - 1
    q = p ** r
    def dec(c):
        return [(c // p ** i) % p for i in range(r)]
    def enc(v):
        return sum((v[i] % p) * p ** i for i in range(r))
    add = [[enc([(a + b) for a, b in zip(dec(x), dec(y))]) for y in range(q)] for x in range(q)]
    def mulv(a, b):
        prod = [0] * (2 * r - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                prod[i + j] = (prod[i + j] + x * y) % p
        for d in range(2 * r - 2, r - 1, -1):
            c = prod[d]
            if c:
                for i in range(r + 1):
                    prod[d - r + i] = (prod[d - r + i] - c * f[i]) % p
        return prod[:r]
    mul = [[enc(mulv(dec(x), dec(y))) for y in range(q)] for x in range(q)]
    neg = [enc([(-a) % p for a in dec(x)]) for x in range(q)]
    Dset = [enc([1] * (t + 1) + [0] * (r - t - 1)) for t in range(r)]
    return q, add, mul, neg, Dset

def f1q(e, sig, q, add):
    best = min(abs(e * q + add[R][sig] - R) for R in range(q))
    return max(0, best - 1)          # = q * f_1

def beta(s, k, q, add, mul, neg, Dset, memo=None):
    # staggered coordinate cstar, others C with weights k (len s-1)
    best = None
    for eC in itertools.product((-1, 0, 1), repeat=s - 1):
        for es in (-1, 0, 1):
            if es == 0 and not any(eC):
                continue
            mov = [i for i in range(s - 1) if eC[i]]
            for Ds in itertools.product(Dset, repeat=len(mov)):
                sig = 0
                for i, D in zip(mov, Ds):
                    t = mul[k[i]][D]
                    if eC[i] < 0:
                        t = neg[t]
                    sig = add[sig][t]
                v = f1q(es, sig, q, add)
                if best is None or v < best:
                    best = v
                    if best == 0:
                        return 0
    return best

def irreducibles(p, r):
    out = []
    for c in range(p ** r):
        f = [(c // p ** i) % p for i in range(r)] + [1]
        # irreducible iff no root-free factorization: test by checking x^{p^r} = x mod f and gcd conditions (small: brute factor)
        if is_irred(f, p):
            out.append(f)
    return out

def polymod(a, b, p):
    a = a[:]
    while len(a) >= len(b) and any(a):
        if a[-1] == 0:
            a.pop(); continue
        c = a[-1] * pow(b[-1], p - 2, p) % p
        d = len(a) - len(b)
        for i in range(len(b)):
            a[d + i] = (a[d + i] - c * b[i]) % p
        a.pop()
    while a and a[-1] == 0:
        a.pop()
    return a

def is_irred(f, p):
    r = len(f) - 1
    # brute: no monic factor of degree 1..r//2
    for d in range(1, r // 2 + 1):
        for c in range(p ** d):
            g = [(c // p ** i) % p for i in range(d)] + [1]
            if not polymod(f, g, p):
                return False
    return True

if __name__ == "__main__":
    rows = [(2, 2, [1, 1, 0, 1], [2]), (2, 3, [1, 0, 1], [3]), (2, 2, [1, 1, 0, 0, 1], [2]), (2, 5, [2, 0, 1], [10]),
            (2, 3, [1, 2, 0, 1], [11]), (2, 7, [1, 0, 1], [21]),
            (3, 5, [2, 0, 1], [7, 2]), (3, 2, [1, 1, 1, 1, 0, 1], [12, 2]), (3, 7, [1, 0, 1], [21, 7]),
            (3, 2, [1, 1, 0, 0, 0, 0, 1], [42, 23]), (3, 3, [2, 1, 0, 0, 1], [17, 3]), (3, 11, [1, 0, 1], [55, 22]),
            (3, 5, [1, 1, 0, 1], [35, 26])]
    mode = sys.argv[1] if len(sys.argv) > 1 else "rows"
    if mode == "rows":
        for s, p, f, k in rows:
            q, add, mul, neg, D = mk_field(p, f)
            print("s=%d q=%d f=%s k=%s beta*q=%d" % (s, q, f, k, beta(s, k, q, add, mul, neg, D)), flush=True)
    elif mode == "best":
        s, p, r = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        for f in irreducibles(p, r):
            q, add, mul, neg, D = mk_field(p, f)
            b = 0; arg = None
            for k in itertools.product(range(1, q), repeat=s - 1):
                v = beta(s, list(k), q, add, mul, neg, D)
                if v > b:
                    b, arg = v, k
            print("s=%d q=%d f=%s best beta*q=%d at k=%s" % (s, q, f, b, arg), flush=True)
