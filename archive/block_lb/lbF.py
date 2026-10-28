# Audit program: one-digit relaxation LB(F) of thm:block(iii) for a design F=(F_0..F_{s-2}), exact integer arithmetic:
# returns min over steps e (up to sign) and carry lengths l_c in 1..s-1 of sum_i g_i^2, g_i = p*f_1(e_i, sigma_i).
# Also: reachability check (F_n[i][c] = v_i^{-1} tau_ic gamma_{c,n}(tau_ic), deg gamma_{c,n} = n exactly).
import sys, json, itertools, math
from fractions import Fraction as Fr
from fp import primes

def g1(e, sig, p):
    sig %= p
    if e == 0:
        return max(0, min(sig, p - sig) - 1)
    if e == -1:
        sig = (-sig) % p
    return max(0, (sig if sig else p) - 1)

def LBsq(F, p):
    s = len(F[0])
    L = len(F)                    # = s-1 carry depths
    M = []                        # partial sums
    acc = [[0] * s for _ in range(s)]
    for n in range(L):
        acc = [[acc[i][c] + F[n][i][c] for c in range(s)] for i in range(s)]
        M.append([row[:] for row in acc])
    best = None
    arg = None
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e):
            continue
        first = next(x for x in e if x)
        if first < 0:
            continue              # up to sign
        mov = [c for c in range(s) if e[c]]
        for ls in itertools.product(range(L), repeat=len(mov)):
            sig = [0] * s
            for c, l in zip(mov, ls):
                for i in range(s):
                    sig[i] += e[c] * M[l][i][c]
            val = sum(g1(e[i], sig[i], p) ** 2 for i in range(s))
            if best is None or val < best:
                best, arg = val, (e, ls)
    return best, arg

def modq(x, p):
    x = Fr(x)
    return x.numerator % p * pow(x.denominator % p, p - 2, p) % p

def interp_deg(xs, ys, p):
    """degree of the interpolating polynomial (deg <= len-1) mod p, -1 if zero"""
    n = len(xs)
    # Newton divided differences
    coef = list(ys)
    for j in range(1, n):
        for i in range(n - 1, j - 1, -1):
            num = (coef[i] - coef[i - 1]) % p
            den = (xs[i] - xs[i - j]) % p
            coef[i] = num * pow(den, p - 2, p) % p
    # convert Newton form to monomial to read degree: leading coeff of degree k part = coef[k] (top nonzero)
    d = -1
    for k in range(n):
        if coef[k]:
            d = k
    return d

def reach_ok(F, places, v, p):
    s = len(places)
    a = [modq(x, p) for x in places]
    if len(set(a)) < s:
        return False
    vv = [modq(x, p) for x in v]
    for c in range(s):
        others = [i for i in range(s) if i != c]
        taus = [pow((a[i] - a[c]) % p, p - 2, p) for i in others]
        if len(set(taus)) < len(taus):
            return False
        for n in range(s - 1):
            ys = [vv[i] * modq(F[n][i][c], p) % p * pow(t, p - 2, p) % p for i, t in zip(others, taus)]
            if interp_deg(taus, ys, p) != n:
                return False
    return True

if __name__ == "__main__":
    which = sys.argv[1]
    D = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'ustar_finite.json')))
    if which in ("4", "5"):
        s = int(which)
        d = D[which]
        F = d["F"][: s - 1]
        astar = max(-F[0][c][c] for c in range(s))
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        for p in primes(lo, hi):
            b, arg = LBsq(F, p)
            r = reach_ok(F, d["a"], d["v"], p)
            print(p, "LB^2*p^2 =", b, "target", (p - astar - 1) ** 2, "OK" if b == (p - astar - 1) ** 2 else "DIFF", "reach", r, flush=True)
    elif which == "small":
        S2 = [[[-1, 1], [-1, -1]]]
        S3 = [[[-1, -1, 1], [1, -1, -1], [-1, 1, -1]], [[0, 0, -1], [-1, 0, 0], [0, -1, 0]]]
        for p in primes(3, 199):
            b2, _ = LBsq(S2, p)
            out = [p, b2 == (p - 2) ** 2]
            if p >= 3:
                b3, a3 = LBsq(S3, p)
                out += [b3 == (p - 2) ** 2, b3, (p - 2) ** 2]
            print(*out)
        for u in [2, 4, 6, 10, 14, 16, 20]:
            p = u * u + 1
            b, arg = LBsq([[[-1, u], [-u, -1]]], p)
            print("gauss p=%d" % p, "LB=%.4f" % (math.sqrt(b) / p), "formula=%.4f" % (math.sqrt((u - 2) ** 2 + (u * u - u - 1) ** 2) / p), arg)
