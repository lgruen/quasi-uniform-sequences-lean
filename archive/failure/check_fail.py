# Audit program: Section sec:fail checks (independent code). thm:nonqu / lem:carrypair pairs on Halton-type (incl. non-monic,
# reducible bases), Q = p^w (G1), F_4 frame (prime power, Q = 2^w), Sobol' (Lemma S1, cor:sobol pair, tab:sobolpar),
# rem:faurerate, cor:unscrambled, rem:toeplitz.  Usage: python3 failure/check_fail.py
import random, math
from fractions import Fraction
from ff import *

# ---------------- generic prime-field helpers
def badic(V, b, p):
    """b-adic digits (list of polys, deg < deg b)"""
    out = []
    V = trim(list(V))
    while V:
        q, r = pdivmod(V, b, p)
        out.append(r); V = q
    return out

def halton_coord(V, b, p, mu=1, extra=0):
    """GHS Def. 2 radical inverse, digit map pi(a) = ([z^{e-1}]a,...,[z^0]a), times scalar mu; exact Fraction"""
    e = len(b) - 1
    y = Fraction(0); pos = 0
    for a in badic(V, b, p):
        for i in range(e):
            idx = e - 1 - i
            d = (mu * (a[idx] if idx < len(a) else 0)) % p
            pos += 1
            y += Fraction(d, p ** pos)
    return y

def order_mod(x, mod, p, cap=10 ** 6):
    r = pmod(x, mod, p); cur = list(r); n = 1
    while trim(list(cur)) != [1]:
        cur = pmod(pmul(cur, r, p), mod, p); n += 1
        if n > cap:
            raise RuntimeError("order too large")
    return n

def nonqu_pair(bases, ch, p, Q, gvec=None, kmult=1):
    s = len(bases); b = bases[ch]; e = len(b) - 1
    es = [len(x) - 1 for x in bases]
    E = 1
    for x in es:
        E = E * x // math.gcd(E, x)
    Theta = [1]
    for c in range(s):
        if c != ch:
            Theta = pmul(Theta, ppow(bases[c], E // es[c], p), p)
    R = pmul(psub([1], b, p), Theta, p)
    nu = order_mod(b, R, p)
    bnu = ppow(b, nu, p)
    ordT = order_mod(Theta, bnu, p)
    k = ordT * kmult
    while (E // e) * (k + 1) < nu:
        k += ordT
    eta = (E // e) * (k + 1) - nu
    # digit map of GHS: pi(g) = (1..1) -> g = 1+z+..+z^{e-1}; gt = -(1+..+z^{e-2}); g' = -g
    g = [1] * e; gt = [(p - 1)] * (e - 1); gp = [(p - 1)] * e
    def S(n):
        r = []
        bp = [1]
        for _ in range(n):
            r = padd(r, bp, p); bp = pmul(bp, b, p)
        return r
    D = pmul(pmul(pmul(g, ppow(b, Q * eta, p), p), S(Q * nu), p), ppow(Theta, Q * k, p), p)
    V1 = padd(pmul(gt, ppow(b, Q * eta, p), p), pmul(pmul(gp, ppow(b, Q * eta + 1, p), p), S(Q * nu - 1), p), p)
    L = Q * E * (k + 1); m = Q * (s * E * (k + 1) - (s - 1) * E)
    return dict(V1=V1, V2=padd(V1, D, p), D=D, L=L, m=m, nu=nu, k=k, eta=eta, E=E)

def check_halton(bases, ch, p, Q, label):
    P = nonqu_pair(bases, ch, p, Q)
    V1, V2 = P["V1"], P["V2"]
    y1 = [halton_coord(V1, b, p) for b in bases]
    y2 = [halton_coord(V2, b, p) for b in bases]
    d2 = sum((a - c) ** 2 for a, c in zip(y1, y2))
    s = len(bases)
    bound = Fraction(s + 3, p ** (2 * P["L"]))
    print(f"{label}: nu={P['nu']} k={P['k']} eta={P['eta']} L={P['L']} m={P['m']} degV1={len(V1)-1} degV2={len(V2)-1} "
          f"d^2*p^(2L)={float(d2 * p ** (2 * P['L'])):.4f} (<{s+3}: {d2 < bound}; in P_m: {len(V2) <= P['m'] and len(V1) <= P['m']})")

random.seed(1)
# Halton-type, p=3: b0 = z^2+1 (irreducible), b1 = 2z+1 (non-monic linear)
check_halton([[1, 0, 1], [1, 2]], 0, 3, 1, "p=3 {z^2+1, 2z+1} chat=0 Q=1")
check_halton([[1, 0, 1], [1, 2]], 1, 3, 1, "p=3 {z^2+1, 2z+1} chat=1 Q=1")
check_halton([[1, 0, 1], [1, 2]], 1, 3, 3, "p=3 {z^2+1, 2z+1} chat=1 Q=3")
# reducible base: b0 = z^2 (=z*z), b1 = z+1, p=2 ; and 3 coords p=5: z, z-1, z^2+2
check_halton([[0, 0, 1], [1, 1]], 0, 2, 1, "p=2 {z^2, z+1} chat=0 Q=1")
check_halton([[0, 0, 1], [1, 1]], 0, 2, 2, "p=2 {z^2, z+1} chat=0 Q=2")
check_halton([[0, 1], [4, 1], [2, 0, 1]], 2, 5, 1, "p=5 {z, z-1, z^2+2} chat=2 Q=1")
check_halton([[0, 1], [4, 1], [3, 1]], 0, 5, 1, "p=5 Faure-type {z, z-1, z-2} chat=0 Q=1")
check_halton([[0, 1], [4, 1], [3, 1]], 0, 5, 5, "p=5 Faure-type {z, z-1, z-2} chat=0 Q=5")

# ---------------- cor:unscrambled: coordinate chat = mu*diag(beta^n)*Pas_a, others L_c*Pas_{a_c} with random L_c
def taylor_digits(V, a, p, n):
    t = shift_poly(V, a, p)
    return [(t[i] if i < len(t) else 0) for i in range(n)]
def coord_val(d, p):
    return sum(Fraction(x, p ** (i + 1)) for i, x in enumerate(d))
def unscr_test(p, places, ch, mu, beta, Q):
    s = len(places)
    bases = [[(-a) % p, 1] for a in places]
    binv = pow(beta, p - 2, p)
    bases_thm = list(bases)
    bases_thm[ch] = [(-places[ch] * binv) % p, binv]           # beta^{-1}(z - a)
    # digit map of mu * (identity radical inverse): pi(g) = mu*g ; need pi(g) = 1 => g = mu^{-1}; gt=0; g'=-mu^{-1}
    P = nonqu_pair(bases_thm, ch, p, Q)
    # rebuild with the right g's: nonqu_pair uses GHS g (=1 for e=1); here the digit map is mu*id, so g = mu^{-1}
    mi = pow(mu, p - 2, p)
    scale = lambda V: pscal(V, mi, p)
    V1, V2 = scale(P["V1"]), scale(P["V2"])
    L = P["L"]; Ndig = P["m"] + 2
    Ls = {c: [[random.randrange(p) if j < n else ((random.randrange(1, p)) if j == n else 0) for j in range(Ndig)] for n in range(Ndig)] for c in range(s) if c != ch}
    def point(V):
        y = []
        for c in range(s):
            td = taylor_digits(V, places[c], p, Ndig)
            if c == ch:
                d = [(mu * pow(beta, n, p) * td[n]) % p for n in range(Ndig)]
            else:
                d = [sum(Ls[c][n][j] * td[j] for j in range(n + 1)) % p for n in range(Ndig)]
            y.append(coord_val(d, p))
        return y
    y1, y2 = point(V1), point(V2)
    d2 = sum((a - b) ** 2 for a, b in zip(y1, y2))
    print(f"cor:unscrambled p={p} places={places} chat={ch} mu={mu} beta={beta} Q={Q}: L={L} m={P['m']} "
          f"d^2 p^(2L)={float(d2 * p ** (2 * L)):.4f} < {s+3}: {d2 < Fraction(s + 3, p ** (2 * L))}")
unscr_test(7, [0, 1, 3], 1, 3, 5, 1)
unscr_test(5, [0, 2], 0, 2, 3, 1)

# ---------------- rem:faurerate
def faurerate(p, places, ch, c1, Q):
    s = len(places)
    a = places[ch]
    delta = {c: (places[c] - a) % p for c in range(s) if c != ch}
    gamma = 1
    for c in delta:
        gamma = gamma * (-delta[c]) % p
    # in Y = z - a
    D = pscal(ppow([p - 1, 1], Q - 1, p), (-pow(gamma, p - 2, p)) % p, p)
    for c in delta:
        if c != c1:
            D = pmul(D, ppow([(-delta[c]) % p, 1], Q, p), p)
    V1 = [0] + [p - 1] * (Q - 1)
    # back to z: substitute Y = z - a
    V1z = shift_poly(V1, (-a) % p, p); Dz = shift_poly(D, (-a) % p, p)
    V2z = padd(V1z, Dz, p)
    Nd = (s - 1) * Q + 2
    pt = lambda V: [coord_val(taylor_digits(V, places[c], p, Nd), p) for c in range(s)]
    y1, y2 = pt(V1z), pt(V2z)
    d2 = sum((x - y) ** 2 for x, y in zip(y1, y2))
    ind = lambda V: sum(x * p ** i for i, x in enumerate(V))
    print(f"rem:faurerate p={p} places={places} Q={Q}: deg D={len(Dz)-1} (<{(s-1)*Q}) ind(V1)={ind(V1z)} ind(V2)={ind(V2z)} "
          f"d^2 p^(2Q)={float(d2 * p ** (2 * Q)):.3f} < p^2+s+2={p*p+s+2}: {d2 < Fraction(p * p + s + 2, p ** (2 * Q))}")
faurerate(5, [0, 1], 0, 1, 5)
faurerate(5, [0, 1, 2], 0, 1, 5)
faurerate(7, [0, 1, 4, 5], 0, 1, 7)
