# Audit program: (1) thm:nonqu over F_4 with Q = 2^w (G1: Q a power of p, not of q); (2) Sobol' Lemma S1 + cor:sobol explicit
# pair + tab:sobolpar; (3) rem:toeplitz witness on a small case.  Usage: python3 failure/check_f4_sobol.py
import math, random
from fractions import Fraction
from ff import *

# ---------- GF(4): ints 0..3 = x0 + 2 x1 <-> x0 + x1*omega, omega^2 = omega + 1 ; add = xor
def gm(a, b):
    a0, a1, b0, b1 = a & 1, a >> 1, b & 1, b >> 1
    # (a0 + a1 w)(b0 + b1 w) = a0b0 + (a0b1 + a1b0) w + a1b1 (w+1)
    c0 = (a0 & b0) ^ (a1 & b1)
    c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
    return c0 | (c1 << 1)
def gi(a):
    return next(b for b in (1, 2, 3) if gm(a, b) == 1)
def t4(a):
    while a and a[-1] == 0: a.pop()
    return a
def qadd(a, b):
    n = max(len(a), len(b))
    return t4([(a[i] if i < len(a) else 0) ^ (b[i] if i < len(b) else 0) for i in range(n)])
def qmul(a, b):
    if not a or not b: return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] ^= gm(x, y)
    return t4(r)
def qpow(a, e):
    r = [1]
    for _ in range(e): r = qmul(r, a)
    return r
def qdivmod(a, b):
    a = t4(list(a)); b = t4(list(b)); inv = gi(b[-1])
    q = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b) and a:
        c = gm(a[-1], inv); d = len(a) - len(b); q[d] = c
        for i, y in enumerate(b): a[i + d] ^= gm(c, y)
        t4(a)
    return t4(q), a
def qorder(x, mod):
    r = qdivmod(x, mod)[1]; cur = list(r); n = 1
    while cur != [1]:
        cur = qdivmod(qmul(cur, r), mod)[1]; n += 1
    return n
def qshift(V, a):   # V(a + t)
    r = []
    for c in reversed(V):
        r = qadd(qmul(r, [a, 1]), [c])
    return r

def f4_frame_pair(places, ch, Q):
    s = len(places)
    b = [places[ch], 1]                     # z - a = z + a (char 2)
    Theta = [1]
    for c in range(s):
        if c != ch: Theta = qmul(Theta, [places[c], 1])
    R = qmul(qadd([1], b), Theta)
    nu = qorder(b, R)
    bnu = qpow(b, nu)
    k = qorder(Theta, bnu)
    kk = k
    while kk + 1 < nu: kk += k
    k = kk
    eta = (k + 1) - nu
    ybar = 3; ycirc = 1                     # enc^{-1}(3) = omega^2, enc^{-1}(q/p - 1) = enc^{-1}(1) = 1
    g = ybar; gt = ycirc; gp = ybar          # pi = id, e = 1: pi(g) = -ybar = ybar
    def S(n):
        r = []; bp = [1]
        for _ in range(n): r = qadd(r, bp); bp = qmul(bp, b)
        return r
    D = qmul(qmul(qmul([g], qpow(b, Q * eta)), S(Q * nu)), qpow(Theta, Q * k))
    V1 = qadd(qmul([gt], qpow(b, Q * eta)), qmul(qmul([gp], qpow(b, Q * eta + 1)), S(Q * nu - 1)))
    V2 = qadd(V1, D)
    L = Q * (k + 1); m = Q * (s * (k + 1) - (s - 1))
    Nd = m + 3
    def pt(V):
        return [sum(Fraction(x, 4 ** (i + 1)) for i, x in enumerate((qshift(V, places[c]) + [0] * Nd)[:Nd])) for c in range(s)]
    y1, y2 = pt(V1), pt(V2)
    d2 = sum((x - y) ** 2 for x, y in zip(y1, y2))
    # Theta^k == 1 mod b^nu ?  (c = 1 case)
    c1 = qdivmod(qpow(Theta, k), bnu)[1] == [1]
    print(f"F4 frame places={places} chat={ch} Q={Q}: nu={nu} k={k} (Theta^k=1 mod b^nu: {c1}) L={L} m={m} "
          f"degV1={len(V1)-1} degV2={len(V2)-1} d^2*4^(2L)={float(d2 * 4 ** (2 * L)):.4f} < {s+3}: {d2 < Fraction(s + 3, 4 ** (2 * L))}")
f4_frame_pair([0, 1], 0, 1)
f4_frame_pair([0, 1], 0, 2)
f4_frame_pair([0, 1], 0, 4)
f4_frame_pair([0, 2], 1, 2)      # places 0, omega; chat at omega
f4_frame_pair([0, 1, 2], 2, 2)   # s = 3 over F4

# ---------- Sobol' : F2 polys as ints (bit i = coeff z^i)
def f2mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def f2mod(a, m):
    dm = m.bit_length() - 1
    while a and a.bit_length() - 1 >= dm:
        a ^= m << (a.bit_length() - 1 - dm)
    return a
def f2pow(a, e):
    r = 1
    for _ in range(e): r = f2mul(r, a)
    return r
polys = [0b10, 0b11, 0b111, 0b1011, 0b1101, 0b10011, 0b11001]  # z, z+1, z^2+z+1, z^3+z+1, z^3+z^2+1, z^4+z+1, z^4+z^3+1
print("tab:sobolpar recomputed (s, E, nu, k, L1, m1, (s-1)E, bound rounded up):")
for s in range(2, 8):
    others = polys[1:s]
    es = [q.bit_length() - 1 for q in others]
    E = 1
    for e in es: E = E * e // math.gcd(E, e)
    Theta = 1
    for q, e in zip(others, es): Theta = f2mul(Theta, f2pow(q, E // e))
    R = f2mul(0b11, Theta)
    nu = 1
    while f2mod((1 << nu) ^ 1, R) != 0: nu += 1
    k = 1
    while k < nu: k *= 2
    L = E * (k + 1); m = s * E * (k + 1) - (s - 1) * E
    bnd = math.sqrt(s + 3) * 2 ** (-(s - 1) * E / s)
    def up(x):
        e = math.floor(math.log10(x)) - 2
        return math.ceil(x / 10 ** e) * 10 ** e
    print(f"  s={s} E={E} nu={nu} k={k} L={L} m={m} (s-1)E={(s-1)*E} bound={bnd:.6g} -> {up(bnd):.3g}")

# Sobol' coordinate with polynomial b (const term 1), admissible random direction numbers
def sobol_dirs(b, K, rng):
    e = b.bit_length() - 1
    alpha = [(b >> (e - i)) & 1 for i in range(e + 1)]   # alpha[0]=1 (z^e), alpha[i] coeff of z^{e-i}, alpha[e]=1
    u = [None] + [rng.randrange(1, 2 ** k, 2) for k in range(1, e + 1)]
    for k in range(e + 1, K + 1):
        x = u[k - e] ^ (u[k - e] << e)
        for i in range(1, e):
            if alpha[i]: x ^= u[k - i] << i
        u.append(x)
    return u
def sobol_y(V, u, K):  # exact dyadic, numerator over 2^K
    acc = 0
    k = 1
    while V:
        if V & 1: acc ^= u[k] << (K - k)
        V >>= 1; k += 1
    return acc
rng = random.Random(7)
K = 80
okS1 = True
for b in polys[1:]:
    for trial in range(3):
        u = sobol_dirs(b, K, rng)
        e = b.bit_length() - 1
        for _ in range(30):
            V = rng.getrandbits(40)
            if sobol_y(f2mul(b, V), u, K) != sobol_y(V, u, K) >> e: okS1 = False
        # digit map upper unitriangular: y(z^i) has digits only at positions 0..i, a 1 at position i
        for i in range(e):
            y = sobol_y(1 << i, u, K)
            if y >> (K - i - 1) != (y >> (K - i - 1)) or y % (1 << (K - i - 1)) != 0 or not ((y >> (K - i - 1)) & 1):
                okS1 = False
print("Lemma S1 (shift by b and unitriangular digit map) on 6 polys x 3 random direction sets:", okS1)

# cor:sobol explicit pair, s = 2 and s = 3 (Q = 1, 2 for s = 2), random admissible direction numbers
for s, Qs in ((2, (1, 2, 4)), (3, (1,))):
    others = polys[1:s]
    es = [q.bit_length() - 1 for q in others]
    E = 1
    for e in es: E = E * e // math.gcd(E, e)
    Theta = 1
    for q, e in zip(others, es): Theta = f2mul(Theta, f2pow(q, E // e))
    nu = 1
    while f2mod((1 << nu) ^ 1, f2mul(0b11, Theta)) != 0: nu += 1
    j = 0
    while 2 ** j < nu: j += 1
    eta = E * (2 ** j + 1) - nu
    for Q in Qs:
        L = Q * E * (2 ** j + 1); m = Q * (s * E * (2 ** j + 1) - (s - 1) * E)
        # Theta(z^{2^j Q})
        ThQ = 0; t = Theta; i = 0
        while t:
            if t & 1: ThQ |= 1 << (i * 2 ** j * Q)
            t >>= 1; i += 1
        D = f2mul(f2mul(1 << (Q * eta), (1 << (Q * nu)) - 1), ThQ)
        V1 = (1 << L) - (1 << (Q * eta + 1)); V2 = V1 ^ D
        KK = m + 5
        us = [None] + [[None] + [1] * KK] + [sobol_dirs(q, KK, rng) for q in others]
        def pt(V):
            return [Fraction(sobol_y(V, us[c + 1], KK), 2 ** KK) for c in range(s)]
        y1, y2 = pt(V1), pt(V2)
        d2 = sum((x - y) ** 2 for x, y in zip(y1, y2))
        print(f"cor:sobol s={s} Q={Q}: L={L} m={m} V1<2^m:{V1 < 2**m} V2<2^m:{V2 < 2**m} d^2*4^L={float(d2 * 4 ** L):.4f} < {s+3}: {d2 < Fraction(s + 3, 4 ** L)}")

# ---------- rem:toeplitz, p = 3, s = 2, a = 0, other place 2, rho = A/B with A = 1, B = 1 + Y
p = 3
A = [1]; B = [1, 1]
deltas = [2]                       # a_c - a
E1 = [1]
for d in deltas: E1 = pmul(E1, [1, (-pow(d, p - 2, p)) % p], p)
R1 = pmul([1, p - 1], A, p)
prod = pmul(R1, E1, p)
nu = 1
while pmod(padd([1], [0] * nu + [p - 1], p), prod, p) != []: nu += 1
Q = p
while Q % nu != 1 % nu: Q *= p
Qp = p
while Qp < nu: Qp *= p
L = Q * (Qp + 1); eta = L - nu * Q
Nser = L + 5
H = pmul(sinv(ppow(E1, L, p, N=Nser) + [0] * Nser, p, Nser), sinv(R1 + [0] * Nser, p, Nser), p, Nser)
BH = pmul(B, H, p, Nser)
gap = all((BH + [0] * Nser)[n] == 0 for n in range((nu - 1) * Q + len(B) - 1, nu * Q))
T1 = (BH + [0] * Nser)[:nu * Q]
D = pmul(pmul(ppow(E1, L, p), [0] * eta + [1], p), trim(list(T1)), p)
m = 2 * L - Q + (len(B) - 1)
# scrambled digits of coordinate 0 at a = 0: Taylor digits of rho*V = A V / B
def scr(V, n):
    return (pmul(pmul(A, V, p, n), sinv(B + [0] * n, p, n), p, n) + [0] * n)[:n]
dD = scr(D, L)
patt = dD == [0] * eta + [1] * (L - eta)
div = pmod(D, ppow([(-2) % p, 1], L, p), p) == []
# V1: scrambled digits (0^eta, 0, -1, ..., -1)  => V1 = (target * B/A) mod Y^L
target = [0] * (eta + 1) + [p - 1] * (L - eta - 1)
V1 = trim((pmul(pmul(target, B, p, L), sinv(A + [0] * L, p, L), p, L) + [0] * L)[:L])
V2 = padd(V1, D, p)
Nd = m + 10
def pt(V):
    y0 = sum(Fraction(x, p ** (i + 1)) for i, x in enumerate(scr(V, Nd)))
    t = shift_poly(V, 2, p) + [0] * Nd
    y1 = sum(Fraction(t[i], p ** (i + 1)) for i in range(Nd))   # other coordinate unscrambled (any LT scramble keeps L digits)
    return y0, y1
y1, y2 = pt(V1), pt(V2)
d2 = sum((x - y) ** 2 for x, y in zip(y1, y2))
print(f"rem:toeplitz p=3 rho=1/(1+Y), places 0,2: nu={nu} Q={Q} Q'={Qp} L={L} eta={eta} gap={gap} digits(D)=(0^eta,1^(L-eta)):{patt} "
      f"(z-2)^L|D:{div} degD={len(D)-1} < m={m}: {len(D)-1 < m}, degV1<L:{len(V1) <= L}; d^2 p^(2L)={float(d2 * p ** (2 * L)):.3f} <= 5: {d2 <= Fraction(5, p ** (2 * L))}")
