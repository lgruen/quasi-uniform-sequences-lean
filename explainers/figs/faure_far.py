"""faure_far.py -- the explicit close pair of rem:faurerate for the 2D Faure sequence in base 5 (places 0 and 1):
V1 = -(z + ... + z^(Q-1)), V2 = V1 + (z-1)^(Q-1), both in the first N = 5^Q points, for Q = 5, 25, 125.
Computes both points exactly (coordinate c = Taylor digits of V at the place c, read as a base-5 fraction) and
prints sep = (toroidal distance) * sqrt(N) as log10."""
from fractions import Fraction
from math import comb, log10
p = 5
def taylor_digits(V, a, n):           # coefficients of V in powers of (z - a), mod p
    return [sum(comb(k, j) * pow(a, k - j, p) * V[k] for k in range(j, len(V))) % p for j in range(n)]
def coord(d): return sum(Fraction(x, p ** (i + 1)) for i, x in enumerate(d))
for Q in (5, 25, 125):
    V1 = [0] + [p - 1] * (Q - 1)                       # -(z + ... + z^(Q-1))
    D = [comb(Q - 1, k) * (-1) ** (Q - 1 - k) % p for k in range(Q)]   # (z-1)^(Q-1)
    V2 = [(x + y) % p for x, y in zip(V1, D)]
    idx = lambda V: sum(x * p ** k for k, x in enumerate(V))
    d2 = Fraction(0)
    for a in (0, 1):
        x = coord(taylor_digits(V1, a, Q + 2)) - coord(taylor_digits(V2, a, Q + 2))
        x = abs(x); x = min(x, 1 - x); d2 += x * x
    # sep = sqrt(d2 * N), N = 5^Q
    l = 0.5 * (log10(d2.numerator) - log10(d2.denominator) + Q * log10(p))
    print(f"Q={Q}: indices {idx(V2)} and {'%d' % idx(V1) if Q < 30 else '5^%d - 5' % Q}; N=5^{Q}; sep = 10^{l:.3f}")
