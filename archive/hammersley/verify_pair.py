"""verify_pair.py -- exact check of the carry-pair bound for Hammersley lifts (no enumeration of the net).

For a scrambled frame C_c = L_c Pas_{a_c} with places A in {0} u mu_n (n = s-1 if 0 in A, else n = s), the indices
    i = (p^l - 1) p^k,   j = p^{k+l},   l = n p^r - 1,   k + l + 1 <= m
have j - i = p^k and index difference D = z^k (1 + z + ... + z^l) = z^k (z - 1)^{p^r - 1} H^{p^r} over F_p,
H = 1 + z + ... + z^{n-1}, which vanishes to order k at 0, to order >= p^r - 1 at 1 and to order >= p^r at the other
n-th roots of unity.  Claim (prop:liftcarry, sharper constant of the Lean stage V10-5): the lifted distance satisfies
    delta^2 <= p^{2(k-m)} + [0 in A] p^{-2k} + [1 in A] p^{-2(p^r-1)} + |A minus {0,1}| p^{-2 p^r}.
This script computes the two lifted points exactly (R = m + extra digits, integer arithmetic) for the paper's constructions
and prints c_pair = |x_i - x_j|_T * N^{1/(s+1)} against the bound.  Also scans the low digits u (i -> i+u, j -> j+u) for the
smallest pair of this family when p^k is small.
Usage: python verify_pair.py CONSTR p s m k r [places...]
"""
import sys, os, math
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from b3_gen import brickwall, matrices, inv
from audit_gen import block_matrices, pascal


def seq(constr, p, s, R, m, places):
    if constr == 'faure':
        return [pascal(a % p, R, m, p) for a in places]
    if constr == 'bw':
        return brickwall(p, R, m)
    if constr == 'res':
        rho = 1
        while (rho + 1) ** s <= p: rho += 1
        v = [pow(rho, c + 1, p) for c in range(s - 1)] + [p - 1]
        return matrices('U', p, places, 1, R, m, v=v)
    if constr == 'stag':
        k = [pow(inv(2, p), s - i, p) for i in range(1, s)]
        mu = [(-inv(kc, p)) % p for kc in k] + [1]
        return matrices('R', p, places, 1, R, m, cstar=s - 1, mu=mu)
    if constr == 'blk':
        assert s == 2
        C, _ = block_matrices(p, 2, 2, places, 1, [1, 1], [[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]], None, rows=R, cols=m)
        return C
    raise KeyError(constr)


def point(C, p, m, R, idx):
    V = [(idx // p ** t) % p for t in range(m)]
    out = []
    for M in C:
        x = 0
        for n in range(R):
            x = x * p + sum(M[n][t] * V[t] for t in range(m)) % p
        out.append(Fraction(x, p ** R))
    return out


def tdist2(x, y):
    s = 0
    for a, b in zip(x, y):
        d = abs(a - b); d = min(d, 1 - d); s += d * d
    return s


def main():
    constr, p, s, m, k, r = sys.argv[1], *map(int, sys.argv[2:7])
    places = [int(a) % p for a in sys.argv[7:]] or list(range(s))
    n = s - 1 if 0 in places else s; l = n * p ** r - 1
    assert all(a == 0 or pow(a, n, p) == 1 for a in places), 'places not in {0} u mu_n'
    assert k + l + 1 <= m, 'pair does not fit'
    R = m + 8
    C = seq(constr, p, s, R, m, places)
    N = p ** m
    base_i, base_j = (p ** l - 1) * p ** k, p ** (k + l)
    A = set(places)
    bound2 = (Fraction(1, p ** (2 * (m - k))) + (0 in A) * Fraction(1, p ** (2 * k))
              + (1 in A) * Fraction(1, p ** (2 * (p ** r - 1))) + len(A - {0, 1}) * Fraction(1, p ** (2 * p ** r)))
    best = None
    for u in range(min(p ** k, 2000)):
        i, j = base_i + u, base_j + u
        xi = [Fraction(i, N)] + point(C, p, m, R, i); xj = [Fraction(j, N)] + point(C, p, m, R, j)
        d2 = tdist2(xi, xj)
        if best is None or d2 < best[0]: best = (d2, u)
    scale = N ** (1.0 / (s + 1))
    d0 = tdist2([Fraction(base_i, N)] + point(C, p, m, R, base_i), [Fraction(base_j, N)] + point(C, p, m, R, base_j))
    ok = d0 <= bound2   # exact rational comparison (the pair of the proof, u = 0)
    print('%s p=%d s=%d m=%d k=%d r=%d l=%d places=%s: c_pair(u=0)=%.6f  min over %d u: %.6f (u=%d)  bound=%.6f  %s' % (
        constr, p, s, m, k, r, l, places, math.sqrt(d0) * scale,
        min(p ** k, 2000), math.sqrt(best[0]) * scale, best[1], math.sqrt(float(bound2)) * scale, 'PASS' if ok else 'FAIL'))
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
