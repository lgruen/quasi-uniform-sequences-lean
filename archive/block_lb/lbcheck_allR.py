"""lbcheck_allR.py -- second, independent evaluation of the computer-assisted part of thm:block(c):
LB(F) = 1 - (a*_s + 1)/p at every prime 7 <= p <= 109 (s = 4) and 19 <= p <= 109 (s = 5).

Written from the statements of lem:cert (j = 1, prime p) and thm:block(iii) only (no code of the search programs or of the
first program is used): for every step e in {-1,0,1}^s \\ {0} (both signs, no symmetry reduction) and every choice of carry
lengths of the moving coordinates, capped at s-1 (carry length l gives the response column of M^{(min(l,s-1)-1)},
M^{(j)} = F_0 + ... + F_j, j <= s-2), sigma_i = sum_c e_c M^{(j_c)}[i][c] mod p, and the term of coordinate i is
f_1(e_i, sigma_i) = max(0, min_R |e_i p + R(+)sigma_i - R| - 1)/p, the minimum over ALL positions R in {0..p-1}
(computed by brute force once per prime, as a table). LB(F) = min(1, min sqrt(sum_i f_1^2)).
The designs F_0..F_{s-2} are read as data from block_lb/ustar_finite.json (the design U*_s of [Gru26geo] at the places
0, 1, 1/2, ..., 1/(s-1)); the s = 4 design is compared with the matrices printed after thm:block in Section 6.
    python3 block_lb/lbcheck_allR.py      (from the archive root; a few seconds)
"""
import json, os, math, itertools
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, 'ustar_finite.json')
D = json.load(open(DATA))
PRINTED_F4 = [[[-5, 2, 1, 2], [1, -3, -1, -1], [1, 2, -5, -2], [1, 1, 1, -3]],
              [[0, -3, -1, -1], [-2, 0, 2, 1], [-1, -1, 0, 3], [0, -1, 0, 0]],
              [[0, 2, 0, -1], [2, 0, -2, 0], [0, -1, 0, -2], [-1, 0, -1, 0]]]


def primes(lo, hi):
    return [n for n in range(lo, hi + 1) if n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))]


def lbF(F, s, p):
    # partial sums M^{(j)}, j = 0..s-2
    M, acc = [], [[0] * s for _ in range(s)]
    for j in range(s - 1):
        acc = [[acc[i][c] + F[j][i][c] for c in range(s)] for i in range(s)]
        M.append([row[:] for row in acc])
    # f_1 numerators by brute force over the position R: tab[e][sigma] = max(0, min_R |e p + (R+sigma mod p) - R| - 1)
    tab = {e: [max(0, min(abs(e * p + (R + sg) % p - R) for R in range(p)) - 1) for sg in range(p)]
           for e in (-1, 0, 1)}
    best = None
    for e in itertools.product((-1, 0, 1), repeat=s):
        if not any(e):
            continue
        mv = [c for c in range(s) if e[c]]
        for js in itertools.product(range(s - 1), repeat=len(mv)):
            tot = 0
            for i in range(s):
                sg = sum(e[c] * M[j][i][c] for c, j in zip(mv, js)) % p
                b = tab[e[i]][sg]
                tot += b * b
            if best is None or tot < best:
                best = tot
    return best  # integer (p LB)^2, before the cap at 1


ok = True
assert [D['4']['F'][j] for j in range(3)] == PRINTED_F4, 's = 4 data differ from the printed design'
for s, astar, lo in ((4, 5, 7), (5, 16, 19)):
    F = D[str(s)]['F'][:s - 1]
    diag = max(-F[0][c][c] for c in range(s))
    assert diag == astar, (s, diag)
    bad = []
    for p in primes(lo, 109):
        b2 = lbF(F, s, p)
        target = p - astar - 1                      # LB = 1 - (a*+1)/p  <=>  min sum b^2 = (p - a* - 1)^2
        if not (isinstance(b2, int) and b2 == target * target):
            bad.append((p, b2))
    print('s=%d a*=%d: LB(F) = 1-(a*+1)/p at every prime %d..109: %s' % (s, astar, lo, 'yes' if not bad else bad))
    ok = ok and not bad
print('ALL OK' if ok else 'FAIL')
