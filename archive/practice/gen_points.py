"""gen_points.py dump_pp_s3_p<p>.txt N [start] -- print points start..start+N-1 of a certified (0,3)-sequence.
Dump format: 'p R C' then 3*R rows of C integers = rows i<R, columns j<C of the generator matrices C'_c (c=0,1,2).
Point n: digits n_j of n in base p (least significant first, j<C, so n < p^C);
  x_c = sum_{i<R} ((sum_j C'_c[i][j] n_j) mod p) p^{-(i+1)}.   Pure Python, no dependencies."""
import sys
def load(fn):
    t = open(fn).read().split(); p, R, C = map(int, t[:3]); v = list(map(int, t[3:3 + 3 * R * C]))
    return p, R, C, [[v[(c * R + i) * C:(c * R + i + 1) * C] for i in range(R)] for c in range(3)]
def point(p, R, C, M, n):
    d = []
    for _ in range(C): d.append(n % p); n //= p
    assert n == 0, 'index beyond p^C'
    return tuple(sum((sum(a * b for a, b in zip(M[c][i], d)) % p) * p ** (R - 1 - i) for i in range(R)) / p ** R for c in range(3))
if __name__ == '__main__':
    p, R, C, M = load(sys.argv[1]); N = int(sys.argv[2]); s0 = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    for n in range(s0, s0 + N): print('%.15f %.15f %.15f' % point(p, R, C, M, n))
