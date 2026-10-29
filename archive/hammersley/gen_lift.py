"""gen_lift.py -- generator matrices of the Hammersley lifts {(i/p^m, x_i)} of the paper's sequences, in the input
format of liftsep.cpp / sepx.cpp ("p d m R" then d*R rows of m entries).

Usage: python gen_lift.py CONSTR p s m R out [nolift]
CONSTR: faure   (I, P, ..., P^{s-1})                       -- classical Faure sequence (Hammersley lift = Faure net)
        bw      brick wall W^- (s = 2, def:WF)              -- certified at m = 2K (thm:WF)
        stag    staggered residue, dyadic weights (s = 3)   -- certified at m = sK (cor:dyadic)
        res     residue sequence R_v, Korobov v (cor:korobov), places 0..s-1, theta = 1 -- certified at m = sK-1
        blk     block-periodic residue sequence (thm:block (a) s=2, (b) s=3) -- certified at m = s^2 K
Generators come from b3_gen.py and audit_gen.py of this directory (copies of paper/scripts/b3_gen.py, audit_gen.py).
"""
import os, sys
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from b3_gen import brickwall, matrices, inv
from audit_gen import block_matrices, pascal


def seq_matrices(constr, p, s, R, m):
    if constr == 'faure':
        return [pascal(c % p, R, m, p) for c in range(s)]
    if constr == 'bw':
        assert s == 2
        return brickwall(p, R, m)
    if constr == 'stag':
        # dyadic weights k_{c_i} = 2^{i-s} (cor:dyadic), c* = s-1, places 0..s-1, theta = 1, mu_* = 1, mu_c = -1/k_c
        k = [pow(inv(2, p), s - i, p) for i in range(1, s)]
        mu = [(-inv(kc, p)) % p for kc in k] + [1]
        return matrices('R', p, list(range(s)), 1, R, m, cstar=s - 1, mu=mu)
    if constr == 'res':
        rho = int(round(p ** (1.0 / s)))
        while rho ** s > p: rho -= 1
        while (rho + 1) ** s <= p: rho += 1
        v = [pow(rho, c + 1, p) for c in range(s - 1)] + [p - 1]
        return matrices('U', p, list(range(s)), 1, R, m, v=v)
    if constr == 'blk':
        if s == 2:
            a, vv, F = [0, 1], [1, 1], [[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]]
        else:
            M = [[-1, -1, 1], [1, -1, -1], [-1, 1, -1]]; J = [[0, 0, -1], [-1, 0, 0], [0, -1, 0]]
            a, vv, F = [0, 2, 1], [Fraction(1, 2), Fraction(1, 2), -1], [M, J, [[0] * 3 for _ in range(3)]]
        C, _ = block_matrices(p, s, s, a, 1, vv, F, None, rows=R, cols=m)
        return C
    raise KeyError(constr)


def main():
    constr, p, s, m, R, out = sys.argv[1], *map(int, sys.argv[2:6]), sys.argv[6]
    nolift = len(sys.argv) > 7 and sys.argv[7] == 'nolift'
    C = seq_matrices(constr, p, s, R, m)
    mats = []
    if not nolift:
        J = [[1 if (n < m and k == m - 1 - n) else 0 for k in range(m)] for n in range(R)]
        mats.append(J)
    mats += C
    with open(out, 'w') as f:
        f.write('%d %d %d %d\n' % (p, len(mats), m, R))
        for M in mats:
            for row in M[:R]:
                f.write(' '.join(str(x % p) for x in row[:m]) + '\n')


if __name__ == '__main__':
    main()
