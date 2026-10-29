#!/usr/bin/env python3
"""fd_s45_check.py -- the program of the Lean stage for s = 4, 5 (third evaluation; computation unchanged): exact
one-digit relaxation LB(F) of `thm:block`(iii) for designs with the off-diagonal entries of U*_4 / U*_5 (its own copy
of the matrices, equal to block_lb/ustar4.txt, ustar5.txt) and a chosen diagonal of F_0 (`thm:block`(d)).

LB(F) = min over steps e in {-1,0,1}^s (e != 0) and carry depths j_c in [0, s-2] of the moving coordinates of
(sum_i f_1(e_i, sigma_i)^2)^(1/2), sigma_i = sum_c e_c M^(j_c)[i][c], with the integer numerators
g = p f_1. Prints p - p*LB(F) (so `1 - A/p` shows as A), rounded to 3 decimals. Also checks the p-independent
hypothesis of Lemma `lem:signclass` (number of violating steps) and its threshold ("written range").

Usage (from the archive root): uv run --with sympy python block_lb/fd_s45_check.py
"""
import itertools
import math
from sympy import primerange

U4 = [[[-5, 2, 1, 2], [1, -3, -1, -1], [1, 2, -5, -2], [1, 1, 1, -3]],
      [[0, -3, -1, -1], [-2, 0, 2, 1], [-1, -1, 0, 3], [0, -1, 0, 0]],
      [[0, 2, 0, -1], [2, 0, -2, 0], [0, -1, 0, -2], [-1, 0, -1, 0]]]
U5 = [[[-16, 6, 2, 2, 6], [1, -8, -2, -1, -2], [1, 6, -12, -2, -3], [1, 3, 2, -12, -6], [1, 2, 1, 2, -7]],
      [[0, -11, -3, -1, -1], [-3, 0, 5, 1, 1], [-2, -5, 0, 3, 2], [-1, -4, -1, 0, 7], [0, -3, -1, 1, 0]],
      [[0, 6, 0, -2, -4], [2, 0, -3, 0, 1], [0, 1, 0, -3, 1], [-1, 1, 1, 0, -3], [-1, 1, 0, -3, 0]],
      [[0, -1, 1, 1, -1], [-1, 0, 1, 0, 0], [1, -1, 0, 2, 0], [1, 0, -2, 0, 3], [0, 0, 0, 1, 0]]]


def with_diag(F, d):
    G = [[r[:] for r in X] for X in F]
    for c, x in enumerate(d):
        G[0][c][c] = -x
    return G


def partial(F):
    s = len(F[0])
    M = [F[0]]
    for n in range(1, s - 1):
        M.append([[M[-1][i][c] + F[n][i][c] for c in range(s)] for i in range(s)])
    return M


def steps(s):
    for e in itertools.product((-1, 0, 1), repeat=s):
        if any(e):
            mov = [c for c in range(s) if e[c]]
            for js in itertools.product(range(s - 1), repeat=len(mov)):
                yield e, mov, js


def lb_num2(F, p):
    s = len(F[0])
    M = partial(F)
    best = None
    for e, mov, js in steps(s):
        tot = 0
        for i in range(s):
            r = sum(e[c] * M[j][i][c] for c, j in zip(mov, js)) % p
            if e[i] == 0:
                g = 0 if r == 0 else min(r, p - r) - 1
            elif e[i] == 1:
                g = p - 1 if r == 0 else r - 1
            else:
                g = p - 1 - r
            tot += g * g
        best = tot if best is None else min(best, tot)
    return best


def signclass(F, A):
    s = len(F[0])
    M = partial(F)
    bad = 0
    for e, mov, js in steps(s):
        sig = [sum(e[c] * M[j][i][c] for c, j in zip(mov, js)) for i in range(s)]
        back = [i for i in range(s) if e[i] != 0 and e[i] * sig[i] <= 0]
        if not (any(abs(sig[i]) <= A for i in back) or len(back) >= 2):
            bad += 1
    B = [[max(abs(M[j][i][c]) for j in range(s - 1)) for c in range(s)] for i in range(s)]
    S = max(sum(r) for r in B)
    p0 = next(p for p in range(2, 10 ** 6) if S < p and (p - A - 1) ** 2 <= 2 * (p - S - 1) ** 2)
    return bad, S, p0


PR = list(primerange(5, 110)) + [211, 401, 1009, 10007, 100003]
for name, F, d, A in [('U*_4', U4, (5, 3, 5, 3), 5), ('s=4 diag 3', U4, (3, 3, 3, 3), 3),
                      ('U*_5', U5, (16, 8, 12, 12, 7), 16), ('s=5 diag 7', U5, (7,) * 5, 7)]:
    G = with_diag(F, d)
    vals = [(p, round(p - math.sqrt(lb_num2(G, p)), 3)) for p in PR if p > max(d)]
    bad, S, p0 = signclass(G, A)
    print(name, 'p - p*LB:', vals)
    print('   sign-class(A=%d): violating steps %d, S = %d, written range p >= %d' % (A, bad, S, p0))
