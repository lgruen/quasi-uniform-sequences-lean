"""box_check.py -- third, independent evaluation of the exact values lambda_jit(Lambda_v)^2 behind the
certified bounds of tab:residue (both columns) and of the residue rows of tab:practice (thm:residue, cor:korobov).

Written from the definitions of Section 5 only: Lambda_v = {b in Z^s : sum_c v_c b_c = 0 mod p},
lambda_jit(Lambda)^2 = min over b != 0 in Lambda of sum_c max(0, |b_c| - 1)^2.  If that minimum is <= L, a minimising
b has |b_c| <= 1 + floor(sqrt(L)) in every coordinate; so the claim "lambda_jit^2 = L" is checked by enumerating the box
|b_c| <= 1 + floor(sqrt(L)) in the first s-1 coordinates and solving the congruence for the last one (the box is narrower
than p/2, so the centred solution is the only candidate). No code of the search programs is used.
    python3 residue_tables/box_check.py      (from the archive root; about a second)
"""
import itertools, math


def ljit2_upto(v, p, L):
    s = len(v)
    B = 1 + math.isqrt(L)
    assert 2 * B + 1 < p
    inv_last = pow(v[-1] % p, p - 2, p)
    best = None
    for head in itertools.product(range(-B, B + 1), repeat=s - 1):
        t = sum(vc * b for vc, b in zip(v[:-1], head)) % p
        last = (-t * inv_last) % p
        if last > p // 2:
            last -= p
        if abs(last) > B:
            continue
        b = head + (last,)
        if not any(b):
            continue
        val = sum(max(0, abs(x) - 1) ** 2 for x in b)
        if best is None or val < best:
            best = val
    return best


def korobov(s, p):
    rho = int(round(p ** (1 / s)))
    while rho ** s > p:
        rho -= 1
    while (rho + 1) ** s <= p:
        rho += 1
    return [rho ** k for k in range(1, s)] + [-1], rho


# (s, p, v, claimed lambda_jit^2) -- tab:residue "best v found" column (same list as check_vectors.tsv)
best = [(2, 11, [3, -1], 4), (2, 17, [4, -1], 9), (2, 37, [6, -1], 25), (2, 101, [30, -1], 85), (2, 1009, [122, -1], 1060),
        (3, 11, [9, 4, -1], 1), (3, 17, [6, 2, -1], 1), (3, 37, [9, 3, -1], 4), (3, 101, [35, 13, -1], 13),
        (3, 1009, [105, 11, -1], 89), (3, 10007, [7775, 9087, -1], 498),
        (4, 17, [9, 15, 4, -1], 1), (4, 37, [14, 4, 2, -1], 1), (4, 101, [27, 9, 3, -1], 4), (4, 1009, [443, 201, 758, -1], 25),
        (5, 37, [16, 8, 4, 2, -1], 1), (5, 101, [2, 4, 8, 16, -1], 1), (5, 1009, [560, 313, 92, 858, -1], 9)]
# tab:practice residue rows
practice = [(3, 13, [5, 3, 6], 1), (3, 17, [4, 10, 16], 1), (3, 23, [4, 14, 20], 2), (3, 31, [10, 30, 7], 4)]
ok = True
for s, p, v, L in best + practice:
    got = ljit2_upto(v, p, L)
    good = (got == L)
    ok &= good
    print('s=%d p=%5d v=%-24s claimed %4d  computed %s  bound p^(-1/s)*ljit = %.5f %s'
          % (s, p, str(v), L, got, p ** (-1 / s) * math.sqrt(L), '' if good else '  <-- MISMATCH'))
# Korobov column: lambda_jit = rho - 1 in every row
for s, p in [(2, 11), (2, 17), (2, 37), (2, 101), (2, 1009), (3, 11), (3, 17), (3, 37), (3, 101), (3, 1009), (3, 10007),
             (4, 17), (4, 37), (4, 101), (4, 1009), (5, 37), (5, 101), (5, 1009)]:
    v, rho = korobov(s, p)
    L = (rho - 1) ** 2
    got = ljit2_upto(v, p, L)
    good = (got == L)
    ok &= good
    print('Korobov s=%d p=%5d rho=%d: ljit^2 = %s (claimed %d), bound %.5f%s'
          % (s, p, rho, got, L, p ** (-1 / s) * (rho - 1), '' if good else '  <-- MISMATCH'))
print('ALL OK' if ok else 'FAIL')
