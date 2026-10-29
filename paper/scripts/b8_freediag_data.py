"""b8_freediag_data.py -> data/freediag.json (read by b8_freediag.py and by explainers/gen_data.py, key 'freediag'):
the certified constants LB(F) of the block-periodic designs of thm:block(c) (U*_s with the nets' diagonal) and
thm:block(d) (U*_s off the diagonal, F_0[c][c] = -delta_c), s = 4..7, at primes inside the ranges stated in the paper
(tab:block).  Each value is the exact one-digit relaxation (lem:cert, j = 1), evaluated by the independent C++ program
lb.cpp (bin/lb) on the design files data/ustar<s>.txt (the same files as archive/block_lb/ustar<s>.txt), and asserted
against the paper: 1-(a*_s+1)/p resp. 1-(A+1)/p on the stated ranges, and the quoted small-prime values.

    PY scripts/b8_freediag_data.py          (from paper/; about 10 s) compares with data/freediag.json (exit 1 if not equal)
    PY scripts/b8_freediag_data.py --write  rewrites data/freediag.json
"""
import _paths
import json, math, os, subprocess, sys
U = _paths.DATA
DELTA = {4: [3] * 4, 5: [7] * 5, 6: [3, 12, 13, 14, 13, 13], 7: [41, 44, 59, 57, 56, 6, 32]}
ASTAR = {4: 5, 5: 16, 6: 43, 7: 170}
A = {4: 3, 5: 7, 6: 14, 7: 59}
FROM_U = {4: 7, 5: 19, 6: 191, 7: 757}            # thm:block(c): c.a. from 7 / 19, written proof (3+sqrt2)a*+1 for s = 6, 7
FROM_D = {4: 11, 5: 23, 6: 37, 7: 191}            # thm:block(d)
EXTRA_D = {4: {7: math.sqrt(3) / 7}, 5: {11: 1 / 11, 13: 3 / 13, 17: 3 * math.sqrt(5) / 17, 19: math.sqrt(101) / 19}}
POS_D = {6: '17-31', 7: '17, 19, 23, 31-181'}     # further primes with LB(F) > 0 (values not quoted in the paper)
isprime = lambda n: n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
grid = [p for p in range(7, 114) if isprime(p)] + [127, 151, 191, 211, 251, 307, 359, 401, 449, 503, 557, 577, 601, 757, 809, 1009]
exe = _paths.exe('lb')
def lb(s, p, d=None):
    r = subprocess.run([exe, os.path.join(U, 'ustar%d.txt' % s), str(p)] + ([str(x) for x in d] if d else []),
                       capture_output=True, text=True, check=True).stdout
    return float(r.split('(LB = ')[1].split(')')[0])
out = {'astar': ASTAR, 'A': A, 'delta': DELTA, 'fromU': FROM_U, 'fromD': FROM_D, 'posD': POS_D, 'series': {}}
for s in (4, 5, 6, 7):
    us = [(p, lb(s, p)) for p in grid if p >= FROM_U[s] and (s < 7 or p in (757, 809, 1009))]
    for p, v in us:
        assert abs(v - (1 - (ASTAR[s] + 1) / p)) < 2e-6, (s, p, v)
    ds = []
    for p in grid:
        if p >= FROM_D[s] or p in EXTRA_D.get(s, {}):
            if s == 7 and p < 191:
                continue
            v = lb(s, p, DELTA[s])
            want = EXTRA_D[s][p] if p in EXTRA_D.get(s, {}) else 1 - (A[s] + 1) / p
            assert abs(v - want) < 2e-6, (s, p, v, want)
            ds.append((p, v))
    out['series'][str(s)] = {'ustar': [[p, round(v, 6)] for p, v in us], 'diag': [[p, round(v, 6)] for p, v in ds]}
    print('s', s, len(us), len(ds))
OUTF = os.path.join(_paths.DATA, 'freediag.json')
text = json.dumps(out, separators=(',', ':'))
if '--write' in sys.argv:
    open(OUTF, 'w').write(text)
    print('wrote', OUTF)
else:
    same = open(OUTF).read() == text
    print('data/freediag.json:', 'identical' if same else 'DIFFERS')
    sys.exit(0 if same else 1)
