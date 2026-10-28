"""run_third.py -- driver (no mathematics) for the third program of Table tab:ca for thm:block(c): evaluates the
one-digit relaxation with lb.py (variant noH2: jitter 1 on every coordinate, carry depths capped at s-1) on the designs
U*_4, U*_5 of ustar_finite.json, at the primes 7..31 and 101 (s = 4) and 37..101 (s = 5), and compares with
1 - (a*_s + 1)/p, a*_s = largest diagonal entry of -F_0 (5 for s = 4, 16 for s = 5).
usage (from the archive root): python3 block_lb/run_third.py [all]   ('all': every prime 7..109 / 19..109 instead)"""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lb import LB
D = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ustar_finite.json')))
isp = lambda n: n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
full = len(sys.argv) > 1 and sys.argv[1] == 'all'
R = {4: [q for q in range(7, 110) if isp(q) and (full or q <= 31 or q == 101)],
     5: [q for q in range(19, 110) if isp(q) and (full or 37 <= q <= 101)]}
bad = 0
for s in (4, 5):
    F0 = D[str(s)]['F']; astar = max(-F0[0][c][c] for c in range(s)); ok = 0
    for q in R[s]:
        F = [[[x % q for x in r] for r in Fn] for Fn in F0]
        v, arg = LB(q, F, False); tgt = 1 - (astar + 1) / q; good = abs(v - tgt) < 1e-12
        ok += good; bad += not good
        print(f's={s} p={q}: LB(F) = {v:.6f}, 1-(a*+1)/p = {tgt:.6f} {"OK" if good else "DIFF"}', flush=True)
    print(f's={s} a*={astar}: {ok}/{len(R[s])} primes OK')
print('ALL OK' if not bad else 'FAILURES: %d' % bad)
