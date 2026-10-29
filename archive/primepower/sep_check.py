"""sep_check.py -- driver: the exact separations quoted with Table tab:primepower (illustrations, not part of a proof),
by bin/audit_fq (mode sep: places with codes 0, 1, 2, c* = 2, theta = 1, the row's f and k; it also checks the
relation of the staggered coordinate on the points and t = 0 at the full level). No mathematics of its own.

    python3 primepower/sep_check.py P3              last column of the table: exact sep(P_3), s = 3 rows (q^3 points)
    python3 primepower/sep_check.py min Q1,Q2,...   text after the table: the smallest sep(P_[N]) over all N <= 10^7,
                                                    s = 3 rows q = Q1, Q2, ...; the paper quotes the range 0.0144 (q = 32)
                                                    to 0.1484 (q = 49), above beta_q/q in every case
Exit status 1 if a value differs.
"""
import sys, os, subprocess, re

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rows_check import rows


def run(r, nmax):
    p = r['p']; deg = len(r['f']) - 1
    cmd = ['bin/audit_fq', str(p), str(deg), ','.join(map(str, r['f'][:-1])), '3', 'sep', str(nmax), ','.join(map(str, r['k']))]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
    sep3 = float(re.search(r'level K=1 N=\d+: sep=([\d.]+)', out).group(1))
    mn = float(re.search(r'min_N sep\(P_\[N\]\) = ([\d.]+) at N=(\d+)', out).group(1))
    frozen_ok = re.search(r'frozen identity on points: checks=\d+ fails=0', out) is not None
    t0_ok = re.search(r'cells with 2 points=0', out) is not None
    return sep3, mn, frozen_ok and t0_ok


def main():
    R = [r for r in rows() if r['s'] == 3]
    bad = 0
    if sys.argv[1] == 'P3':
        for r in R:
            sep3, mn, ok0 = run(r, r['q'] ** 3)
            ok = ok0 and f'{sep3:.4f}' == r['sep']; bad += not ok
            print(f"q={r['q']}: exact sep(P_3) = {sep3:.6f} (table {r['sep']}); relation and t=0 checks {'pass' if ok0 else 'FAIL'}: {'OK' if ok else 'DIFF'}", flush=True)
    else:
        Qs = [int(x) for x in sys.argv[2].split(',')]
        for r in R:
            if r['q'] not in Qs:
                continue
            sep3, mn, ok0 = run(r, 10 ** 7)
            v = round(mn, 4)
            ok = ok0 and mn > r['num'] / r['q'] ** 2 and 0.0144 <= v <= 0.1484
            if r['q'] == 32: ok = ok and v == 0.0144
            if r['q'] == 49: ok = ok and v == 0.1484
            bad += not ok
            print(f"q={r['q']}: min over N <= 10^7 of sep(P_[N]) = {mn:.6f} (beta_q/q = {r['num'] / r['q'] ** 2:.6f}) {'OK' if ok else 'DIFF'}", flush=True)
    print('ALL OK' if bad == 0 else 'DIFFERENCES FOUND')
    return bad


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
