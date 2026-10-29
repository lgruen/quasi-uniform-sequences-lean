"""best_check.py -- driver: exhaustive statements around Table tab:primepower, by the compiled programs in bin/ (see
primepower/README.md). No mathematics of its own; it parses the programs' output and compares with the paper.

    python3 primepower/best_check.py fq      rows with s <= 3: max of beta_q over ALL monic irreducible f and ALL weights
    python3 primepower/best_check.py ppb       = the table value, by bin/audit_fq (all), bin/pp_best_audit, bin/pp_search (pb);
    python3 primepower/best_check.py pb        also the caption: q = 25, s = 2: 5/25 (x^2+2) to 8/25 (x^2+3);
                                               q = 32, s = 3: positive for 2 of the 6 irreducible quintics
    python3 primepower/best_check.py codes   text after the table: beta_q = 0 for q = 8, 9 (s = 3) for every digit code
                                               (bin/pp_anycode_audit, bin/pp_search any) and for q = 16, 27 (s = 3) for
                                               every F_p-linear code (bin/pp_search lin)
    python3 primepower/best_check.py zeros PROG   beta_q = 0 for every power-basis code (every monic irreducible f) and
                                               every weight: s = 4, q = 16, 25, 27, 32, 64, 81; s = 5, q = 49;
                                               PROG = pb (bin/pp_search) or ppb (bin/pp_best_audit)
Exit status 1 if a value differs.
"""
import sys, os, subprocess, re

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rows_check import rows, poly

PR = {8: (2, 3), 9: (3, 2), 16: (2, 4), 25: (5, 2), 27: (3, 3), 32: (2, 5), 49: (7, 2), 64: (2, 6), 81: (3, 4),
      121: (11, 2), 125: (5, 3), 128: (2, 7), 169: (13, 2)}


def run(cmd, env=None):
    e = dict(os.environ); e.update(env or {})
    return subprocess.run(cmd, capture_output=True, text=True, check=True, env=e).stdout


def per_f(prog, p, r, s):
    """{f as polynomial string: beta*q} for every monic irreducible f of degree r over F_p"""
    D = {}
    if prog == 'fq':
        for line in run(['bin/audit_fq', str(p), str(r), 'all', str(s), 'beta']).splitlines():
            m = re.match(r'Q=(\d+) f=\(([\d ]+)\) s=\d+ .* = ([\d.e+]+)/\d+', line)
            D[poly([int(x) for x in m.group(2).split()])] = int(round(float(m.group(3))))
    elif prog == 'ppb':
        for line in run(['bin/pp_best_audit', str(p), str(r), str(s)], env={'V': '1'}).splitlines():
            m = re.match(r'f=([\d ]+): (\d+)/\d+', line)
            if m:
                D[poly([int(x) for x in m.group(1).split()][::-1])] = int(m.group(2))
    elif prog == 'pb':
        for line in run(['bin/pp_search', 'pb', str(p), str(r), str(s)]).splitlines():
            m = re.match(r's=\d+ q=\d+ f=(\S+) best=(\d+)/\d+', line)
            if m:
                D[m.group(1)] = int(m.group(2))
    return D


def best(prog):
    bad = 0; n = 0
    for row in rows():
        if row['s'] > 3:
            continue
        p, r = PR[row['q']]
        D = per_f(prog, p, r, row['s'])
        mx = max(D.values())
        ok = mx == row['num'] and D[row['fstr']] == row['num']; bad += not ok; n += 1
        print(f"{prog}: s={row['s']} q={row['q']}: {len(D)} irreducible f, max beta*q = {mx}, table f {row['fstr']}: "
              f"{D[row['fstr']]} (table {row['num']}) {'OK' if ok else 'DIFF'}", flush=True)
    # caption of tab:primepower
    D = per_f(prog, 5, 2, 2)
    lo = min(D.values()); hi = max(D.values())
    ok = (lo, hi) == (5, 8) and D['x^2+2'] == 5 and D['x^2+3'] == 8; bad += not ok
    print(f"{prog}: caption q=25 s=2: from {lo}/25 to {hi}/25 (x^2+2: {D['x^2+2']}/25, x^2+3: {D['x^2+3']}/25) {'OK' if ok else 'DIFF'}")
    D = per_f(prog, 2, 5, 3)
    pos = sorted(f for f in D if D[f] > 0)
    ok = len(D) == 6 and len(pos) == 2; bad += not ok
    print(f"{prog}: caption q=32 s=3: positive for {len(pos)} of {len(D)} quintics ({', '.join(pos)}) {'OK' if ok else 'DIFF'}")
    print(f'{prog}: {n - bad + 2}/{n + 2} statements OK')
    return bad


def codes():
    bad = 0
    for p, r, s, f in [(2, 3, 3, [1, 1, 0, 1]), (3, 2, 3, [1, 0, 1])]:
        o1 = run(['bin/pp_anycode_audit', str(p), str(r), str(s)] + [str(x) for x in f]).strip()
        o2 = run(['bin/pp_search', 'any', str(p), str(r), str(s), '0']).strip()
        ok = o1.endswith(f'= 0/{p ** r}') and f' max=0/{p ** r} ' in o2 + ' '; bad += not ok
        print(f'every digit code: {o1} | {o2} {"OK" if ok else "DIFF"}')
    for p, r, s in [(2, 4, 3), (3, 3, 3)]:
        o = run(['bin/pp_search', 'lin', str(p), str(r), str(s), '0']).strip()
        ok = f' max=0/{p ** r} ' in o + ' '; bad += not ok
        print(f'every F_p-linear code: {o} {"OK" if ok else "DIFF"}')
    print('ALL OK' if bad == 0 else 'DIFFERENCES FOUND')
    return bad


def zeros(prog):
    bad = 0
    for s, q in [(4, 16), (4, 25), (4, 27), (4, 32), (4, 64), (4, 81), (5, 49)]:
        p, r = PR[q]
        D = per_f(prog, p, r, s)
        ok = max(D.values()) == 0; bad += not ok
        print(f"{prog}: s={s} q={q}: {len(D)} irreducible f, max over f and weights beta*q = {max(D.values())} {'OK' if ok else 'DIFF'}", flush=True)
    print('ALL OK' if bad == 0 else 'DIFFERENCES FOUND')
    return bad


if __name__ == '__main__':
    m = sys.argv[1]
    b = best(m) if m in ('fq', 'ppb', 'pb') else codes() if m == 'codes' else zeros(sys.argv[2])
    sys.exit(1 if b else 0)
