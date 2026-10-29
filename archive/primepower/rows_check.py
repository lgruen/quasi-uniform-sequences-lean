"""rows_check.py -- driver: the 26 rows of Table tab:primepower (primepower/table_primepower.tsv) evaluated by the
archived programs. No mathematics of its own (it only formats the polynomial of each row from its coefficients, to
check the transcription of the f column).

    python3 primepower/rows_check.py audit2     beta_q at the row's (f, k) by primepower/audit2_primepower.py (second audit)
    python3 primepower/rows_check.py ppbeta     beta_q at the row's (f, k) by primepower/pp_beta_audit.py (audit of the
                                                Lean stage)
    uv run --with numpy python primepower/rows_check.py third
                                                rows with s <= 3: best beta_q over ALL weights for the row's f, by the
                                                third program practice/rebuild_check.py (independent re-implementation)
Exit status 1 if a value differs from the table.
"""
import sys, os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def rows():
    out = []
    for line in open(os.path.join(HERE, 'table_primepower.tsv')):
        if line.startswith('#') or not line.strip():
            continue
        s, q, p, fc, fs, k, b, sep = line.rstrip('\n').split('\t')
        num, den = map(int, b.split('/'))
        assert den == int(q)
        out.append(dict(s=int(s), q=int(q), p=int(p), f=[int(x) for x in fc.split(',')], fstr=fs,
                        k=[int(x) for x in k.split(',')], num=num, sep=sep))
    return out


def poly(f):
    t = []
    for i in range(len(f) - 1, -1, -1):
        c = f[i]
        if c == 0:
            continue
        mon = '' if i == 0 else ('x' if i == 1 else f'x^{i}')
        t.append((str(c) if (c != 1 or i == 0) else '') + mon)
    return '+'.join(t)


def main(mode):
    R = rows(); bad = 0; n = 0
    for r in R:
        assert poly(r['f']) == r['fstr'], (poly(r['f']), r['fstr'])
        assert r['p'] ** (len(r['f']) - 1) == r['q']
    if mode == 'audit2':
        import audit2_primepower as A
        for r in R:
            q, add, mul, neg, D = A.mk_field(r['p'], r['f'])
            v = A.beta(r['s'], r['k'], q, add, mul, neg, D)
            ok = v == r['num']; bad += not ok; n += 1
            print(f"s={r['s']} q={r['q']} f={r['fstr']} k={r['k']}: beta*q={v} (table {r['num']}) {'OK' if ok else 'DIFF'}", flush=True)
    elif mode == 'ppbeta':
        import pp_beta_audit as B
        for r in R:
            F = B.mk(r['p'], r['f'])
            v = B.beta(F, r['s'], r['k'])
            ok = v == r['num'] and F[6]; bad += not ok; n += 1
            print(f"s={r['s']} q={r['q']} f={r['fstr']} irreducible={F[6]} k={r['k']}: beta*q={v} (table {r['num']}) {'OK' if ok else 'DIFF'}", flush=True)
    elif mode == 'third':
        sys.path.insert(0, os.path.join(HERE, '..', 'practice'))
        import rebuild_check as C
        for r in R:
            if r['s'] > 3:
                continue
            v, Q, kk = C.beta_q(r['p'], r['f'], r['s'])
            ok = v == r['num']; bad += not ok; n += 1
            print(f"s={r['s']} q={r['q']} f={r['fstr']}: max over weights beta*q={v} at k={kk} (table {r['num']}, k={r['k']}) {'OK' if ok else 'DIFF'}", flush=True)
    print(f'{mode}: {n - bad}/{n} rows OK')
    return bad


if __name__ == '__main__':
    sys.exit(1 if main(sys.argv[1]) else 0)
