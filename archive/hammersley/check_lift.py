"""check_lift.py -- re-run of lift_results.csv (exact toroidal separations of the Hammersley lifts, sec:hammersley).

    python3 hammersley/check_lift.py sep LO HI [CONSTR]   (from the archive root; needs bin/liftsep, see README.md)
    python3 hammersley/check_lift.py brute NMAX     (needs NumPy: independent O(N^2) check, rows with N <= NMAX)
    python3 hammersley/check_lift.py pairs          (the closest pairs at p = 5, m = 9, 10 are pairs of prop:liftcarry)

sep: for every row of lift_results.csv with LO <= N = p^m <= HI (and construction CONSTR if given), the generator matrices of the lift are rebuilt by
gen_lift.py (R = m + 4 digits, as for the archived run), bin/liftsep computes the exact toroidal separation with the slab
split K0 = floor(m/(s+1)), and its output (c, c_inslab, closest pair, |i-j|, exactness flag) is compared with the row.
brute: the same matrices, separation by brute_check.py (all pairs, integer arithmetic), compared with c to 1e-6.
pairs: for the brick-wall, residue and block-periodic lifts at p = 5, m = 9, 10, the index polynomials V_i, V_j of the
closest pair of the row (base-p digits of i, j) satisfy V_j - V_i = z^k (1 + z + ... + z^l) over F_p with l = 4 for
one ordering of the pair (the D of the proof of prop:liftcarry with n = 1, r = 1); prints k and whether the pair lies
across the torus boundary of the index coordinate (|i - j| != p^k).
Prints one line per disagreement and a summary; exit status 1 if any row disagrees. A driver, no mathematics.
"""
import csv, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
TMP = os.path.join('bin', 'ham_lift_tmp.txt')


def rows():
    with open(os.path.join(HERE, 'lift_results.csv')) as f:
        for r in csv.DictReader(f):
            r['N'] = int(r['p']) ** int(r['m'])
            yield r


def gen(r):
    os.makedirs('bin', exist_ok=True)
    m = int(r['m'])
    subprocess.run([sys.executable, os.path.join(HERE, 'gen_lift.py'), r['construction'], r['p'], r['s'], r['m'],
                    str(m + 4), TMP], check=True)


def pairs():
    n = bad = 0
    for r in rows():
        p, m = int(r['p']), int(r['m'])
        if not (r['s'] == '2' and p == 5 and m in (9, 10) and r['construction'] in ('bw', 'res', 'blk')):
            continue
        a, b = map(int, r['pair'].split(','))
        found = None
        for i, j in ((a, b), (b, a)):
            D = [((j // p ** t) - (i // p ** t)) % p for t in range(m)]   # digits of V_j - V_i over F_p
            nz = [t for t in range(m) if D[t]]
            k = nz[0] if nz else None
            if k is not None and D == [1 if k <= t <= k + 4 else 0 for t in range(m)]:
                found = (k, abs(j - i) != p ** k)
        n += 1
        if found is None:
            bad += 1
            print('NOT A PAIR OF THE PROPOSITION', r['construction'], 'm=%d' % m, r['pair'])
        else:
            print('%s m=%d pair %s: V_j - V_i = z^%d (1 + ... + z^4), across the torus boundary: %s'
                  % (r['construction'], m, r['pair'], found[0], found[1]))
    print(f'pairs: {n} rows checked, {n - bad} are pairs of the proposition')
    sys.exit(1 if bad or n == 0 else 0)


def main():
    mode = sys.argv[1]
    if mode == 'pairs':
        pairs()
    n = bad = 0
    for r in rows():
        if mode == 'sep':
            lo, hi = int(float(sys.argv[2])), int(float(sys.argv[3]))
            if not lo <= r['N'] <= hi or (len(sys.argv) > 4 and r['construction'] != sys.argv[4]):
                continue
            gen(r)
            K0 = int(r['m']) // (int(r['s']) + 1)
            out = subprocess.run([os.path.join('bin', 'liftsep'), TMP, str(K0)], check=True, capture_output=True,
                                 text=True).stdout
            g = dict(kv.split('=', 1) for kv in out.split() if '=' in kv)
            got = (float(g['c']), g['c_inslab'], int(g['K0']), set(g['pair'].split(',')), int(g['|i-j|']), g['exact'])
            want = (float(r['c']), r['c_inslab'], int(r['K0']), set(r['pair'].split(',')), int(r['absdiff']), r['exact'])
        else:
            if r['N'] > int(float(sys.argv[2])):
                continue
            gen(r)
            out = subprocess.run([sys.executable, os.path.join(HERE, 'brute_check.py'), TMP], check=True,
                                 capture_output=True, text=True).stdout
            c = float(re.search(r'c=([0-9.]+)', out).group(1))
            got, want = abs(c - float(r['c'])) <= 1e-6, True
        n += 1
        if got != want:
            bad += 1
            print('DIFFERS', r['construction'], 's=' + r['s'], 'p=' + r['p'], 'm=' + r['m'], got, want)
    print(f'{mode}: {n} rows checked, {n - bad} agree, {bad} differ')
    sys.exit(1 if bad or n == 0 else 0)


if __name__ == '__main__':
    main()
