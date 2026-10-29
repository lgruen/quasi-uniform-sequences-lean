"""run_freediag.py -- driver for the checks of Theorem thm:block(d) (free diagonal) and Lemma lem:signclass.
Runs the compiled programs (bin/, see block_lb/README.md) on the designs block_lb/ustar<s>.txt with the diagonals of
block_lb/freediag.txt and compares their output with the values stated in the paper. No mathematics of its own,
except that `signclass` also recomputes S and the threshold of lem:signclass from their formulas (a cross-check).

    python3 block_lb/run_freediag.py signclass
        A, S and the threshold of lem:signclass for s = 4..7, by bin/fd_signclass_audit and bin/fd_diag (mode A);
        the proof range (3+sqrt2)a*_s+1 of thm:block(c) for U*_4..U*_7.
    python3 block_lb/run_freediag.py lb PROG s pmin pmax
        exact LB(F) at every prime pmin <= p <= pmax by PROG = audit (bin/fd_lb_audit) or diag (bin/fd_diag, mode lb),
        compared with thm:block(d): (p LB)^2 = (p-A-1)^2 at every prime from 11, 23, 37, 191 (s = 4, 5, 6, 7) on;
        sqrt3/7 at p = 7 (s = 4); 1/11, 3/13, 3sqrt5/17, sqrt101/19 at p = 11, 13, 17, 19 (s = 5); LB > 0 at every
        prime 17 <= p <= 31 (s = 6) and at 17, 19, 23 and every prime 31 <= p <= 181 (s = 7). Other primes: printed.
Exit status 1 if a value differs.
"""
import sys, subprocess, math

EXPECT_SC = {4: (3, 8, 23), 5: (7, 23, 67), 6: (14, 46, 127), 7: (59, 211, 587)}   # A, S, first prime (thm:block(d))
LO = {4: 11, 5: 23, 6: 37, 7: 191}                                                    # 1-(A+1)/p from here on
QUOTED = {(4, 7): 3, (5, 11): 1, (5, 13): 9, (5, 17): 45, (5, 19): 101}              # (p LB)^2: sqrt3/7, 1/11, 3/13, 3sqrt5/17, sqrt101/19
QNAME = {(4, 7): 'sqrt3/7', (5, 11): '1/11', (5, 13): '3/13', (5, 17): '3sqrt5/17', (5, 19): 'sqrt101/19'}


def isprime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def positive_claimed(s, p):
    if s == 6:
        return 17 <= p <= 31
    if s == 7:
        return p in (17, 19, 23) or 31 <= p <= 181
    return False


def designs():
    D = {}
    for line in open('block_lb/freediag.txt'):
        if line.strip() and not line.startswith('#'):
            v = list(map(int, line.split()))
            D[v[0]] = v[1:]
    return D


def load(s):
    t = open(f'block_lb/ustar{s}.txt').read().split()
    v = list(map(int, t[1:]))
    return [[[v[(n * s + i) * s + j] for j in range(s)] for i in range(s)] for n in range(s - 1)]


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout


def signclass():
    D = designs(); bad = 0
    for s in (4, 5, 6, 7):
        d = D[s]; f = f'block_lb/ustar{s}.txt'
        o1 = run(['bin/fd_signclass_audit', f] + [str(x) for x in d]).split()
        A1 = int(o1[1].split('=')[1]); S1 = int(o1[2].split('=')[1]); thr1 = int(o1[-1].split('>=')[1])
        o2 = run(['bin/fd_diag', f, 'A'] + [str(x) for x in d]).split()
        A2 = int(o2[0].split('=')[1]); nob = int(o2[1].split('=')[1])
        # cross-check of S and the threshold from their formulas (lem:signclass)
        F = load(s)
        for c in range(s):
            F[0][c][c] = -d[c]
            for n in range(1, s - 1):
                F[n][c][c] = 0
        M = [F[0]]
        for n in range(1, s - 1):
            M.append([[M[-1][i][c] + F[n][i][c] for c in range(s)] for i in range(s)])
        S3 = max(sum(max(abs(M[j][i][c]) for j in range(s - 1)) for c in range(s)) for i in range(s))
        thr3 = next(p for p in range(S3 + 1, 10 ** 6) if (p - A1 - 1) ** 2 <= 2 * (p - S3 - 1) ** 2)
        fp = next(p for p in range(thr1, 10 ** 6) if isprime(p))
        A, S, P = EXPECT_SC[s]
        ok = A1 == A2 == A and nob == 0 and S1 == S3 == S and thr1 == thr3 and fp == P
        bad += not ok
        print(f's={s} delta={d}: A = {A1} (audit), {A2} (fd_diag; steps without backward coordinate: {nob}); '
              f'S = {S1} (audit), {S3} (formula); threshold p >= {thr1} (audit), {thr3} (formula); first prime {fp}; '
              f'paper: A={A}, S={S}, first prime {P}: {"OK" if ok else "DIFF"}')
    for s in (4, 5, 6, 7):
        a = max(-load(s)[0][c][c] for c in range(s))
        x = (3 + math.sqrt(2)) * a + 1
        print(f'U*_{s}: a*_s = {a}, (3+sqrt2)a*_s+1 = {x:.2f}, first prime {next(p for p in range(math.ceil(x), 10 ** 6) if isprime(p))}')
    print('ALL OK' if bad == 0 else 'DIFFERENCES FOUND')
    return bad


def lb(prog, s, lo, hi):
    d = designs()[s]; f = f'block_lb/ustar{s}.txt'; A1 = EXPECT_SC[s][0] + 1
    nclaim = nok = 0
    for p in range(lo, hi + 1):
        if not isprime(p) or p <= max(3, s - 1):
            continue
        if prog == 'audit':
            out = run(['bin/fd_lb_audit', f, str(p)] + [str(x) for x in d])
        else:
            out = run(['bin/fd_diag', f, 'lb', str(p)] + [str(x) for x in d])
        sq = int(out.split('sumsq=')[1].split()[0])
        lbv = math.sqrt(sq) / p
        if p >= LO[s]:
            claim, ok = f'1-{A1}/p', sq == (p - A1) ** 2
        elif (s, p) in QUOTED:
            claim, ok = QNAME[(s, p)], sq == QUOTED[(s, p)]
        elif positive_claimed(s, p):
            claim, ok = 'LB>0', sq > 0
        else:
            claim, ok = None, True
        if claim:
            nclaim += 1; nok += ok
            print(f's={s} p={p} (p LB)^2={sq} LB={lbv:.6f} p-p*LB={p - math.sqrt(sq):.4f} claim {claim}: {"OK" if ok else "DIFF"}')
        else:
            print(f's={s} p={p} (p LB)^2={sq} LB={lbv:.6f} p-p*LB={p - math.sqrt(sq):.4f} (no claim)')
    print(f'{prog} s={s} primes {lo}..{hi}: {nok}/{nclaim} claimed values OK')
    return nclaim - nok


if __name__ == '__main__':
    if sys.argv[1] == 'signclass':
        sys.exit(1 if signclass() else 0)
    elif sys.argv[1] == 'lb':
        sys.exit(1 if lb(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])) else 0)
