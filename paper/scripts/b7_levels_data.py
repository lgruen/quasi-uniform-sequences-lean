"""b7_levels_data.py -- data of panel (b) of fig:levels (Section sec:intro): exact separation constants
sep(P_m) = delta(P_m) p^{m/2}, m = 1..10, of three two-dimensional sequences over F_5:

  residue      R_v (def:residue), places (0,1), theta = 1, Korobov check vector v = (2,-1) (rho = 2):
               certified at m = 2K-1 (thm:residue / cor:korobov): sep >= (rho-1) 5^{-1/2} = 0.4472
  brick wall   W^- (ex:brickwall, def:WF), staggered residue sequence, theta = -1/4, mu = (-4, 2):
               certified at m = 2K (thm:WF): sep >= (5-3)/10 = 0.2
  block        thm:block(a), places (0,1), v = (1,1), F_0 = [[-1,1],[-1,-1]], theta = 1:
               certified at m = 4K: sep >= 1 - 2/5 = 0.6

Generators: b3_gen.py (residue formulas) and audit_gen.block_matrices; exact toroidal separation by the cell-list
program sepx.cpp (bin/sepx), by brute force for m < s.

    PY scripts/b7_levels_data.py            (from paper/; about 5 s) compares with data/levels_p5.txt (exit 1 if not equal)
    PY scripts/b7_levels_data.py --write    rewrites data/levels_p5.txt
"""
import _paths
import os, sys, subprocess, tempfile, re

from b3_gen import brickwall, matrices
from audit_gen import block_matrices

SEPX = _paths.exe('sepx')
OUTF = os.path.join(_paths.DATA, 'levels_p5.txt')
WRITE = '--write' in sys.argv
p, s, R = 5, 2, 18
MMAX = int(os.environ.get('MMAX', 10))


def sep_brute(C, m):
    """exact toroidal separation by brute force over all pairs (small m; sepx needs one digit per cell)."""
    import itertools, math
    pts = []
    for V in itertools.product(range(p), repeat=m):
        pts.append([sum((sum(C[c][n][k] * V[k] for k in range(m)) % p) * p ** (-n - 1) for n in range(R))
                    for c in range(s)])
    best = min(sum(min(abs(x - y), 1 - abs(x - y)) ** 2 for x, y in zip(P, Q))
               for P, Q in itertools.combinations(pts, 2))
    return math.sqrt(best) * p ** (m / s), 'yes'


def sep(C, m):
    if m < s:
        return sep_brute(C, m)
    with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False) as f:
        f.write('%d %d %d %d\n' % (p, s, m, R))
        for c in range(s):
            for n in range(R):
                f.write(' '.join(str(C[c][n][k] % p) for k in range(m)) + '\n')
        name = f.name
    out = subprocess.run([SEPX, name], capture_output=True, text=True).stdout
    os.unlink(name)
    mo = re.search(r'sep=([0-9.]+)\s+\(exact if delta<cell side: (\w+)', out)
    return float(mo.group(1)), mo.group(2)


seqs = {
    'residue': matrices('U', p, [0, 1], 1, R, MMAX, v=[2, p - 1]),
    'brickwall': brickwall(p, R, MMAX),
    'block': block_matrices(p, s, 2, [0, 1], 1, [1, 1], [[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]], None,
                            rows=R, cols=MMAX)[0],
}
lines = ['# s=2 p=5 exact toroidal sep(P_m) (b7_levels_data.py, sepx); columns: m residue brickwall block']
for m in range(1, MMAX + 1):
    row = [m]
    for key in ('residue', 'brickwall', 'block'):
        v, ok = sep(seqs[key], m)
        row.append('%.4f' % v + ('' if ok in ('yes', 'YES', 'true', '1') else '?'))
    lines.append(' '.join(str(x) for x in row))
    print(lines[-1], flush=True)
text = '\n'.join(lines) + '\n'
if WRITE:
    open(OUTF, 'w').write(text)
    print('wrote', OUTF)
else:
    same = open(OUTF).read() == text
    print('data/levels_p5.txt:', 'identical' if same else 'DIFFERS')
    sys.exit(0 if same else 1)
