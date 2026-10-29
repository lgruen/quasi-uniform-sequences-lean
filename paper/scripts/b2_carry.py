"""b2_carry.py -- Figure fig:carry (Section sec:fail), built from the real points.

    PY scripts/b2_carry.py [--out DIR]          (from paper/; PY: see README.md; < 5 s)

The two-dimensional Faure sequence (I, P) in base p = 5 (= the Halton-type sequence with bases z, z - 1), prefix P_5
(3125 points). The points are generated from the generator matrices (coordinate 0: index digits; coordinate 1:
Pascal matrix P_1, i.e. Taylor digits at 1), exact integer coordinates in units of 5^-5. The script computes the exact
closest pair of P_5 by brute force (Euclidean distance in the cube and toroidal distance), checks that it is the pair
of indices (1, 3120) of Remark rem:faurerate (Q = 5), prints its digits, and draws (a) the whole prefix, (b) a zoom on
the pair with the elementary intervals, (c) the digit strings. Output: fig_carry.pdf / .png.
"""
import _paths
import os, math
import numpy as np
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.collections import LineCollection

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = _paths.OUT
plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42})
WIDTH = 6.3
INK, GRID, FINE, LATE, ACC, ACC2, SHADE = '#111111', '#c8c8c8', '#e2e2e2', '#6f6f6f', '#2b6cb0', '#c05621', '#dde6f2'
CARRYSH = '#f6dfcf'

p, m = 5, 5
N = p ** m


def digits_of(i):
    return [(i // p ** k) % p for k in range(m)]


# generator matrices: C_0 = I, C_1 = Pascal P_1 (P[n][k] = binom(k, n)), m x m
P1 = np.array([[math.comb(k, n) % p for k in range(m)] for n in range(m)], dtype=np.int64)
V = np.array([digits_of(i) for i in range(N)], dtype=np.int64)          # rows: index digits V_0..V_4
Y0 = V % p                                                                # output digits of coordinate 0
Y1 = (V @ P1.T) % p                                                       # output digits of coordinate 1
w = p ** (m - 1 - np.arange(m))                                           # digit n has weight p^(m-1-n) (units p^-m)
X0, X1 = Y0 @ w, Y1 @ w                                                   # integer coordinates in units of p^-m

# exact closest pair (squared distances in units p^-2m), Euclidean in the cube and toroidal
best, bestT = None, None
for i in range(N - 1):
    d0 = np.abs(X0[i + 1:] - X0[i]); d1 = np.abs(X1[i + 1:] - X1[i])
    dd = d0 * d0 + d1 * d1
    t0 = np.minimum(d0, N - d0); t1 = np.minimum(d1, N - d1); tt = t0 * t0 + t1 * t1
    j = int(np.argmin(dd)); k = int(np.argmin(tt))
    if best is None or dd[j] < best[0]: best = (int(dd[j]), i, i + 1 + j)
    if bestT is None or tt[k] < bestT[0]: bestT = (int(tt[k]), i, i + 1 + k)
d2, i1, i2 = best
print('closest pair (cube):', (i1, i2), 'dist^2 =', d2, '* 5^-10  -> dist =', math.sqrt(d2) / N,
      ' sep = dist*N^(1/2) =', round(math.sqrt(d2) / N * math.sqrt(N), 4))
print('closest pair (torus):', bestT[1:], 'dist^2 =', bestT[0])
assert (i1, i2) == (1, 3120) and d2 == 17 and bestT[0] == 17
for i in (3120, 1):
    print(i, 'coord0 digits', Y0[i], 'coord1 digits', Y1[i], ' point', X0[i] / N, X1[i] / N)
A, B = 3120, 1

fig = plt.figure(figsize=(WIDTH, 2.35))
axa = fig.add_axes([0.005, 0.07, 0.30, 0.86])
axb = fig.add_axes([0.335, 0.07, 0.30, 0.86])
axc = fig.add_axes([0.655, 0.07, 0.345, 0.86])

# (a) the whole prefix
segs = [[(k / p, 0), (k / p, 1)] for k in range(1, p)] + [[(0, k / p), (1, k / p)] for k in range(1, p)]
axa.add_collection(LineCollection(segs, colors=GRID, linewidths=0.35, zorder=0))
axa.scatter(X0 / N, X1 / N, s=0.35, c=LATE, lw=0, zorder=1)
zx, zy, zr = 0.2, 0.2, 0.012
axa.add_patch(Rectangle((zx - zr, zy - zr), 2 * zr, 2 * zr, fill=False, ec=ACC2, lw=0.7, zorder=3))
axa.scatter([X0[A] / N, X0[B] / N], [X1[A] / N, X1[B] / N], s=4, c=ACC2, lw=0, zorder=4)
axa.set_aspect('equal'); axa.set_xlim(0, 1); axa.set_ylim(0, 1); axa.set_xticks([]); axa.set_yticks([])
for s_ in axa.spines.values(): s_.set_color(GRID)
axa.set_title('(a) $P_5$: 3125 points, base 5', pad=3)

# (b) zoom: x in [0.2-r, 0.2+r], y likewise; fine grid of side 5^-4, the line x = 1/5, the shared y-interval
r = 0.006
x0, x1, y0, y1 = zx - r, zx + r, zy - r * 0.55, zy + r * 1.45
f = p ** -4
xs = np.arange(math.ceil(x0 / f) * f, x1 + 1e-12, f); ys = np.arange(math.ceil(y0 / f) * f, y1 + 1e-12, f)
axb.add_collection(LineCollection([[(x, y0), (x, y1)] for x in xs] + [[(x0, y), (x1, y)] for y in ys],
                                  colors=FINE, linewidths=0.45, zorder=0))
axb.add_patch(Rectangle((x0, 0.2), x1 - x0, f, fc=SHADE, ec='none', zorder=0.5))
axb.plot([0.2, 0.2], [y0, y1], color=INK, lw=0.9, zorder=1)
sel = (X0 / N > x0) & (X0 / N < x1) & (X1 / N > y0) & (X1 / N < y1)
axb.scatter(X0[sel] / N, X1[sel] / N, s=7, c=LATE, lw=0, zorder=2)
axb.scatter([X0[A] / N, X0[B] / N], [X1[A] / N, X1[B] / N], s=14, c=ACC2, lw=0, zorder=3)
axb.annotate('index 3120', (X0[A] / N, X1[A] / N), xytext=(-25, 9), textcoords='offset points', fontsize=6.5,
             color=ACC2, ha='center', arrowprops=dict(arrowstyle='-', color=ACC2, lw=0.4))
axb.annotate('index 1', (X0[B] / N, X1[B] / N), xytext=(16, -10), textcoords='offset points', fontsize=6.5,
             color=ACC2, ha='left', arrowprops=dict(arrowstyle='-', color=ACC2, lw=0.4))
axb.text(0.2, y1 - 0.0004, r'$y_0=\frac{1}{5}$', ha='center', va='top', fontsize=6.5,
         bbox=dict(fc='white', ec='none', pad=0.6))
axb.text(x1 - 0.0002, 0.2 + f / 2, r'shared $y_1$-interval' + '\n' + r'of length $5^{-4}$', ha='right',
         va='center', fontsize=6.0, color=ACC)
axb.set_aspect('equal'); axb.set_xlim(x0, x1); axb.set_ylim(y0, y1); axb.set_xticks([]); axb.set_yticks([])
for s_ in axb.spines.values(): s_.set_color(ACC2)
axb.set_title(r'(b) zoom, grid of side $5^{-4}$', pad=3)

# (c) digit strings
axc.set_xlim(0, 10); axc.set_ylim(0, 10); axc.axis('off')
axc.set_title('(c) base-5 digits of the two points', pad=3)


def row(yb, lab, digs, shade_from, color):
    axc.text(0.0, yb + 0.45, lab, ha='left', va='center', fontsize=6.6)
    axc.text(2.75, yb + 0.45, '0.', ha='right', va='center', fontsize=7.2)
    for n, d in enumerate(digs):
        fc = color if n >= shade_from else 'white'
        axc.add_patch(Rectangle((2.8 + n * 0.95, yb), 0.85, 0.9, fc=fc, ec=GRID, lw=0.4))
        axc.text(2.8 + n * 0.95 + 0.425, yb + 0.45, str(d), ha='center', va='center', fontsize=7.2)
    axc.text(2.8 + 5 * 0.95 + 0.1, yb + 0.45, r'$\ldots$', ha='left', va='center', fontsize=7)


axc.text(0.0, 9.3, r'coordinate 0 (place $0$): a carry', fontsize=6.8, color=ACC2)
row(7.7, 'index 3120', list(Y0[A]), 0, CARRYSH)
row(6.6, 'index 1', list(Y0[B]), 0, CARRYSH)
axc.text(0.0, 5.85, r'$0.04444_5 + 5^{-5} = 0.1_5$: next to each other' + '\n' + r'across the line $y_0=\frac{1}{5}$',
         fontsize=6.2, va='top', color=LATE)
axc.text(0.0, 3.6, r'coordinate 1 (place $1$): shared digits', fontsize=6.8, color=ACC)
row(2.25, 'index 3120', list(Y1[A]), 9, SHADE)
row(1.15, 'index 1', list(Y1[B]), 9, SHADE)
for yb in (2.25, 1.15):
    for n in range(4):
        axc.add_patch(Rectangle((2.8 + n * 0.95, yb), 0.85, 0.9, fc=SHADE, ec=GRID, lw=0.4))
        axc.text(2.8 + n * 0.95 + 0.425, yb + 0.45, str(Y1[A if yb > 2 else B][n]), ha='center', va='center',
                 fontsize=7.2)
axc.text(0.0, 0.85, r'four equal leading digits', fontsize=6.2, va='top', color=LATE)

os.makedirs(OUT, exist_ok=True)
for ext in ('pdf', 'png'):
    fig.savefig(os.path.join(OUT, f'fig_carry.{ext}'), dpi=220 if ext == 'png' else None)
print('wrote', os.path.join(OUT, 'fig_carry.pdf'))
