"""b3_figs.py -- Figures fig:residue (Section sec:residue) and fig:block (Section sec:block), from the real points.

    PY scripts/b3_figs.py [--out DIR]           (from paper/; < 30 s)

fig_residue: (a) the brick wall W^- (staggered residue sequence, s = 2, Faure places, theta = -1/4, mu = (-4, 2)),
             p = 13, the full level P_2: in every column of cells the height (first digit below the cell of
             coordinate 1) is the rank-1 lattice rule r_1 = n_0/2 mod 13 (Lemma lem:residuestar-rel); the horizontal
             position is free (a jitter of a whole cell).
             (b), (c) the residue sequence R_v, s = 2, p = 11, places (0, 1), theta = 1, v = (3, -1) (= Korobov,
             rho = 3), the prefix P_3 (K = 2): fine cells of side 11^-2; the occupied fine cells are exactly
             Lambda_v = {b : 3 b_0 - b_1 = 0 mod 11} (Theorem thm:residue(i)), the lattice image of a point is the
             corner of its fine cell, the jitter is less than one fine cell.
fig_block:   the block-periodic residue sequence of Theorem thm:block, s = 2, p = 7, places (0, 1), v = (1, 1),
             theta = 1, F_0 = [[-1, 1], [-1, -1]], F_1 = 0 (generator: audit_gen.block_matrices, an independent
             implementation); (a) the certified level m = 8, (b) the uncertified level m = 6.
Generators: b3_gen.py (residue formulas), audit_gen.py. Exact separations are recomputed here by brute force in
small windows only for drawing; the values quoted in the captions are exact values of the cell-list program sepx.cpp.
Output: fig_residue.pdf/.png, fig_block.pdf/.png.
"""
import _paths
import os, sys, math
import numpy as np
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, Circle, FancyArrowPatch
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D

OUT = _paths.OUT
from b3_gen import brickwall, matrices
from audit_gen import block_matrices

plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42})
WIDTH = 6.3
INK, GRID, FINE, LATE, ACC, ACC2, SHADE = '#111111', '#c8c8c8', '#e2e2e2', '#6f6f6f', '#2b6cb0', '#c05621', '#dde6f2'


def points(C, p, m, R, idx):
    """coordinates (s x len(idx)) in [0,1) of the points with integer indices idx, digits n < R."""
    s = len(C)
    V = np.array([(idx // p ** k) % p for k in range(m)], dtype=np.int64)          # m x n
    w = float(p) ** -(np.arange(R) + 1)
    X = []
    for c in range(s):
        A = np.array([[C[c][n][k] for k in range(m)] for n in range(R)], dtype=np.int64)
        Y = (A @ V) % p                                                            # R x n digits
        X.append(w @ Y)
    return np.array(X), V


def closest(X, period=1.0):
    best = (9.0, 0, 0)
    n = X.shape[1]
    for i in range(n - 1):
        d = np.abs(X[:, i + 1:] - X[:, [i]]); d = np.minimum(d, period - d)
        dd = (d * d).sum(0); j = int(np.argmin(dd))
        if dd[j] < best[0]: best = (float(dd[j]), i, i + 1 + j)
    return best


def frame(ax, color=GRID):
    ax.set_aspect('equal'); ax.set_xticks([]); ax.set_yticks([])
    for s_ in ax.spines.values(): s_.set_color(color)


def ring(ax, x, y, r):
    ax.add_patch(Circle((x, y), r, fill=False, ec=ACC, lw=1.0, zorder=6))


# ------------------------------------------------------------------------------------------------ fig_residue
fig = plt.figure(figsize=(WIDTH, 2.62))
axa = fig.add_axes([0.005, 0.15, 0.31, 0.74])
axb = fig.add_axes([0.345, 0.15, 0.31, 0.74])
axc = fig.add_axes([0.685, 0.15, 0.31, 0.74])

# (a) brick wall, p = 13, P_2
p, m, R = 13, 2, 14
C = brickwall(p, R, m)
N = p ** m
X, _ = points(C, p, m, R, np.arange(N))
d2, i1, i2 = closest(X)
sepa = math.sqrt(d2) * N ** 0.5
print('brick wall p=13 sep(P_2) = %.4f (pair %d, %d)' % (sepa, i1, i2))
segs = [[(k / p, 0), (k / p, 1)] for k in range(1, p)] + [[(0, k / p), (1, k / p)] for k in range(1, p)]
axa.add_collection(LineCollection(segs, colors=GRID, linewidths=0.35, zorder=0))
n0 = np.floor(X[0] * p).astype(int); n1 = np.floor(X[1] * p).astype(int)
r1 = np.floor(X[1] * p * p).astype(int) % p
half = (p + 1) // 2
assert np.all(r1 == (half * n0) % p), 'height must be n_0/2 mod p (Lemma residuestar-rel)'
courses = [[(n0[i] / p, (n1[i] + r1[i] / p) / p), ((n0[i] + 1) / p, (n1[i] + r1[i] / p) / p)] for i in range(N)]
axa.add_collection(LineCollection(courses, colors=ACC, linewidths=0.7, zorder=1))
axa.scatter(X[0], X[1], s=3.2, c=INK, lw=0, zorder=3)
for i in (i1, i2): ring(axa, X[0][i], X[1][i], 0.018)
frame(axa); axa.set_xlim(0, 1); axa.set_ylim(0, 1)
axa.set_title('(a) staggered residue sequence $W^-$,\n$p=13$, $P_2$, $\\mathrm{sep}=%.4f$' % sepa, pad=3)

# (b), (c) residue sequence, p = 11, v = (3, -1), P_3
p, m, R, K = 11, 3, 14, 2
v = [3, p - 1]
C = matrices('U', p, [0, 1], 1, R, m, v=v)
N = p ** m
X, _ = points(C, p, m, R, np.arange(N))
d2, i1, i2 = closest(X)
sepb = math.sqrt(d2) * N ** 0.5
print('residue p=11 v=(3,-1) sep(P_3) = %.4f (pair %d, %d); bound 2*11^(-1/2) = %.4f' % (sepb, i1, i2, 2 / math.sqrt(11)))
F = p ** K
Pc = np.floor(X * F).astype(int)
assert np.all((3 * Pc[0] - Pc[1]) % p == 0), 'occupied fine cells must lie in Lambda_v'
assert len(set(zip(Pc[0], Pc[1]))) == N
segs = [[(k / p, 0), (k / p, 1)] for k in range(1, p)] + [[(0, k / p), (1, k / p)] for k in range(1, p)]
axb.add_collection(LineCollection(segs, colors=FINE, linewidths=0.35, zorder=0))
axb.scatter(X[0], X[1], s=0.55, c=INK, lw=0, zorder=2)
cx = 0.5 * (X[0][i1] + X[0][i2]); cy = 0.5 * (X[1][i1] + X[1][i2])
W = 13                                                  # zoom window: W x W fine cells
bx0 = int(round(cx * F)) - W // 2; by0 = int(round(cy * F)) - W // 2
bx0 = min(max(bx0, 0), F - W); by0 = min(max(by0, 0), F - W)
axb.add_patch(Rectangle((bx0 / F, by0 / F), W / F, W / F, fill=False, ec=ACC2, lw=0.8, zorder=4))
frame(axb); axb.set_xlim(0, 1); axb.set_ylim(0, 1)
axb.set_title('(b) residue sequence $\\mathcal{R}_v$, $v=(3,-1)$,\n$p=11$, $P_3$ (1331 points)', pad=3)

# (c) zoom in fine-cell units
for a_ in range(bx0, bx0 + W):
    for b_ in range(by0, by0 + W):
        if (3 * a_ - b_) % p == 0:
            axc.add_patch(Rectangle((a_, b_), 1, 1, fc=SHADE, ec='none', zorder=0))
segs = [[(k, by0), (k, by0 + W)] for k in range(bx0, bx0 + W + 1)] + \
       [[(bx0, k), (bx0 + W, k)] for k in range(by0, by0 + W + 1)]
axc.add_collection(LineCollection(segs, colors=GRID, linewidths=0.3, zorder=0.5))
sel = (Pc[0] >= bx0) & (Pc[0] < bx0 + W) & (Pc[1] >= by0) & (Pc[1] < by0 + W)
xs, ys = X[0][sel] * F, X[1][sel] * F
axc.scatter(Pc[0][sel], Pc[1][sel], s=9, facecolors='none', edgecolors=LATE, lw=0.5, zorder=2)
axc.add_collection(LineCollection([[(a_, b_), (x_, y_)] for a_, b_, x_, y_ in zip(Pc[0][sel], Pc[1][sel], xs, ys)],
                                  colors=INK, linewidths=0.5, zorder=2.5))
axc.scatter(xs, ys, s=5, c=INK, lw=0, zorder=3)
for i in (i1, i2): ring(axc, X[0][i] * F, X[1][i] * F, 0.55)
# lattice basis (1,3), (-3,2) from a lattice point near the lower left
base = None
rings = [(X[0][i] * F, X[1][i] * F) for i in (i1, i2)]
def far(pt): return all((pt[0] - u) ** 2 + (pt[1] - w_) ** 2 > 1.6 ** 2 for u, w_ in rings)
for a_ in range(bx0, bx0 + W):
    for b_ in range(by0, by0 + W):
        if (3 * a_ - b_) % p == 0 and bx0 + 4 <= a_ <= bx0 + W - 3 and b_ + 3 <= by0 + W - 1:
            if far((a_, b_)) and far((a_ + 1, b_ + 3)) and far((a_ - 3, b_ + 2)):
                if base is None or b_ < base[1]: base = (a_, b_)
assert base is not None
for dx, dy, lab in ((1, 3, '$(1,3)$'), (-3, 2, '$(-3,2)$')):
    axc.add_patch(FancyArrowPatch(base, (base[0] + dx, base[1] + dy), arrowstyle='-|>', mutation_scale=6,
                                  color=ACC2, lw=0.9, zorder=4, shrinkA=0, shrinkB=0))
    axc.text(base[0] + dx + (0.25 if dx > 0 else -0.25), base[1] + dy + 0.15, lab, color=ACC2, fontsize=6.4,
             ha='left' if dx > 0 else 'right', va='bottom', zorder=5,
             bbox=dict(fc='white', ec='none', pad=0.4, alpha=0.85))
frame(axc, ACC2); axc.set_xlim(bx0, bx0 + W); axc.set_ylim(by0, by0 + W)
axc.set_title('(c) zoom: $13\\times13$ fine cells; shaded:\n$\\Lambda_v$; $\\mathrm{sep}(P_3)=%.4f$' % sepb, pad=3)

handles = [Line2D([], [], color=ACC, lw=0.9, label='height of coordinate 1 (designed)'),
           Line2D([], [], marker='o', ls='', mfc='none', mec=LATE, ms=3.6, mew=0.6, label='lattice image (fine-cell corner)'),
           Line2D([], [], color=INK, lw=0.6, label='jitter'),
           Line2D([], [], marker='o', ls='', mfc=INK, mec=INK, ms=2.2, label='point'),
           Line2D([], [], marker='o', ls='', mfc='none', mec=ACC, ms=5.5, mew=1.0, label='closest pair')]
fig.legend(handles=handles, loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.5, -0.005),
           handletextpad=0.4, columnspacing=1.1)
os.makedirs(OUT, exist_ok=True)
for ext in ('pdf', 'png'):
    fig.savefig(os.path.join(OUT, f'fig_residue.{ext}'), dpi=220 if ext == 'png' else None)
plt.close(fig)

# ------------------------------------------------------------------------------------------------ fig_block
p, s, L, theta = 7, 2, 2, 1
a, vv = [0, 1], [1, 1]
Fd = [[[-1, 1], [-1, -1]], [[0, 0], [0, 0]]]
Cb, vals = block_matrices(p, s, L, a, theta, vv, Fd, None, rows=26, cols=8)
assert vals == [[1, 0], [1, 0]]
fig = plt.figure(figsize=(WIDTH, 3.25))
panels = [(8, fig.add_axes([0.06, 0.12, 0.42, 0.76]), '(a) certified level $m=8$'),
          (6, fig.add_axes([0.54, 0.12, 0.42, 0.76]), '(b) uncertified level $m=6$')]
pairs = {8: (1085326, 4241291), 6: (26625, 2804)}       # closest pairs (sepx.cpp)
for m, ax, title in panels:
    K = m // 2; Fc = p ** K; R = m + 10; N = p ** m
    # cells of the closest pair, window of W x W cells around them
    Xp, _ = points(Cb, p, m, R, np.array(pairs[m], dtype=np.int64))
    dd = np.abs(Xp[:, 0] - Xp[:, 1]); dd = np.minimum(dd, 1 - dd)
    sep_pair = math.sqrt((dd ** 2).sum()) * N ** 0.5
    W = 11
    cx = int(np.floor(Xp[0][0] * Fc)); cy = int(np.floor(Xp[1][0] * Fc))
    x0 = min(max(cx - W // 2, 0), Fc - W); y0 = min(max(cy - W // 2, 0), Fc - W)
    sel_pts = []
    chunk = 1 << 20
    for start in range(0, N, chunk):
        idx = np.arange(start, min(N, start + chunk), dtype=np.int64)
        Xc, _ = points(Cb, p, m, R, idx)
        nx = np.floor(Xc[0] * Fc); ny = np.floor(Xc[1] * Fc)
        ok = (nx >= x0) & (nx < x0 + W) & (ny >= y0) & (ny < y0 + W)
        if ok.any(): sel_pts.append(Xc[:, ok])
    P = np.concatenate(sel_pts, axis=1) * Fc
    assert P.shape[1] == W * W
    # brute force inside the window (all pairs inside): must reproduce the pair distance
    d2w, j1, j2 = closest(P / Fc)
    print('block p=7 m=%d: window min sep %.4f, closest pair from sepx %.4f' % (m, math.sqrt(d2w) * N ** 0.5, sep_pair))
    nxy = np.floor(P); rr = np.floor((P - nxy) * p)
    img = nxy + rr / p
    segs = [[(k, y0), (k, y0 + W)] for k in range(x0, x0 + W + 1)] + [[(x0, k), (x0 + W, k)] for k in range(y0, y0 + W + 1)]
    ax.add_collection(LineCollection(segs, colors=GRID, linewidths=0.35, zorder=0))
    ax.scatter(img[0], img[1], s=14, facecolors='none', edgecolors=LATE, lw=0.55, zorder=2)
    ax.add_collection(LineCollection([[(img[0][i], img[1][i]), (P[0][i], P[1][i])] for i in range(P.shape[1])],
                                     colors=INK, linewidths=0.5, zorder=2.5))
    ax.scatter(P[0], P[1], s=5, c=INK, lw=0, zorder=3)
    for i in range(2): ring(ax, Xp[0][i] * Fc, Xp[1][i] * Fc, 0.3)
    if m == 8:
        # lattice steps between neighbouring lattice images where the step is exactly (I + F_0/p) e_c
        cellmap = {(int(nxy[0][i]), int(nxy[1][i])): (img[0][i], img[1][i]) for i in range(P.shape[1])}
        steps = {(1, 0): (1 - 1 / p, -1 / p), (0, 1): (1 / p, 1 - 1 / p)}
        lat = []
        for (cx_, cy_), pt in cellmap.items():
            for (ex, ey), (sx, sy) in steps.items():
                q_ = cellmap.get((cx_ + ex, cy_ + ey))
                if q_ is not None and abs(q_[0] - pt[0] - sx) < 1e-9 and abs(q_[1] - pt[1] - sy) < 1e-9:
                    lat.append([pt, q_])
        ax.add_collection(LineCollection(lat, colors=SHADE, linewidths=1.6, zorder=1))
        print('  lattice steps drawn:', len(lat), 'of', 2 * W * (W - 1))
        # the lattice (I + F_0/p) Z^2 of the lattice images: two basis steps from one image
        k0 = int(np.argmin((img[0] - (x0 + 2)) ** 2 + (img[1] - (y0 + 2)) ** 2))
        b0 = (img[0][k0], img[1][k0])
        for dx, dy, lab in ((1 - 1 / p, -1 / p, r'$(I+F_0/p)\,e_0$'), (1 / p, 1 - 1 / p, r'$(I+F_0/p)\,e_1$')):
            ax.add_patch(FancyArrowPatch(b0, (b0[0] + dx, b0[1] + dy), arrowstyle='-|>', mutation_scale=6,
                                         color=ACC2, lw=0.9, zorder=4, shrinkA=0, shrinkB=0))
        ax.text(b0[0] + 1.05, b0[1] - 0.45, r'$(I+F_0/p)\,e_0$', color=ACC2, fontsize=6.3, va='top',
                bbox=dict(fc='white', ec='none', pad=0.4, alpha=0.85), zorder=5)
        ax.text(b0[0] - 0.1, b0[1] + 1.12, r'$(I+F_0/p)\,e_1$', color=ACC2, fontsize=6.3, va='bottom',
                bbox=dict(fc='white', ec='none', pad=0.4, alpha=0.85), zorder=5)
    frame(ax); ax.set_xlim(x0, x0 + W); ax.set_ylim(y0, y0 + W)
    ax.set_title(title + ', $\\mathrm{sep}(P_{%d})=%.4f$\n($%d\\times%d$ of the $%d^2$ cells)' % (m, sep_pair, W, W, Fc),
                 pad=3)
handles = [Line2D([], [], marker='o', ls='', mfc='none', mec=LATE, ms=4, mew=0.6, label='lattice image $n+r/p$'),
           Line2D([], [], color=SHADE, lw=1.6, label='lattice step $(I+F_0/p)e_c$'),
           Line2D([], [], color=INK, lw=0.6, label='jitter'),
           Line2D([], [], marker='o', ls='', mfc=INK, mec=INK, ms=2.2, label='point'),
           Line2D([], [], marker='o', ls='', mfc='none', mec=ACC, ms=5.5, mew=1.0, label='closest pair')]
fig.legend(handles=handles, loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.5, -0.005))
for ext in ('pdf', 'png'):
    fig.savefig(os.path.join(OUT, f'fig_block.{ext}'), dpi=220 if ext == 'png' else None)
plt.close(fig)
print('wrote fig_residue, fig_block to', OUT)
