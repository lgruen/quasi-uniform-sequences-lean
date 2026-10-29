"""b7_levels.py -- Figure fig:levels (Section sec:intro): which numbers of points N = p^m each construction
certifies (its level family), and what the exact separations look like on and off the certified sizes.

    PY scripts/b7_levels.py [--out DIR]         (from paper/; < 5 s)

(a) s = 3, m = 1..27: one row per construction, a filled square where the construction has a certified lower bound on
    sep(P_m) for every prime of its range; the right column gives the certified constant at p = 37: residue sequence
    best v .600 (tab:residue), staggered residue sequence 8/37 = .216 (cor:dyadic), block-periodic 1 - 2/37 = .945
    truncated (thm:block(b)), two families with l = 4 (thm:blocktwo): design levels 12N with .945 and skeleton
    levels 5, 17, 29, ... with the residue constant .600 for the best check vector v'.
(b) s = 2, p = 5, m = 1..10: exact sep(P_m) of the residue sequence (Korobov v = (2,-1), bound 1/sqrt5 = .447 at odd m),
    the brick wall (bound (5-3)/10 = .2 at even m) and the block-periodic sequence of thm:block(a) (bound .6 at m = 4K);
    data: data/levels_p5.txt, computed by b7_levels_data.py. Output: fig_levels.pdf/.png.
"""
import _paths
import os, math
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

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
GREEN = '#2f7d4f'

S, MMAX = 3, 27
rows = [  # (label, set of certified m, colour, constant at p = 37)
    ('classical: Faure, Sobol\', Halton-type', set(), LATE, 'none'),
    ('residue sequence (Sec. 5)', {m for m in range(1, MMAX + 1) if m % S == S - 1}, ACC, '.600'),
    ('staggered residue sequence (Sec. 5)', {m for m in range(1, MMAX + 1) if m % S == 0}, ACC2, '.216'),
    # CUT1 (2026-10-28): the row 'ordered window systems (App. E)' was removed with the ordered windows.
    ('block-periodic, $\\ell=s$ (Sec. 6)', {m for m in range(1, MMAX + 1) if m % (S * S) == 0}, GREEN, '.945'),
    ('two families, $\\ell=4$ (Sec. 6)', {12, 24} | {5, 17}, GREEN, '.945 / .600'),
]

fig = plt.figure(figsize=(WIDTH, 4.1))
ax = fig.add_axes([0.30, 0.50, 0.58, 0.44])
nr = len(rows)
for i, (lab, cert, col, const) in enumerate(rows):
    y = nr - 1 - i
    for m in range(1, MMAX + 1):
        full = (m % S == 0)
        ax.add_patch(Rectangle((m - 0.45, y - 0.36), 0.9, 0.72, facecolor=SHADE if full else 'white',
                               edgecolor=GRID, lw=0.3, zorder=1))
        if m in cert:
            fc = col
            if lab.startswith('two families') and m in (5, 17):
                fc = ACC
            ax.add_patch(Rectangle((m - 0.45, y - 0.36), 0.9, 0.72, facecolor=fc, edgecolor=fc, lw=0.3, zorder=2))
    ax.text(-0.2, y, lab, ha='right', va='center', fontsize=6.8, color=INK)
    ax.text(MMAX + 1.0, y, const, ha='left', va='center', fontsize=6.8, color=INK)
ax.text(MMAX + 1.0, nr - 0.25, '$p=37$', ha='left', va='bottom', fontsize=6.8, color=LATE)
ax.set_xlim(0.4, MMAX + 0.6)
ax.set_ylim(-0.6, nr - 0.3)
ax.set_xticks([m for m in range(1, MMAX + 1) if m % 3 == 0 or m == 1])
ax.set_yticks([])
for sp in ('left', 'right', 'top'):
    ax.spines[sp].set_visible(False)
ax.set_xlabel('exponent $m$ of the prefix $P_m$ ($N=p^m$ points); shaded: full levels $m\\in3\\mathbb{N}$', labelpad=2)
fig.text(0.02, 0.965, '(a) certified sizes in dimension $s=3$', fontsize=7.5)

# ------------------------------------------------------------------ (b) exact separations, s = 2, p = 5
data = {}
for line in open(os.path.join(_paths.DATA, 'levels_p5.txt')):
    if line.startswith('#'):
        continue
    m, a, b, c = line.split()
    data[int(m)] = (float(a), float(b), float(c))
ms = sorted(data)
series = [  # (name, column, colour, certified m, bound, marker)
    ('residue sequence, $v=(2,-1)$', 0, ACC, [m for m in ms if m % 2 == 1], 1 / math.sqrt(5), 'o'),
    ('brick wall $W^-$', 1, ACC2, [m for m in ms if m % 2 == 0], 0.2, 's'),
    ('block-periodic, $\\ell=s$', 2, GREEN, [m for m in ms if m % 4 == 0], 0.6, 'D'),
]
bx = fig.add_axes([0.085, 0.085, 0.60, 0.30])
for name, j, col, cert, bound, mk in series:
    ys = [data[m][j] for m in ms]
    bx.plot(ms, ys, '-', color=col, lw=0.8, zorder=2)
    for m in ms:
        filled = m in cert
        bx.plot([m], [data[m][j]], mk, ms=3.6 if mk != 'D' else 3.2, color=col,
                mfc=col if filled else 'white', mew=0.7, zorder=3)
    for m in cert:
        bx.plot([m - 0.32, m + 0.32], [bound, bound], '-', color=col, lw=1.4, solid_capstyle='butt', zorder=1)
bx.set_xlim(0.5, 10.5)
bx.set_ylim(0, 0.72)
bx.set_xticks(ms)
bx.set_yticks([0, 0.2, 0.4, 0.6])
bx.set_xlabel('$m$', labelpad=1)
bx.set_ylabel('exact sep$(P_m)$', labelpad=2)
bx.grid(axis='y', color=FINE, lw=0.3)
for sp in ('right', 'top'):
    bx.spines[sp].set_visible(False)
fig.text(0.02, 0.405, '(b) exact separation in dimension $s=2$, $p=5$', fontsize=7.5)
# legend panel
lx = fig.add_axes([0.70, 0.085, 0.29, 0.30])
lx.axis('off')
yy = 0.92
for name, j, col, cert, bound, mk in series:
    lx.plot([0.02, 0.12], [yy, yy], '-', color=col, lw=0.8)
    lx.plot([0.07], [yy], mk, ms=3.4, color=col, mfc=col, mew=0.7)
    lx.text(0.16, yy, name, va='center', fontsize=6.6)
    yy -= 0.16
lx.plot([0.07], [yy], 'o', ms=3.4, color=LATE, mfc=LATE)
lx.text(0.16, yy, 'certified size', va='center', fontsize=6.6)
yy -= 0.13
lx.plot([0.07], [yy], 'o', ms=3.4, color=LATE, mfc='white', mew=0.7)
lx.text(0.16, yy, 'size outside the family', va='center', fontsize=6.6)
yy -= 0.13
lx.plot([0.03, 0.11], [yy, yy], '-', color=LATE, lw=1.4)
lx.text(0.16, yy, 'certified lower bound', va='center', fontsize=6.6)
lx.set_xlim(0, 1)
lx.set_ylim(0, 1)

for ext in ('pdf', 'png'):
    fig.savefig(os.path.join(OUT, 'fig_levels.' + ext), dpi=220)
print('wrote', os.path.join(OUT, 'fig_levels.pdf'))
