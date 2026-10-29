"""b4_figs.py -- Figure fig:count (Section sec:count): the counting argument of Theorem thm:count.

    PY scripts/b4_figs.py [--out DIR]           (from paper/; < 5 s)

s = 2, coordinate 0, the range of levels T = 6..11 (admissible for depth J = 1: K0 = 6 > (s-1)R + s - 2 = 5).
A relation of top index T is a bar in column T over the digit positions n of coordinate 0 at which it has a
nonzero coefficient:
 (a) residue sequence: skeleton relation sum_c v_c y_{c,T} = 0 on P_{2T+1} (lem:residue-rel): position T only;
 (b) block-periodic residue sequence of thm:block(a) (F_0 = [[-1,1],[-1,-1]]): at even T the design
     y_{i,T} = sum_c F_0[i][c] y_{c,T-1} (thm:block(ii)); in coordinate 0 the relation of i = 0 has coefficients
     at T (the geometric digit) and T-1 (F_0[0][0] = -1), the relation of i = 1 only at T-1 (F_0[1][0] = -1);
 (c) hypothetical: both geometric digits designed with depth 1 at every level (12 relations, 7 positions).
Output: fig_count.pdf/.png.
"""
import _paths
import os
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, FancyBboxPatch

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

T0, T1 = 6, 11
J = 1
NMIN, NMAX = T0 - J, T1


def residue():
    return {T: [[T]] for T in range(T0, T1 + 1)}


def block():
    return {T: ([[T - 1, T], [T - 1]] if T % 2 == 0 else []) for T in range(T0, T1 + 1)}


def every():
    return {T: [[T - 1, T], [T - 1]] for T in range(T0, T1 + 1)}


def panel(ax, rel, title, colour, bad=False):
    for n in range(NMIN, NMAX + 1):
        ax.axhspan(n - 0.5, n + 0.5, color=SHADE if (n - NMIN) % 2 == 0 else 'white', lw=0, zorder=0)
    used = set()
    nrel = 0
    for T, bars in rel.items():
        k = len(bars)
        for j, ns in enumerate(bars):
            w = 0.62 / max(k, 1)
            x0 = T - 0.31 + j * w + 0.04
            lo, hi = min(ns), max(ns)
            ax.add_patch(FancyBboxPatch((x0, lo - 0.36), w - 0.08, hi - lo + 0.72,
                                        boxstyle='round,pad=0,rounding_size=0.08',
                                        fc=colour, ec=INK, lw=0.4, zorder=3))
            used.update(ns)
            nrel += 1
    for n in used:
        ax.plot([T0 - 0.62], [n], marker='s', ms=2.6, color=INK, zorder=4, clip_on=False)
    ax.set_xlim(T0 - 0.7, T1 + 0.5)
    ax.set_ylim(NMIN - 0.6, NMAX + 0.6)
    ax.set_xticks(range(T0, T1 + 1))
    ax.set_yticks(range(NMIN, NMAX + 1))
    ax.set_xlabel('level $T$ (top index)')
    ax.tick_params(length=0)
    for sp in ax.spines.values():
        sp.set_visible(False)
    col = ACC2 if bad else INK
    ax.set_title(title, loc='left', pad=12)
    ax.text(0.0, 1.015, f'{nrel} relations on {len(used)} digit positions' + ('  (excluded)' if bad else ''),
            transform=ax.transAxes, ha='left', va='bottom', fontsize=6.6, color=col)


fig, axs = plt.subplots(1, 3, figsize=(WIDTH, 2.25), sharey=True)
panel(axs[0], residue(), '(a) residue sequence', ACC)
panel(axs[1], block(), '(b) block-periodic residue sequence', ACC)
panel(axs[2], every(), '(c) full design at every level', ACC2, bad=True)
axs[0].set_ylabel('digit position $n$ of coordinate 0')
fig.subplots_adjust(left=0.08, right=0.995, bottom=0.17, top=0.83, wspace=0.12)
for ext in ('pdf', 'png'):
    fig.savefig(os.path.join(OUT, f'fig_count.{ext}'), dpi=200)
print('wrote', os.path.join(OUT, 'fig_count.pdf'))
