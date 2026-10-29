"""make_figs_bs.py -- panel builders for the staggered window system p = 101 (slabs of P_3 with cell grid, lattice
images, jitter and closest pair; 3D blocks with near-neighbour links), used by make_figs_v3._restyle_child.

Extracted from the development scripts of the paper: only the functions used by the figures of this paper are kept,
unchanged. Every c printed is an exact toroidal c = delta * N^(1/s) of the plotted point set (bin/mdist).
"""
import _paths
import os, sys, math, json
import numpy as np
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.collections import LineCollection
from matplotlib.lines import Line2D
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)
import bslib as B

plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 9, 'axes.titlesize': 9, 'axes.labelsize': 9, 'legend.fontsize': 8.5,
    'xtick.labelsize': 7.5, 'ytick.labelsize': 7.5, 'axes.linewidth': 0.5,
    'pdf.fonttype': 42})
INK, GRID, FINE, LATE, JIT, ACC = '#111111', '#c8c8c8', '#e2e2e2', '#6f6f6f', '#4a4a4a', '#2b6cb0'
ACC2 = '#c05621'
SOB = '#8a8a8a'
DASH = (0, (2.4, 1.3))
NAMES = {'bs': 'brick-star', 'fa': r'Faure $(I,P,P^2)$', 'sob': "Owen-scrambled Sobol'"}
OUT = {}


def clean(ax, lim):
    ax.set_aspect('equal'); ax.set_xlim(*lim[0]); ax.set_ylim(*lim[1]); ax.set_xticks([]); ax.set_yticks([])
    for s in ax.spines.values(): s.set_color(GRID)


def gridlines(ax, x0, x1, y0, y1, step, color=GRID, lw=0.35):
    xs = np.arange(np.ceil(x0 / step - 1e-9) * step, x1 + 1e-12, step)
    ys = np.arange(np.ceil(y0 / step - 1e-9) * step, y1 + 1e-12, step)
    segs = [[(x, y0), (x, y1)] for x in xs] + [[(x0, y), (x1, y)] for y in ys]
    ax.add_collection(LineCollection(segs, colors=color, linewidths=lw, zorder=0))


# ------------------------------------------------------------------ 1: 2D projections at N = p^2 (full) and p^3 (zoom)
PAIRS3 = [(0, 1), (0, 2), (1, 2)]


# ------------------------------------------------------------------ 2: one-cell-thick slabs of P_3
def closest_pair(X):
    d = B.nn_dist(X, 'cp'); i = int(np.argmin(d))
    D = np.abs(X - X[i]); D = np.minimum(D, 1 - D); dd = (D ** 2).sum(1); dd[i] = np.inf; j = int(np.argmin(dd))
    return i, j, float(d[i])


def slab_panel(ax, X, p, sl_ax, u, v, i, j, W, title):
    g = p; A = X * p; n = np.floor(A + 1e-9); ideal = n + np.floor((A - n) * p) / p
    a, b = A[i].copy(), A[j].copy(); b += g * np.round((a - b) / g)
    sl = n[:, sl_ax] == n[i, sl_ax]
    ctr = (a[[u, v]] + b[[u, v]]) / 2; x0, y0 = int(np.floor(ctr[0])) - W // 2, int(np.floor(ctr[1])) - W // 2
    I0, P0 = ideal[sl][:, [u, v]], A[sl][:, [u, v]]; I, P = [], []
    for sx in (-g, 0, g):
        for sy in (-g, 0, g):
            sh = np.array([sx, sy]); Q = P0 + sh
            k = (Q[:, 0] >= x0) & (Q[:, 0] < x0 + W) & (Q[:, 1] >= y0) & (Q[:, 1] < y0 + W)
            I.append(I0[k] + sh); P.append(Q[k])
    I, P = np.vstack(I), np.vstack(P); assert len(P) == W * W
    gridlines(ax, x0, x0 + W, y0, y0 + W, 1.0, color=GRID, lw=0.5)
    ax.add_collection(LineCollection(np.stack([I, P], 1), colors=JIT, linewidths=0.6, zorder=4))
    ax.scatter(I[:, 0], I[:, 1], s=26, facecolors='none', edgecolors=LATE, linewidths=0.55, zorder=3)
    ax.scatter(P[:, 0], P[:, 1], s=9, c=INK, lw=0, zorder=5)
    same = np.floor(b[sl_ax]) % g == n[i, sl_ax]
    ax.scatter(*a[[u, v]], s=110, facecolors='none', edgecolors=ACC, lw=1.1, zorder=8)
    ax.scatter(*b[[u, v]], s=110, facecolors='none', edgecolors=ACC, lw=1.1, ls='-' if same else (0, (1.5, 1)), zorder=8)
    clean(ax, ((x0, x0 + W), (y0, y0 + W)))
    ax.set_xlabel(rf'$x_{u}$ (cells)', labelpad=1); ax.set_ylabel(rf'$x_{v}$ (cells)', labelpad=1)
    ax.set_title(title, pad=3)
    return dict(same_slab=bool(same))


# ------------------------------------------------------------------ 2b: neighbour displacement ("response") matrix
# ------------------------------------------------------------------ 3: 3D block of 6x6x6 cells with near-neighbour links
def block_pts(X, p, ctr, W):
    """torus copies of the points of P_3 (cell units) inside the W^3 block of cells around ctr."""
    A = X * p; lo = np.floor(ctr) - W // 2
    D = A - lo; D = D - p * np.floor(D / p)                     # shift so the block is [0, W)^3 (mod p)
    k = (D < W).all(1); return D[k], lo


def links(P, rmax):
    from itertools import combinations
    d = np.sqrt(((P[:, None, :] - P[None, :, :]) ** 2).sum(-1)); iu = np.triu_indices(len(P), 1)
    k = d[iu] < rmax; return iu[0][k], iu[1][k], d[iu][k]


def panel3d(ax, P, vert, title, rmax=1.12, cmin=None):
    from matplotlib import cm
    ax.set_proj_type('ortho')
    order = [q for q in range(3) if q != vert] + [vert]; Q = P[:, order]
    i, j, d = links(P, rmax)
    norm = plt.Normalize(0.55, rmax); cmap = matplotlib.colormaps['Blues_r']
    for a, b, dd in sorted(zip(i, j, d), key=lambda t: -t[2]):
        ax.plot(*zip(Q[a], Q[b]), color=cmap(norm(dd) * 0.75), lw=0.6 + 1.4 * (rmax - dd) / rmax, zorder=2)
    ax.scatter(Q[:, 0], Q[:, 1], Q[:, 2], s=9, c=INK, depthshade=True, lw=0, zorder=3)
    if len(d):
        m = np.argmin(d); ax.plot(*zip(Q[i[m]], Q[j[m]]), color=ACC2, lw=2.4, zorder=5)
    ax.set_xlabel(rf'$x_{order[0]}$', labelpad=-12); ax.set_ylabel(rf'$x_{order[1]}$', labelpad=-12); ax.set_zlabel(rf'$x_{order[2]}$', labelpad=-12)
    ax.set_xticklabels([]); ax.set_yticklabels([]); ax.set_zticklabels([])
    ax.view_init(elev=14, azim=-58); ax.set_box_aspect((1, 1, 1))
    ax.set_title(title, pad=0, fontsize=9)
    return float(d.min()) if len(d) else None


# ------------------------------------------------------------------ 4: c(N) for every N <= 2^23
LB1 = {23: 0.4370, 31: 0.2370, 53: 0.444098, 101: 0.6335}       # exact lem:cert of the ACTUAL responses at K = 1 (T3D_BS_BUILD; p=53 bs_cert)


# ------------------------------------------------------------------ 5: nearest-neighbour distance histograms at N = p^3
# ------------------------------------------------------------------ 6: 4D brick-star, p = 307, N = p^2
# ------------------------------------------------------------------ main
FIGS = {}
