"""make_figs_v3.py -- figure builders of the window-system figures (fig_principles, fig_cost, and the slabs and 3D
links of the staggered window system), used by b5_figs.py and cut1_figs.py, and helpers used by b6_figs.py and
b8_freediag.py (style, drop data, slabs).

Extracted from the development scripts of the paper: only the functions used by the figures of this paper are kept;
the code of the kept functions is unchanged except for the paths (module _paths) and the end of _restyle_child (its
parts (3), (4) drew figures that are not in the paper). Inputs: the ordered window system p = 31 (data/pp_s3_p31.cfg),
the staggered window system p = 101 (bslib.py, data/bs3_p101.txt), drop data (data/drops_*.txt).
Every c printed is an exact toroidal c = delta * N^(1/s) of the plotted point set.
"""
import _paths
import os, sys, math, itertools, subprocess, json
import numpy as np
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, Wedge, Arc, FancyArrowPatch
from matplotlib.lines import Line2D
from matplotlib.collections import LineCollection
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)

OUT = _paths.OUT
DATA = _paths.DATA
import bslib as B

plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42})
WIDTH = 6.3
INK, GRID, FINE, LATE, JIT, ACC = '#111111', '#c8c8c8', '#e2e2e2', '#6f6f6f', '#4a4a4a', '#2b6cb0'
ACC2 = '#c05621'; SOB = '#9a9a9a'; SHADE = '#dde6f2'; FREE = '#ececec'
DASH = (0, (2.4, 1.3))
VAL = {}


def save(fig, name):
    for ext in ('pdf', 'png'):
        fig.savefig(os.path.join(OUT, f'{name}.{ext}'), dpi=200 if ext == 'png' else None)
    plt.close(fig); print('  wrote', name, flush=True)


def gridlines(ax, x0, x1, y0, y1, step, color=GRID, lw=0.35, z=0):
    xs = np.arange(np.ceil(x0 / step - 1e-9) * step, x1 + 1e-9, step)
    ys = np.arange(np.ceil(y0 / step - 1e-9) * step, y1 + 1e-9, step)
    segs = [[(x, y0), (x, y1)] for x in xs] + [[(x0, y), (x1, y)] for y in ys]
    ax.add_collection(LineCollection(segs, colors=color, linewidths=lw, zorder=z))


def clean(ax, lim):
    ax.set_aspect('equal'); ax.set_xlim(*lim[0]); ax.set_ylim(*lim[1]); ax.set_xticks([]); ax.set_yticks([])
    for s in ax.spines.values(): s.set_color(GRID)


def load_dump3(path):
    t = open(path).read().split()
    p, R, C = int(t[0]), int(t[1]), int(t[2]); v = np.array(t[3:3 + 3 * R * C], dtype=np.int64)
    return p, v.reshape(3, R, C)


def read_cfg(path):
    """window-system cfg (data/pp_s3_p31.cfg): kappa[c][c'] (row = affected, column = carrying),
    windows W[c'][c] = (lo, hi) of column c' in row c."""
    K, W, extra = [], {}, {}
    for l in open(path):
        t = l.split()
        if not t: continue
        if t[0] == 'kappa_row': K.append([int(x) for x in t[1:]])
        elif t[0] == 'win':
            cp = int(t[1]); v = [int(x) for x in t[2:]]          # sp_check/ground format: one (lo, hi) per ROW c
            W[cp] = {c: (v[2 * c], v[2 * c + 1]) for c in range(len(v) // 2)}
        elif t[0] in ('M', 'W', 'heights', 'places', 'rho', 'superdiag'): extra[t[0]] = [int(x) for x in t[1:]]
        elif t[0] == 'minS': extra['LB'] = float(t[3])
        elif t[0] == 's': extra['p'] = int(t[3]); extra['theta'] = t[5]
    return np.array(K), W, extra


def drops(path):
    return B.load_drops(path)


def sawtooth(dr, s=3, N0=2):
    Ns, d2, Nmax = dr; xs, ys = [], []
    for k in range(len(Ns)):
        a = max(Ns[k], N0); e = Ns[k + 1] if k + 1 < len(Ns) else Nmax
        if e < N0: continue
        xs += [a, e]; ys += [math.sqrt(d2[k]) * a ** (1 / s), math.sqrt(d2[k]) * e ** (1 / s)]
    return np.log2(xs), np.array(ys)


def Jmin(dr, lo=64, hi=2 ** 23):
    Ns = dr[0]; cand = [lo] + [int(n) for n in Ns if lo <= n <= hi]
    return min((B.c_at(dr, n), n) for n in cand)


def tor_closest(X):
    d = B.nn_dist(X, 'v3'); i = int(np.argmin(d))
    D = np.abs(X - X[i]); D = np.minimum(D, 1 - D); dd = (D ** 2).sum(1); dd[i] = np.inf; j = int(np.argmin(dd))
    return i, j, float(d[i])


# ------------------------------------------------------------------ 1. fig_evidence: the headline picture (Section 1)
def slab_at_N(ax, X, title, W=7.0):
    """slab one mean spacing u = N^(-1/3) thick around the closest pair of the N points X, W x W units in-plane."""
    N = len(X); u = N ** (-1 / 3); i, j, d = tor_closest(X)
    a = X[i] / u; b = X[j] / u; L = 1 / u; b = b + L * np.round((a - b) / L)
    sl = int(np.argmin(np.abs(a - b))); uu, vv = [q for q in range(3) if q != sl]
    mid = (a + b) / 2; A = X / u
    dz = A[:, sl] - mid[sl]; dz -= L * np.round(dz / L); keep = np.abs(dz) < 0.5
    P = A[keep][:, [uu, vv]]; Z = dz[keep]
    x0, y0 = mid[uu] - W / 2, mid[vv] - W / 2; pts = []
    for sx in (-L, 0, L):
        for sy in (-L, 0, L):
            Q = P + np.array([sx, sy]); k = (Q[:, 0] >= x0) & (Q[:, 0] < x0 + W) & (Q[:, 1] >= y0) & (Q[:, 1] < y0 + W)
            pts.append(np.c_[Q[k], Z[k]])
    pts = np.vstack(pts)
    gridlines(ax, x0, x0 + W, y0, y0 + W, 1.0, color=FINE, lw=0.35)
    gray = np.clip(0.15 + 0.9 * np.abs(pts[:, 2]), 0, 0.75)
    ax.scatter(pts[:, 0], pts[:, 1], s=5.5, c=[(g, g, g) for g in gray], lw=0, zorder=4)
    for q in (a, b):
        ax.add_patch(plt.Circle((q[uu], q[vv]), 0.28, fill=False, ec=ACC, lw=0.8, zorder=6))
    clean(ax, ((x0, x0 + W), (y0, y0 + W)))
    ax.set_title(title, pad=2.5, fontsize=6.8)
    VAL.setdefault('slab_counts', {})[title[:12]] = int(len(pts))
    return d * N ** (1 / 3), (int(i), int(j)), (uu, vv, sl)


# ------------------------------------------------------------------ 2. fig_principles: ORDER and ANTIPODE (Section 1)
def arc_window(ax, ctr, r, lo, hi, p, col, lw, z=3):
    """window [lo, hi] (integers mod p) on a residue circle, 0 at the top, residues increasing clockwise."""
    a0 = 90 - 360 * (hi + 0.5) / p; a1 = 90 - 360 * (lo - 0.5) / p
    ax.add_patch(Arc(ctr, 2 * r, 2 * r, theta1=a0, theta2=a1, color=col, lw=lw, zorder=z, capstyle='butt'))


def fig_principles():
    K, W, ex = read_cfg(os.path.join(DATA, 'pp_s3_p31.cfg')); p = ex['p']; s = 3
    fig = plt.figure(figsize=(WIDTH, 2.85))
    gs = fig.add_gridspec(1, 3, width_ratios=[1.55, 1.0, 1.2], wspace=0.2, left=0.005, right=0.975, top=0.81, bottom=0.12)
    # (a) the window matrix of a real ordered design; each window label sits BELOW its residue circle
    ax = fig.add_subplot(gs[0]); r = 0.29; dl = 0.35
    ax.add_patch(Rectangle((0.5, -1.56), 2.0, 1.04, fc='#f6e6da', ec='none', zorder=0))          # row 1, columns 1..2
    rows = {}
    for c in range(s):
        Bc = sum(W[cp][c][1] for cp in range(c + 1, s)); lo, hi = W[c][c]; A_, M_ = -hi, hi - lo + 1
        rows[c] = dict(B=Bc, A=A_, M=M_, LB=(p - A_ - M_ - Bc) / p)
        for cp in range(s):
            ctr = (cp, -c + 0.07); lo, hi = W[cp][c]; lab = (ctr[0], ctr[1] - dl)
            ax.add_patch(plt.Circle(ctr, r, fill=False, ec=GRID, lw=0.5, zorder=1))
            ax.plot([ctr[0], ctr[0]], [ctr[1] + r - 0.06, ctr[1] + r + 0.06], color=INK, lw=0.6, zorder=4)
            if hi - lo + 1 >= p:
                ax.add_patch(plt.Circle(ctr, r, fc=FREE, ec=GRID, lw=0.5, zorder=1))
                ax.text(*lab, 'free', ha='center', va='top', fontsize=6.0, color=LATE)
            elif cp == c:
                arc_window(ax, ctr, r, lo, hi, p, ACC, 2.4)
                ax.text(*lab, rf'${lo}$' if lo == hi else rf'$[{lo},{hi}]$', ha='center', va='top', fontsize=6.0, color=ACC)
            else:
                arc_window(ax, ctr, r, lo, hi, p, INK, 1.9)
                ax.text(*lab, rf'$\pm{hi}$', ha='center', va='top', fontsize=6.2, color=INK)
        ax.text(-0.5, -c + 0.07, rf'$x_{c}$', ha='right', va='center', fontsize=7.5)
        ax.text(2.6, -c + 0.07, rf'$\frac{{{p - rows[c]["A"] - rows[c]["M"] - rows[c]["B"]}}}{{{p}}}$', ha='left', va='center', fontsize=8,
                color=ACC2 if c == 1 else INK)
    for cp in range(s): ax.text(cp, 0.5, rf'$n_{cp}{{+}}1$', ha='center', va='bottom', fontsize=7)
    ax.text(2.6, 0.5, 'row bound', ha='left', va='bottom', fontsize=5.8, color=LATE)
    ax.plot(0, -1 + 0.07, marker='x', ms=10, mew=1.0, color=ACC2, zorder=6)        # e_0 = 0 multiplies the free entry by 0
    ax.text(1.05, -2.5, r'step $e=(0,1,\pm1)$: $x_1$ moves first, so row 1 reads' + '\n' + r'only own $+$ upper ($e_0=0$ kills the free entry):' + '\n' +
            r'gap $\geq (p-2B_1-M_1)/p$', ha='center', va='top', fontsize=6.2, color=ACC2)
    ax.set_xlim(-0.75, 3.1); ax.set_ylim(-3.2, 0.82); ax.set_aspect('equal'); ax.axis('off')
    ax.set_title(r'(a) ORDERING: windows of an' + '\n' + rf'ordered design, $p={p}$: own (blue)' + '\n' + r'behind 0, upper small, lower free', pad=2)
    # (a') the coordinate that gives the bound, in cell units: row 1 of the same design
    ax = fig.add_subplot(gs[1]); R = 0.55; c = 1; d = rows[c]; span = (2 * d['B'] + d['M'] - 1) / p; H = 0.32
    for x0 in (0, 1): ax.add_patch(Rectangle((x0, -H), 1, 2 * H, fc='white', ec=GRID, lw=0.9, zorder=1))
    ax.add_patch(Rectangle((1 + R - span, -H), span, 2 * H, fc=SHADE, ec=ACC, lw=0.6, zorder=2))
    ax.plot(R, 0, 'o', ms=4.5, color=INK, zorder=5); ax.plot(1 + R - span, 0, 'o', ms=4.5, mfc='white', mec=INK, mew=0.8, zorder=5)
    ax.plot([1 + R, 1 + R], [-H, H], color=ACC, lw=0.6, ls=DASH, zorder=3)
    ax.annotate('', xy=(1 + R - span, -H - 0.14), xytext=(R, -H - 0.14), arrowprops=dict(arrowstyle='<->', lw=0.7, color=ACC2, shrinkA=0, shrinkB=0))
    ax.text((1 + R - span + R) / 2, -H - 0.22, rf'gap $\geq 1-\frac{{2B_1+M_1}}{{p}}=\frac{{{round(d["LB"] * p)}}}{{{p}}}$', ha='center', va='top', fontsize=7, color=ACC2)
    ax.text(1 + R - span / 2, H + 0.08, 'neighbour lands here:' + '\n' + rf'own $+$ upper $\subseteq[-{2 * d["B"] + d["M"] - 1},0]$', ha='center', va='bottom', fontsize=6.4, color=ACC)
    ax.text(R, -0.08, 'point', ha='center', va='top', fontsize=6.4)
    ax.text(0.05, H - 0.05, r'cell $n_1$', ha='left', va='top', fontsize=6.4, color=LATE)
    ax.text(1.96, H - 0.05, r'$n_1{+}1$', ha='right', va='top', fontsize=6.4, color=LATE)
    ax.set_xlim(-0.05, 2.05); ax.set_ylim(-1.05, 1.0); ax.axis('off')
    ax.set_title(r"(a$'$) the coordinate that bounds" + '\n' + r'$e=(0,1,\pm1)$: $x_1$ (cell units),' + '\n' + 'pulled back, never wrapped', pad=2)
    # (b) HALF-CELL STAGGER: the three one-digit gap shapes on the residue circle
    ax = fig.add_subplot(gs[2]); P = np.linspace(0, 1, 2001)[1:-1]; eps = 0.1
    ax.axvspan(0.5 - eps, 0.5 + eps, color=SHADE, lw=0, zorder=0)
    for xb in (0.0, 1.0): ax.plot([xb, xb], [0, 1], color=LATE, lw=0.6, ls=(0, (1, 1.2)), zorder=2)        # the jump 1 -> 0
    ax.plot(P, P, color=ACC, lw=1.0); ax.plot(P, 1 - P, color=ACC2, lw=1.0)
    ax.plot(P, np.minimum(P, 1 - P), color=INK, lw=1.0, ls=DASH)
    ax.text(0.97, 0.74, r'$e_c=+1$', color=ACC, fontsize=6.4, ha='right')
    ax.text(0.03, 0.74, r'$e_c=-1$', color=ACC2, fontsize=6.4, ha='left')
    ax.text(0.5, 0.17, r'$e_c=0$: $\|\Phi\|$ (dashed)', color=INK, fontsize=6.4, ha='center')
    ax.plot([0, 1], [1, 1], 'o', ms=2.6, color=INK, zorder=5); ax.plot([0, 1], [0, 0], 'o', ms=2.6, mfc='white', mec=INK, zorder=5)
    ax.plot(0.5, 0.5, 'o', ms=4.5, mfc='white', mec=INK, mew=0.9, zorder=6)
    ax.annotate(r'$\Phi=\frac{1}{2}$: all three equal $\frac{1}{2}$,' + '\n' + r'whatever the sign of the step', xy=(0.5, 0.5), xytext=(0.5, 1.03),
                ha='center', va='bottom', fontsize=6.2, arrowprops=dict(arrowstyle='-', lw=0.5, color=LATE))
    for xt, xa, ha in ((0.06, 0.012, 'left'), (0.94, 0.988, 'right')):
        ax.annotate('wrap-around', xy=(xa, 0.33), xytext=(xt, 0.42), ha=ha, va='bottom', fontsize=5.8, color=LATE,
                    arrowprops=dict(arrowstyle='-|>', lw=0.4, color=LATE, mutation_scale=4, shrinkA=0, shrinkB=0))
    ax.set_xlim(0, 1); ax.set_ylim(0, 1.27); ax.set_xticks([0, 0.25, 0.5, 0.75, 1]); ax.set_xticklabels(['0', r'$\frac{1}{4}$', r'$\frac{1}{2}$', r'$\frac{3}{4}$', '1'])
    ax.set_yticks([0, 0.5, 1]); ax.set_xlabel(r'response $\Phi$ (residue circle, cell units)', labelpad=1)
    ax.set_ylabel(r'one-digit gap $\bar f(e_c,\Phi)$', labelpad=1)
    for sp in ('top', 'right'): ax.spines[sp].set_visible(False)
    ax.set_title(r'(b) HALF-CELL STAGGER:' + '\n' + r'works for either sign' + '\n' + 'and through wrap-around', pad=2)
    save(fig, 'fig_principles')
    VAL['principles'] = dict(p=p, rows=rows, LB_cfg=ex['LB'], windows={str(k): {str(c): v for c, v in w.items()} for k, w in W.items()})


# ------------------------------------------------------------------ 3. fig_cost: the count (window volume >= 1/p of F_p^s)
def column_covers(p, alpha, wins):
    """does the product window prod_i wins[i] (integer intervals, coordinate 0 = own) meet every line beta + F_p alpha
    (alpha[0] = 1)?  Projection along alpha onto F_p^(s-1) must be onto."""
    s = len(alpha); grids = np.meshgrid(*[np.arange(lo, hi + 1) for lo, hi in wins], indexing='ij')
    o = grids[0].ravel(); key = np.zeros_like(o)
    for i in range(1, s): key = key * p + (grids[i].ravel() - alpha[i] * o) % p
    return len(np.unique(key)) == p ** (s - 1)


def cube_edges(ax, lo, hi, **kw):
    for (u, v, w) in itertools.product((0, 1), repeat=3):
        P = np.array([(lo, hi)[u][0], (lo, hi)[v][1], (lo, hi)[w][2]], dtype=float)
        for dim in range(3):
            if (u, v, w)[dim] == 0:
                Q = P.copy(); Q[dim] = hi[dim]; ax.plot(*zip(P, Q), **kw)


def fig_cost():
    p2, kap = 7, 3
    K, W, ex = read_cfg(os.path.join(DATA, 'pp_s3_p31.cfg')); p = ex['p']
    fig = plt.figure(figsize=(WIDTH, 2.45))
    gs = fig.add_gridspec(1, 3, width_ratios=[1, 1, 1.3], wspace=0.12, left=0.045, right=0.99, top=0.8, bottom=0.1)
    res = {}
    for k, (box, ttl) in enumerate((((3, 3), r'(a) both entries read: a box,' + '\n' + r'$3\times3=9\geq p$ meets all $7$ lines'),
                                     ((1, 7), r'(b) cross entry free: a strip,' + '\n' + r'$1\times7=p$ meets all $7$ lines'))):
        ax = fig.add_subplot(gs[k]); assert column_covers(p2, (1, kap), [(0, box[0] - 1), (0, box[1] - 1)])
        ax.add_patch(Rectangle((-0.5, -0.5), box[0], box[1], fc=SHADE, ec=ACC, lw=0.7, zorder=0))
        for o in range(p2):
            for x in range(p2):
                bl = (x - kap * o) % p2; inb = o < box[0] and x < box[1]
                ax.text(o, x, str(bl), fontsize=5.6 if inb else 4.8, ha='center', va='center', color=INK if inb else '#a8a8a8', zorder=2)
        for t in range(p2):
            ax.add_patch(plt.Circle((t, (kap * t) % p2), 0.33, fill=False, ec=ACC2, lw=0.6, zorder=3))
        ax.set_xlim(-0.6, p2 - 0.4); ax.set_ylim(-0.6, p2 - 0.4); ax.set_aspect('equal')
        ax.set_xticks(range(p2)); ax.set_yticks(range(p2)); ax.tick_params(labelsize=5.5, length=0)
        ax.set_xlabel(r'own residue $o$', labelpad=1); ax.set_ylabel(r'cross residue $X$', labelpad=2) if k == 0 else None
        for sp in ax.spines.values(): sp.set_color(GRID)
        ax.set_title(ttl, pad=3)
    # (c) the three column windows of the p = 31 lex design: volume >= p^2 each, column 2 drawn
    vols = {}
    for cp in range(3):
        alpha = [1] + [int(K[c][cp]) for c in range(3) if c != cp]
        wins = [W[cp][cp]] + [W[cp][c] for c in range(3) if c != cp]
        wins = [(lo, hi) if hi - lo + 1 <= p else (-(p // 2), p // 2) for lo, hi in wins]
        ok = column_covers(p, alpha, wins); assert ok, cp
        vols[cp] = dict(alpha=alpha, sides=[hi - lo + 1 for lo, hi in wins], vol=int(np.prod([hi - lo + 1 for lo, hi in wins])), covers=ok)
    ax = fig.add_subplot(gs[2], projection='3d'); cp = 2
    wo, w0, w1 = W[cp][2], W[cp][0], W[cp][1]
    LO = np.array([wo[0] - 0.5, -p // 2 - 0.5, -p // 2 - 0.5]); HI = LO + p
    cube_edges(ax, LO, HI, color=GRID, lw=0.4)
    cube_edges(ax, np.array([wo[0] - 0.5, w0[0] - 0.5, w1[0] - 0.5]), np.array([wo[1] + 0.5, w0[1] + 0.5, w1[1] + 0.5]), color=ACC, lw=0.8)
    al = vols[cp]['alpha']; b = np.array([7, 11, -9]); pts = []
    for t in range(p):
        v = (b + t * np.array(al)) % p; v = v - p * (v > HI - 0.5) ; v = v + p * (v < LO + 0.5) * 0
        v = np.array([(v[i] - LO[i] - 0.5) % p + LO[i] + 0.5 for i in range(3)]); pts.append(v)
    pts = np.array(pts)
    ax.scatter(pts[:, 0], pts[:, 1], pts[:, 2], s=4, c=ACC2, depthshade=False, lw=0)
    inb = [k for k in range(p) if wo[0] <= pts[k, 0] <= wo[1] and w0[0] <= pts[k, 1] <= w0[1] and w1[0] <= pts[k, 2] <= w1[1]]
    assert inb
    for k in inb: ax.scatter(*pts[k], s=30, facecolors='none', edgecolors=ACC2, lw=0.9, depthshade=False)
    ax.set_xlim(LO[0], HI[0]); ax.set_ylim(LO[1], HI[1]); ax.set_zlim(LO[2], HI[2])
    ax.set_box_aspect((1, 1, 1)); ax.set_axis_off(); ax.view_init(elev=18, azim=-58)
    sd = vols
    ax.set_title(rf'(c) $p={p}$ ordered design, column 2:' + '\n' +
                 rf'${sd[2]["sides"][0]}\times{sd[2]["sides"][1]}\times{sd[2]["sides"][2]}={sd[2]["vol"]}\geq p^2={p * p}$', pad=-6)
    ax.text2D(0.5, 0.02, rf'columns 0, 1: ${sd[0]["sides"][0]}\times{p}\times{p}={sd[0]["vol"]}$, ${sd[1]["sides"][0]}\times{sd[1]["sides"][1]}\times{p}={sd[1]["vol"]}$'
              + '\n' + r'(free lower crosses fill whole axes)', transform=ax.transAxes, ha='center', va='bottom', fontsize=7.0, color='#444444')
    save(fig, 'fig_cost')
    VAL['cost'] = dict(p2=p2, kappa2=kap, columns_p31=vols, line_hits=len(inb))


# ------------------------------------------------------------------ 4. fig_lex: rule MR-A, p = 101 (mixed radix)
# ------------------------------------------------------------------ 5. fig_dim3: which 3D bases are covered, and how well
# theorem numbers as printed in paper/v3 (theorem counter shared with lemmas etc.).  Read from a main.aux when one is
# available (tectonic -X compile --keep-intermediates [--outdir D] main.tex; set GEOSEQ_AUX=D/main.aux), else the
# values checked against the 2026-10-27 V8 build (rem:p211 inserted after thm:LF).  Re-check after inserting or removing numbered environments.
THM_FALLBACK = {'thm:LF': '26', 'thm:MRall': '25', 'thm:A3': '38', 'rem:A3range': '39'}


# ------------------------------------------------------------------ 6. restyle: the staggered window system p = 101 at paper size
# The builders of make_figs_bs.py (screen size 12.6-13 in) are reused for the computations (slab_panel, panel3d,
# closest_pair, block_pts); only the layout is redone at \textwidth with the paper fonts.
PAPER_RC = dict(plt.rcParams)


def _restyle_child():
    import make_figs_bs as F
    plt.rcParams.update({k: PAPER_RC[k] for k in ('font.size', 'axes.titlesize', 'axes.labelsize', 'legend.fontsize',
                                                  'xtick.labelsize', 'ytick.labelsize', 'axes.linewidth')})
    p = 101; bb = B.BS3[p][1]; comp = [c for c in range(3) if c != bb]; LBbs = B.BS3[p][2]; res = {}
    X = B.bs3_points(p, p ** 3); Xf = B.faure_points(p, 3, p ** 3)
    i, j, d = F.closest_pair(X); fi, fj, fd = F.closest_pair(Xf)
    # (1) slabs of P_3
    fig, axs = plt.subplots(1, 3, figsize=(WIDTH, 2.55)); fig.subplots_adjust(left=0.03, right=0.99, top=0.83, bottom=0.17, wspace=0.12)
    A = X * p; dif = np.minimum(np.abs(np.floor(A[i]) - np.floor(A[j])), p - np.abs(np.floor(A[i]) - np.floor(A[j])))
    ci = min(comp, key=lambda q: dif[q]); cj = [q for q in comp if q != ci][0]
    F.slab_panel(axs[0], X, p, ci, cj, bb, i, j, 10, rf'staggered design: slab $\perp x_{ci}$,' + '\n' + rf'staggered coordinate $x_{bb}$ vertical')
    F.slab_panel(axs[1], X, p, bb, ci, cj, i, j, 10, rf'staggered design: slab $\perp x_{bb}$ (staggered' + '\n' + 'coordinate), other coordinates in-plane')
    Af = Xf * p; df = np.minimum(np.abs(np.floor(Af[fi]) - np.floor(Af[fj])), p - np.abs(np.floor(Af[fi]) - np.floor(Af[fj])))
    fs = int(np.argmin(df)); fu, fv = [q for q in range(3) if q != fs]
    F.slab_panel(axs[2], Xf, p, fs, fu, fv, fi, fj, 10, rf'Faure $(I,P,P^2)$: slab $\perp x_{fs}$' + '\n' + rf'$c(P_3)={fd * p:.4f}$ (no all-$K$ bound)')
    axs[0].text(0.5, -0.09, rf'$c(P_3)={d * p:.4f}$; certified $c(P_{{3K}})\geq{LBbs}$ (every $K$)', transform=axs[0].transAxes, ha='center', va='top', fontsize=6.5, color=ACC)
    for ax in axs:
        for coll in ax.collections:
            if hasattr(coll, 'get_sizes') and len(coll.get_sizes()) and coll.get_sizes()[0] >= 100: coll.set_sizes([55])
            elif hasattr(coll, 'get_sizes') and len(coll.get_sizes()) and coll.get_sizes()[0] >= 20: coll.set_sizes([13])
            elif hasattr(coll, 'get_sizes') and len(coll.get_sizes()): coll.set_sizes([4])
        ax.xaxis.label.set_size(6.5); ax.yaxis.label.set_size(6.5)
    fig.legend(handles=[Line2D([], [], color=GRID, lw=0.9, label='cell grid (side $1/p$)'),
                        Line2D([], [], ls='none', marker='o', ms=3.8, mfc='none', mec=LATE, mew=0.5, label='grid position'),
                        Line2D([], [], ls='none', marker='o', ms=2.2, mfc=INK, mec='none', label='point'),
                        Line2D([], [], color=JIT, lw=0.6, label='jitter'),
                        Line2D([], [], ls='none', marker='o', ms=6, mfc='none', mec=ACC, mew=0.9, label='closest pair (dashed: adjacent slab)')],
               loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.5, -0.01), fontsize=6.2, handlelength=1.5, columnspacing=1.0)
    save(fig, 'fig_bs_slab'); res['slab'] = dict(bs_c3=round(d * p, 4), fa_c3=round(fd * p, 4), axes=(ci, bb, fs))
    # (2) 3D blocks
    fig = plt.figure(figsize=(WIDTH, 2.45)); W6 = 6
    P, _ = F.block_pts(X, p, X[i] * p, W6); Pf, _ = F.block_pts(Xf, p, Xf[fi] * p, W6)
    for k, (PP, vert, ttl) in enumerate(((P, comp[0], rf'staggered design, $x_{comp[0]}$ vertical'),
                                         (P, bb, rf'staggered design, staggered coordinate' + '\n' + rf'$x_{bb}$ vertical (columns staggered by $\approx\frac{{1}}{{2}}$)'),
                                         (Pf, 2, r'Faure $(I,P,P^2)$'))):
        ax = fig.add_subplot(1, 3, k + 1, projection='3d'); F.panel3d(ax, PP, vert, ttl)
        ax.title.set_fontsize(7.0)
        for t in (ax.xaxis.label, ax.yaxis.label, ax.zaxis.label): t.set_fontsize(6.5)
        for coll in ax.collections: coll.set_sizes([3])
        for ln in ax.lines: ln.set_linewidth(ln.get_linewidth() * 0.55)
    fig.subplots_adjust(left=0.0, right=0.98, top=0.9, bottom=0.08, wspace=0.0)
    fig.text(0.5, 0.02, rf'$6\times6\times6$ cells of $P_3$, $p={p}$, around the closest pair; links $<1.12$ cells (darker = shorter); orange = shortest link',
             ha='center', fontsize=6.3)
    save(fig, 'fig_bs_3d')


TARGETS = {'cost': fig_cost, 'principles': fig_principles}
