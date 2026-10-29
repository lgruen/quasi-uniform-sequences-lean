"""make_figs.py -- figure builders of the paper (shared visual language, generator matrices, exact separations) and
the builders of the figures fig:idea, fig:hierarchy, fig:cert, fig:HB, fig:automaton, fig:B2 (run through
b1_relabel.py, b5_figs.py, b6_figs.py, which rename the embedded text to the wording of the paper). Imported also by
the explainers' data generator (explainers/gen_data.py).

Extracted from the development scripts of the paper: only the functions used by the figures of this paper are kept;
the code of the kept functions is unchanged except for the paths (module _paths).
Builders:
  Faure (I, P)            -- here (C_0 = I, C_1 = Pas_1)
  WF (brick wall, W^-)    -- wbuild.py (+ w_alib.py)  (rho = sqrt(1 - x), g_0 = 2/(rho(1+rho)), g_1 = (1+rho)/rho)
  HB window rules         -- hlib.py + hverify.greedy_pair + dlib.build_LI (+ t2d_alib.py)
  B2 (base 2)             -- b2core.py      (u = sum x^(2^k), g_0 = (1+x)(1+u), g_1 = u/x)
  F_4 arithmetic          -- klib.py
Visual language: cell grid, lattice image (open circle at n + R/q^j), actual point, jitter segment, one accent colour.
Every c printed in a panel is an EXACT toroidal c(P) = delta(P) N^(1/s) of the plotted point set (true points,
D digits), computed here.
"""
import _paths
import os, sys, math, time, itertools
import numpy as np
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, ConnectionPatch
from matplotlib.lines import Line2D
from matplotlib.collections import LineCollection
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)

OUT = _paths.OUT

# ------------------------------------------------------------------ builders
import wbuild
import hlib, dlib, hverify
import b2core
import klib

# ------------------------------------------------------------------ common visual language (= geo figs_arc.py)
plt.rcParams.update({
    'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
    'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False,
    'font.size': 7.5, 'axes.titlesize': 7.5, 'axes.labelsize': 7.5, 'legend.fontsize': 6.8,
    'xtick.labelsize': 6.3, 'ytick.labelsize': 6.3, 'axes.linewidth': 0.4,
    'xtick.major.width': 0.3, 'ytick.major.width': 0.3, 'xtick.major.size': 1.5, 'ytick.major.size': 1.5,
    'pdf.fonttype': 42, 'savefig.dpi': 300})
WIDTH = 6.3                     # \textwidth (amsart 11pt, margin 1.1in), as the geo paper
INK, GRID, FINE, LATE, JIT, ACC = '#111111', '#c8c8c8', '#e2e2e2', '#6f6f6f', '#4a4a4a', '#2b6cb0'
ACC2 = '#c05621'                # second accent, used only where two series must be told apart (F7)
S_PT, S_LAT = 7.0, 22.0
DASH = (0, (2.4, 1.3))


def legend_handles(keys):
    H = {'grid': Line2D([], [], color=GRID, lw=0.9, label='cell grid'),
         'lat': Line2D([], [], ls='none', marker='o', ms=4.4, mfc='none', mec=LATE, mew=0.6, label='grid position'),
         'pt': Line2D([], [], ls='none', marker='o', ms=2.7, mfc=INK, mec='none', label='actual point'),
         'jit': Line2D([], [], color=JIT, lw=0.7, label='jitter'),
         'pair': Line2D([], [], ls='none', marker='o', ms=6, mfc='none', mec=ACC, mew=0.9, label='closest pair'),
         'step': Line2D([], [], color=ACC, lw=1.1, label='offset law')}
    return [H[k] for k in keys]


def grid(ax, x0, x1, y0, y1, step=1.0, color=GRID, lw=0.35, z=0):
    xs = np.arange(np.ceil(x0 / step - 1e-9) * step, x1 + 1e-9, step)
    ys = np.arange(np.ceil(y0 / step - 1e-9) * step, y1 + 1e-9, step)
    segs = [[(x, y0), (x, y1)] for x in xs] + [[(x0, y), (x1, y)] for y in ys]
    ax.add_collection(LineCollection(segs, colors=color, linewidths=lw, zorder=z))


def draw_points(ax, ideal, actual, s_lat=S_LAT, s_pt=S_PT, jit=True, lat=True):
    if jit:
        ax.add_collection(LineCollection(np.stack([ideal, actual], 1), colors=JIT, linewidths=0.55, zorder=4))
    if lat:
        ax.scatter(ideal[:, 0], ideal[:, 1], s=s_lat, facecolors='none', edgecolors=LATE, linewidths=0.55, zorder=3)
    ax.scatter(actual[:, 0], actual[:, 1], s=s_pt, c=INK, lw=0, zorder=5)


def arrow(ax, o, v, col=ACC, lw=1.1, ls='-', ms=7, z=6):
    ax.annotate('', xy=(o[0] + v[0], o[1] + v[1]), xytext=(o[0], o[1]),
                arrowprops=dict(arrowstyle='-|>', color=col, lw=lw, ls=ls, mutation_scale=ms, shrinkA=0, shrinkB=0),
                zorder=z)


def label(ax, x, y, s, col=ACC, fs=7.0, ha='center', va='center', z=7, bg=True):
    ax.text(x, y, s, color=col, fontsize=fs, ha=ha, va=va, zorder=z,
            bbox=dict(fc='white', ec='none', pad=0.4, alpha=0.9) if bg else None)


def mark_pair(ax, P, r):
    for q in P:
        ax.add_patch(plt.Circle(q, r, fill=False, ec=ACC, lw=0.9, zorder=8))


def clean(ax, lim, ticks=False):
    ax.set_aspect('equal'); ax.set_xlim(*lim[0]); ax.set_ylim(*lim[1])
    if not ticks: ax.set_xticks([]); ax.set_yticks([])
    for s in ax.spines.values(): s.set_color(GRID)


def save(fig, name):
    for ext in ('pdf', 'png'):
        fig.savefig(os.path.join(OUT, f'{name}.{ext}'), dpi=200 if ext == 'png' else None)
    plt.close(fig)
    print('  wrote', name + '.pdf', flush=True)

# ------------------------------------------------------------------ generator matrices (C_c[n][k], numpy int64)
def Dfor(q):                    # true-point digit depth with q^D < 2^52 (exact in float64 after scaling)
    return int(52 / math.log2(q))


def mats_faure(p, D):
    C1 = np.array([[math.comb(k, n) % p for k in range(D)] for n in range(D)], dtype=np.int64)
    return dict(name='Faure', q=p, s=2, C=[np.eye(D, dtype=np.int64), C1])


def mats_wf(p, D):
    """Theorem WF, rule W^- (eps = -1, theta = -1/4); builder wbuild.py."""
    th = (-pow(4, p - 2, p)) % p
    E = wbuild.build(p, -1, th); _, S = wbuild.series_all(p, -1, th, E, D + 12)
    C = wbuild.genmats(p, S, D)
    return dict(name='WF', q=p, s=2, C=[np.array(C[c], dtype=np.int64) for c in (0, 1)])


def mats_window(p, D, fam, *par):
    """Theorem GA window scrambles: fam 'hf' (half-frozen, par = (b,)) or 'hb' (brick hybrid, par = (b, e))."""
    if fam == 'hf':
        d = hlib.hf_params(p, *par); th = par[0]; LB = hlib.hf_formula(p, *par)
    else:
        d = hlib.hb_params(p, *par); th = d['q'] * par[1]; LB = hlib.hb_formula(p, *par)
    k0, k1 = d['k0'] % p, d['k1'] % p
    assert (k0 * k1 - th * th) % p == 0
    n = D + 2
    X1, O0 = hverify.greedy_pair(p, k0, th, d['WoA'], d['WxA'], n)
    X0, O1 = hverify.greedy_pair(p, k1, th, d['WoB'], d['WxB'], n)
    s = th * dlib.inv(k1, p) % p
    L0, L1, _, _ = dlib.build_LI(p, th, s, X0, X1, D)
    C0, C1 = dlib.gen_mats(p, L0, L1, D, D)
    return dict(name=fam.upper(), q=p, s=2, C=[np.array(C0, dtype=np.int64), np.array(C1, dtype=np.int64)], LB=LB,
                law=dict(X0=X0, X1=X1, O0=O0, O1=O1))


def mats_b2(D=32):
    """Theorem B2 (closed form); bit n of column k = C[n][k]; b2core.B2 = [cols(g0,u), cols(g1,1+u)]."""
    C = [np.array([[(b2core.B2[c][k] >> n) & 1 for k in range(D)] for n in range(D)], dtype=np.int64) for c in (0, 1)]
    return dict(name='B2', q=2, s=2, C=C)


F4 = klib.Field(4)


# ------------------------------------------------------------------ true points (integer coordinates, scale q^D)
def index_digits(q, m, idx):
    return np.stack([(idx // q ** k) % q for k in range(m)], 1)


def points_int(net, m, idx=None):
    """integer coordinates X[:, c] = sum_n y_{c,n} q^(D-1-n) of the points with index idx (default all v < q^m)."""
    q, C = net['q'], net['C']; D = C[0].shape[0]
    idx = np.arange(q ** m, dtype=np.int64) if idx is None else np.asarray(idx, dtype=np.int64)
    V = index_digits(q, m, idx)
    w = q ** np.arange(D - 1, -1, -1, dtype=np.int64)
    out = []
    for Cc in C:
        if q == 4:                                   # F_4: digit products by table, addition = XOR
            Y = np.zeros((len(idx), D), np.int64)
            for k in range(m):
                Y ^= F4.MUL[Cc[:, k][None, :], V[:, k][:, None]]
        else:
            Y = (V @ Cc[:, :m].T) % q
        out.append(Y @ w)
    return np.stack(out, 1), q ** D


def mind_brute(X, scale):
    P = X / scale; best = (9.0, 0, 0)
    for a in range(0, len(P), 1024):
        d = np.abs(P[a:a + 1024, None, :] - P[None]); d = np.minimum(d, 1 - d); d2 = (d ** 2).sum(-1)
        r = np.arange(d2.shape[0]); d2[r, a + r] = 9
        i, j = np.unravel_index(d2.argmin(), d2.shape)
        if d2[i, j] < best[0]: best = (d2[i, j], a + i, j)
    return math.sqrt(best[0]), best[1], best[2]


def mind_net2(X, scale, g):
    """exact toroidal delta of a 2D set with exactly one point per cell of side 1/g (a (0,2K,2)-net, g = q^K):
    a closest pair lies within Chebyshev cell distance 3 (adjacent cells give delta < sqrt(5)/g)."""
    assert scale % g == 0; cell = X // (scale // g); key = cell[:, 0] * g + cell[:, 1]
    assert len(np.unique(key)) == g * g == len(X), 'not one point per cell'
    at = np.empty(g * g, np.int64); at[key] = np.arange(len(X)); at = at.reshape(g, g)
    P = X / scale; best = (9.0, 0, 0)
    for dx in range(0, 4):
        for dy in range(-3, 4):
            if dx == 0 and dy <= 0: continue
            J = at[(cell[:, 0] + dx) % g, (cell[:, 1] + dy) % g]
            d = np.abs(P - P[J]); d = np.minimum(d, 1 - d); d2 = (d ** 2).sum(1)
            i = d2.argmin()
            if d2[i] < best[0]: best = (d2[i], i, J[i])
    return math.sqrt(best[0]), best[1], best[2]


def sep(X, scale, s=2, g=None):
    """exact c(P) = delta(P) N^(1/s) and the closest pair (i, j)."""
    d, i, j = mind_net2(X, scale, g) if g else mind_brute(X, scale)
    return d * len(X) ** (1.0 / s), i, j


def cellview(X, scale, g, j_dig, q):
    """cell units at level g = q^K: actual = g*y; lattice image = n + R/q^j (j geometric digits)."""
    A = X * (g / scale)
    n = np.floor(A); R = np.floor((A - n) * q ** j_dig) / q ** j_dig
    return n + R, A

def points_cells(net, K, cells):
    """graph form: the unique index v < p^(2K) whose level-K cell is n = (n_0, n_1), for each n in cells (prime p).
    Returns integer coordinates (scale p^D) of those points of P_{2K} -- no enumeration of the whole prefix."""
    p, C = net['q'], net['C']; D = C[0].shape[0]; m = 2 * K
    B = np.vstack([C[0][:K, :m], C[1][:K, :m]]) % p              # cell digits = B v
    A = np.hstack([B, np.eye(m, dtype=np.int64)])                # Gauss-Jordan inverse mod p
    for col in range(m):
        piv = next(r for r in range(col, m) if A[r, col] % p)
        A[[col, piv]] = A[[piv, col]]; A[col] = A[col] * pow(int(A[col, col]), p - 2, p) % p
        for r in range(m):
            if r != col and A[r, col]: A[r] = (A[r] - A[r, col] * A[col]) % p
    Binv = A[:, m:]
    cells = np.asarray(cells, dtype=np.int64)
    dig = np.hstack([np.stack([(cells[:, c] // p ** (K - 1 - i)) % p for i in range(K)], 1) for c in (0, 1)])
    V = (dig @ Binv.T) % p                                        # index digits v_0..v_{m-1}
    idx = (V * p ** np.arange(m, dtype=np.int64)).sum(1)
    X, sc = points_int(net, m, idx)
    assert np.all(X // (sc // p ** K) == cells), 'graph-form inversion failed'
    return X, sc

# ------------------------------------------------------------------ shared panel helpers
def pair_images(A, i, j, g):
    """positions (cell units) of the closest pair, j moved to its torus image nearest to i."""
    a, b = A[i].copy(), A[j].copy()
    b += g * np.round((a - b) / g)
    return a, b


def window_pts(ideal, A, x0, y0, W, H, g):
    """all torus copies of the points inside [x0, x0+W) x [y0, y0+H) (cell units)."""
    I, P = [], []
    for sx in (-g, 0, g):
        for sy in (-g, 0, g):
            sh = np.array([sx, sy]); Q = A + sh
            k = (Q[:, 0] >= x0) & (Q[:, 0] < x0 + W) & (Q[:, 1] >= y0) & (Q[:, 1] < y0 + H)
            I.append(ideal[k] + sh); P.append(Q[k])
    return np.vstack(I), np.vstack(P)


def fmtc(c):
    return f'{c:.4f}'

# ------------------------------------------------------------------ F1: hero, same prime, three scrambles
# ------------------------------------------------------------------ F2: idea -- the same law at every level (revision 2: D8)
def fig2():
    p = 7; D = Dfor(p); net = mats_wf(p, D); DL = law_D(net, 4, 2)[:, 0]
    fig = plt.figure(figsize=(WIDTH, 2.42))
    gs = fig.add_gridspec(1, 4, width_ratios=[7, 7, 7, 4.6], wspace=0.13, left=0.012, right=0.99, top=0.85, bottom=0.1)
    axs = [fig.add_subplot(gs[k]) for k in range(4)]
    sub = (3, 3)                                    # zoom into local cell (3, 3) at each level
    org = np.array([0, 0]); laws = []; Rprev = None; marked = []
    for K, ax in zip((1, 2, 3), axs):
        cells = np.array([(org[0] + a, org[1] + b) for a in range(p) for b in range(p)])
        X, sc = points_cells(net, K, cells)
        ideal, A = cellview(X, sc, p ** K, 1, p)
        x0, y0 = org
        grid(ax, x0, x0 + p, y0, y0 + p, lw=0.45)
        draw_points(ax, ideal, A, s_lat=30, s_pt=9)
        lookup = {tuple(cc): ideal[k] for k, cc in enumerate(cells)}
        for a in range(1, 5):
            u = lookup[(x0 + a, y0 + 1)]; v = lookup[(x0 + a + 1, y0 + 1)]; arrow(ax, u, v - u, lw=0.9, ms=6)
        for b in range(2, 5):
            u = lookup[(x0 + 1, y0 + b)]; v = lookup[(x0 + 1, y0 + b + 1)]; arrow(ax, u, v - u, lw=0.9, ms=6)
        # the law itself, read off the real points: change of the geometric digits (r_0, r_1) mod p per step
        R = np.rint((ideal - np.floor(ideal)) * p).astype(int)
        Rd = {tuple(cc): R[k] for k, cc in enumerate(cells)}
        sx = {tuple((Rd[(x0 + a + 1, y0 + b)] - Rd[(x0 + a, y0 + b)]) % p) for a in range(p - 1) for b in range(p)}
        sy = {tuple((Rd[(x0 + a, y0 + b + 1)] - Rd[(x0 + a, y0 + b)]) % p) for a in range(p) for b in range(p - 1)}
        assert len(sx) == 1 and len(sy) == 1, (sx, sy)          # one law for every step inside the panel
        (ax0, ax1), (ay0, ay1) = sx.pop(), sy.pop(); laws.append(((ax0, ax1), (ay0, ay1)))
        assert (ax0, ax1) == (DL[1, 0, 0], DL[1, 1, 0]) and (ay0, ay1) == (DL[1, 0, 1], DL[1, 1, 1])   # = D(1)
        Rloc = np.array([Rd[(x0 + a, y0 + b)] for a in range(p) for b in range(p)])
        if Rprev is not None: assert ((Rloc - Rprev) % p == [3, 0]).all()            # first digits shift by (3,0)
        Rprev = Rloc
        # digit changes printed on two arrows; the local cell (0, 0) marked with its geometric digits
        u = lookup[(x0 + 2, y0 + 1)]; v = lookup[(x0 + 3, y0 + 1)]
        label(ax, (u[0] + v[0]) / 2, (u[1] + v[1]) / 2 - 0.42, f'$({ax0},{ax1})$', fs=6.3)
        u = lookup[(x0 + 1, y0 + 3)]; v = lookup[(x0 + 1, y0 + 4)]
        label(ax, (u[0] + v[0]) / 2 - 0.55, (u[1] + v[1]) / 2, f'$({ay0},{ay1})$', fs=6.3)
        mc = (x0 + 5, y0 + 5); r00 = Rd[mc]; marked.append(tuple(int(t) for t in r00))
        ax.add_patch(Rectangle(mc, 1, 1, fc='none', ec=ACC2, lw=0.8, zorder=8))
        label(ax, mc[0] + 0.5, mc[1] + 1.4, rf'$(r_0,r_1)=({r00[0]},{r00[1]})$', fs=5.8, col=ACC2)
        for a in range(p):                                       # cell indices along the bottom and left edges
            ax.text(x0 + a + 0.5, y0 - 0.12, str(x0 + a), fontsize=4.8, ha='center', va='top', color=LATE)
            ax.text(x0 - 0.1, y0 + a + 0.5, str(y0 + a), fontsize=4.8, ha='right', va='center', color=LATE)
        if K < 3:
            ax.add_patch(Rectangle((x0 + sub[0], y0 + sub[1]), 1, 1, fc='none', ec=ACC, lw=0.8, zorder=8))
        clean(ax, ((x0 - 0.75, x0 + p), (y0 - 0.6, y0 + p)))
        for sp in ax.spines.values(): sp.set_visible(False)
        ax.set_title(rf'$K={K}$: $P_{{{2 * K}}}$' + ('' if K == 1 else rf' in one level-${K - 1}$ cell')
                     + '\n' + r'side $7^{-%d}$; all steps carry length $1$' % K, pad=3)
        if K > 1:                                    # connect the zoomed cell of the previous panel
            prev = axs[K - 2]; po = org // p
            for (cx, cy), (tx, ty) in (((po[0] + 1, po[1] + 1), (x0, y0 + p)), ((po[0] + 1, po[1]), (x0, y0))):
                fig.add_artist(ConnectionPatch((cx, cy), (tx, ty), 'data', 'data', axesA=prev, axesB=ax,
                                               color=LATE, lw=0.4, ls=(0, (1, 1.5))))
        org = (org + np.array(sub)) * p
    # (d) one step across a boundary of carry length 2 (level 2, n_0 = 27 -> 28 = 4*7): the jump is D(2), not D(1)
    ax = axs[3]; K = 2; xs, ys = 26, 23; Wd, Hd = 4, 5
    cells = np.array([(xs + a, ys + b) for a in range(Wd) for b in range(Hd)])
    X, sc = points_cells(net, K, cells); ideal, A = cellview(X, sc, p ** K, 1, p)
    lookup = {tuple(cc): ideal[k] for k, cc in enumerate(cells)}
    Rd = {tuple(cc): np.rint((ideal[k] - np.floor(ideal[k])) * p).astype(int) for k, cc in enumerate(cells)}
    grid(ax, xs, xs + Wd, ys, ys + Hd, lw=0.45)
    ax.plot([28, 28], [ys, ys + Hd], color='#7fa6d1', lw=1.4, zorder=1)
    draw_points(ax, ideal, A, s_lat=30, s_pt=9)
    vr = ys + 2; jumps = []
    for a in range(Wd - 1):
        u = lookup[(xs + a, vr)]; v = lookup[(xs + a + 1, vr)]; l = 2 if xs + a + 1 == 28 else 1
        dl = tuple(int(t) for t in (Rd[(xs + a + 1, vr)] - Rd[(xs + a, vr)]) % p); jumps.append((l, dl))
        assert dl == (DL[l, 0, 0], DL[l, 1, 0])
        arrow(ax, u, v - u, col='#173f6e' if l == 2 else ACC, lw=1.3 if l == 2 else 0.9, ms=6)
        label(ax, (u[0] + v[0]) / 2, (u[1] + v[1]) / 2 + (0.62 if l == 2 else -0.5), rf'$({dl[0]},{dl[1]})$', fs=6.3,
              col='#173f6e' if l == 2 else ACC)
        if l == 2:
            gh = np.array([28, vr]) + ((Rd[(27, vr)] + [DL[1, 0, 0], DL[1, 1, 0]]) % p) / p
            ax.scatter(*gh, s=30, facecolors='none', edgecolors=ACC2, lw=0.7, ls=(0, (1.5, 1)), zorder=6)
    for a in range(Wd):
        ax.text(xs + a + 0.5, ys - 0.12, str(xs + a), fontsize=4.8, ha='center', va='top', color=LATE)
    clean(ax, ((xs - 0.1, xs + Wd + 0.1), (ys - 0.6, ys + Hd + 0.6)))
    for sp in ax.spines.values(): sp.set_visible(False)
    ax.set_title('$K=2$ across $n_0=28$:\ncarry length $2$', pad=3)
    fig.legend(handles=[Line2D([], [], ls='none', marker='o', ms=4.4, mfc='none', mec=LATE, mew=0.6,
                               label='grid position (from the first geometric digit)')] +
               legend_handles(['pt', 'jit']) +
               [Line2D([], [], color=ACC, lw=1.1, label=r'step: change of $(r_0,r_1)$ mod 7'),
                Line2D([], [], ls='none', marker='o', ms=4.4, mfc='none', mec=ACC2, mew=0.8, label='image if carry-free')],
               loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.5, -0.01), handlelength=1.5,
               columnspacing=1.0, handletextpad=0.4, fontsize=6.2)
    save(fig, 'fig_idea')
    return dict(laws=[tuple(tuple(int(t) for t in s_) for s_ in L) for L in laws], marked_r=marked, depth2=jumps)

# ------------------------------------------------------------------ F3: dislocations (B2): carry lengths and responses
# ------------------------------------------------------------------ F4: brick wall (schematic + real WF zooms)
# ------------------------------------------------------------------ F5: brick hybrid HB (schematic + real p = 401)
def near_edges(ax, P, rmax=1.2, col=ACC, lw=0.35):
    d = np.linalg.norm(P[:, None] - P[None], axis=-1)
    ii, jj = np.where(np.triu(d < rmax, 1))
    ax.add_collection(LineCollection(np.stack([P[ii], P[jj]], 1), colors=col, linewidths=lw, zorder=2, alpha=0.6))


def slip_lines(ax, A, x0, y0, W, col=ACC, lw=0.9):
    """mark the slips of a window: cell boundaries across which a fractional offset jumps UP by more than 1/2
    (the offset wraps mod 1, so the two points are about two cells apart: a gap, i.e. a missing column/row).
    A = all point positions (cell units) covering cells [x0-1, x0+W] x [y0-1, y0+W]."""
    n = np.floor(A).astype(np.int64); F = A - n
    at = {(int(u), int(v)): f for (u, v), f in zip(n, F)}
    segs = []
    for u in range(x0 - 1, x0 + W):
        for v in range(y0 - 1, y0 + W):
            f = at[(u, v)]
            if x0 <= u + 1 < x0 + W and y0 <= v < y0 + W and at[(u + 1, v)][0] - f[0] > 0.5:
                segs.append([(u + 1, v), (u + 1, v + 1)])
            if y0 <= v + 1 < y0 + W and x0 <= u < x0 + W and at[(u, v + 1)][1] - f[1] > 0.5:
                segs.append([(u, v + 1), (u + 1, v + 1)])
    ax.add_collection(LineCollection(segs, colors=col, linewidths=lw, linestyles=[DASH], zorder=6))
    return len(segs)


def fig5():
    fig, axs = plt.subplots(1, 3, figsize=(WIDTH, 2.6), gridspec_kw=dict(wspace=0.1, left=0.01, right=0.99,
                                                                         top=0.85, bottom=0.12))
    ax = axs[0]; nc, nr, kap = 8, 6, 1 - math.sqrt(3) / 2
    grid(ax, 0, nc, 0, nr)
    pts = []
    for a in range(-1, nc + 1):
        r0 = (0.55 - kap * a) % 1.0                  # x-step moves x by 1 - kap ~ sqrt(3)/2 (one slip when r0 wraps)
        h = 0.25 + 0.5 * (a % 2)                      # brick wall in y: half a cell between columns
        pts += [(a + r0, b + h) for b in range(-1, nr + 1)]
    P = np.array(pts)
    near_edges(ax, P, 1.08)
    ax.scatter(P[:, 0], P[:, 1], s=7, c=INK, lw=0, zorder=5)
    xs = 4 + (0.55 - 4 * kap) % 1.0                  # last column before the offset wraps: a slip follows
    ax.plot([xs + 0.93, xs + 0.93], [0, nr], color=ACC, lw=0.9, ls=DASH, zorder=6)
    label(ax, xs + 0.93, nr - 0.35, 'slip', fs=6.5)
    clean(ax, ((0, nc), (0, nr)))
    ax.set_title('(a) schematic: brick wall in $y$ +\ncolumns compressed to hexagonal spacing', pad=3)
    p = 401; LB, (b, e) = hlib.hb_best(p); net = mats_window(p, Dfor(p), 'hb', b, e)
    # (b) whole prefix P_2: exact c, zoom around its closest pair
    X, sc = points_int(net, 2); c2, i, j = sep(X, sc, g=p)
    ideal, A = cellview(X, sc, p, 1, p); a_, b_ = pair_images(A, i, j, p); W = 11
    x0 = int(np.floor((a_[0] + b_[0]) / 2)) - W // 2; y0 = int(np.floor((a_[1] + b_[1]) / 2)) - W // 2
    I, Q = window_pts(ideal, A, x0 - 1, y0 - 1, W + 2, W + 2, p)
    ax = axs[1]; grid(ax, x0, x0 + W, y0, y0 + W); near_edges(ax, Q, 1.12)
    assert len(Q) == (W + 2) ** 2 and len({tuple(c) for c in np.floor(Q).astype(int)}) == (W + 2) ** 2  # 1 pt/cell
    nsl_b = slip_lines(ax, Q, x0, y0, W)
    draw_points(ax, I, Q, s_lat=16, s_pt=6); mark_pair(ax, (a_, b_), 0.28)
    clean(ax, ((x0, x0 + W), (y0, y0 + W)))
    ax.set_title(rf'(b) HB, $p={p}$, $P_2$ (${W}\times{W}$ cells)' + '\n' + rf'$c(P_2) = {fmtc(c2)}$', pad=3)
    # (c) a window of P_4 by the graph form (the prefix has 401^4 points; exact c not computed)
    K = 2; x0, y0 = 3 * p + 150, 5 * p + 220
    cells = np.array([(x0 + u, y0 + v) for u in range(-1, W + 1) for v in range(-1, W + 1)])
    X, sc = points_cells(net, K, cells); ideal, A = cellview(X, sc, p ** K, 1, p)
    ax = axs[2]; grid(ax, x0, x0 + W, y0, y0 + W); near_edges(ax, A, 1.12); nsl_c = slip_lines(ax, A, x0, y0, W)
    draw_points(ax, ideal, A, s_lat=16, s_pt=6); clean(ax, ((x0, x0 + W), (y0, y0 + W)))
    ax.set_title(rf'(c) HB, $p={p}$, window of $P_4$' + '\n' + rf'certified $c(P_{{2K}})\geq {LB:.4f}$ for all $K$', pad=3)
    fig.legend(handles=legend_handles(['lat', 'pt', 'jit', 'pair']) +
               [Line2D([], [], color=ACC, lw=0.5, alpha=0.6, label='pairs closer than 1.12 cells'),
                Line2D([], [], color=ACC, lw=0.9, ls=DASH, label='slip (offset wraps)')],
               loc='lower center', ncol=6, frameon=False, bbox_to_anchor=(0.5, 0.0), handlelength=1.8,
               columnspacing=1.2, handletextpad=0.5)
    save(fig, 'fig_HB')
    return dict(p=p, b=b, e=e, LB=LB, c2=c2, slips_b=nsl_b, slips_c=nsl_c)

# ------------------------------------------------------------------ F6: 3D, K4 over F_4 -- P_6 (4^6 points)
# ------------------------------------------------------------------ F7: practice -- c(N) of every prefix
# ------------------------------------------------------------------ F8: Theorem L_3 (3D, p = 1 mod 3) -- P_3, Lambda'
# ================================================================== revision 2 (CLARITY1 §D): shared helpers
def inv_mod(B, p):
    """inverse of a square integer matrix mod a prime p (Gauss-Jordan)."""
    m = B.shape[0]; A = np.hstack([np.asarray(B, np.int64) % p, np.eye(m, dtype=np.int64)])
    for col in range(m):
        piv = next(r for r in range(col, m) if A[r, col] % p)
        A[[col, piv]] = A[[piv, col]]; A[col] = A[col] * pow(int(A[col, col]), p - 2, p) % p
        for r in range(m):
            if r != col and A[r, col]: A[r] = (A[r] - A[r, col] * A[col]) % p
    return A[:, m:]


def law_D(net, K, L, j=1):
    """carry responses D_i(l)[c][c'] (prime q), l = 1..L <= K, i < j, straight from the generator matrices: change of
    geometric digit K+i of coordinate c when 1 is added to each of the l finest level-K cell digits of coordinate c'.
    Returns an array out[l, i, c, c'] (out[0] = 0)."""
    p, C = net['q'], net['C']; s = len(C); m = s * K
    Binv = inv_mod(np.vstack([Cc[:K, :m] for Cc in C]), p)
    out = np.zeros((L + 1, j, s, s), np.int64)
    for cp in range(s):
        for l in range(1, L + 1):
            e = np.zeros(m, np.int64); e[cp * K + K - l:cp * K + K] = 1
            v = Binv @ e % p
            for c in range(s): out[l, :, c, cp] = C[c][K:K + j, :m] @ v % p
    return out


def f_j(e, sig, q, j=1):
    """certificate gap f_j(e, sigma) of Lemma cert (prime q; sigma = tuple of j digits), in cell units."""
    sig = np.atleast_1d(sig) % q; R = np.array([[(r // q ** (j - 1 - i)) % q for i in range(j)] for r in range(q ** j)])
    w = q ** np.arange(j - 1, -1, -1)
    return max(0, np.abs(e * q ** j + ((R + sig) % q) @ w - R @ w).min() - 1) / q ** j


# ------------------------------------------------------------------ F9: the certificate in one picture (schematic + exact f_1)
JITC = '#dde6f2'


def jit_box(ax, x, y, w, h, z=2):
    ax.add_patch(Rectangle((x, y), w, h, fc=JITC, ec='none', zorder=z))


def fig_cert():
    p = 7
    fig = plt.figure(figsize=(WIDTH, 2.6))
    gs = fig.add_gridspec(1, 3, width_ratios=[1.3, 1.0, 0.95], wspace=0.3, left=0.01, right=0.99, top=0.84,
                          bottom=0.21)
    # (a) 1D: two neighbouring cells, sub-grid of q = 7, worst position R, jitter bar, gap f_1(1, sigma)
    ax = fig.add_subplot(gs[0]); out = {}
    for sig, R, y in ((-3, 5, 1.3), (1, 6, 0.0)):
        for x in range(3):
            ax.plot([x, x], [y - 0.28, y + 0.28], color=GRID, lw=0.9, zorder=1)
        for k in range(15):
            ax.plot([k / p, k / p], [y - 0.1, y + 0.1], color=GRID, lw=0.4, zorder=1)
        ax.plot([0, 2], [y, y], color=GRID, lw=0.5, zorder=1)
        Rn = (R + sig) % p; a_img, b_img = R / p, 1 + Rn / p
        jit_box(ax, a_img, y - 0.07, 1 / p, 0.14); jit_box(ax, b_img, y - 0.07, 1 / p, 0.14)
        ax.scatter([a_img, b_img], [y, y], s=S_LAT, facecolors='none', edgecolors=LATE, lw=0.6, zorder=4)
        pa, pb = a_img + 1 / p, b_img                      # worst case: own jitter maximal, neighbour's zero
        ax.scatter([pa, pb], [y, y], s=S_PT + 2, c=INK, lw=0, zorder=5)
        gap = f_j(1, sig, p); out[sig] = gap
        assert abs(gap - max(0.0, pb - pa)) < 1e-12           # the drawn worst case realises f_1 exactly
        if gap > 0:
            ax.annotate('', xy=(pb, y + 0.19), xytext=(pa, y + 0.19), arrowprops=dict(arrowstyle='<|-|>', color=ACC,
                        lw=0.8, mutation_scale=5, shrinkA=0, shrinkB=0), zorder=6)
            label(ax, (pa + pb) / 2, y + 0.38, rf'gap $f_1(1,{sig})=\frac{{{round(gap * p)}}}{{7}}$', fs=6.6)
            verdict = 'safe: backward shift'
        else:
            ax.scatter([pa], [y], s=75, facecolors='none', edgecolors=ACC2, lw=0.9, zorder=7)
            label(ax, pa, y + 0.38, r'gap $f_1(1,+1)=0$: points can touch', fs=6.6, col=ACC2)
            verdict = 'fatal: forward by one'
        ax.text(0.0, y - 0.47, rf'$\sigma={sig:+d}$ ({verdict}): $R={R}$, $R\oplus\sigma={Rn}$',
                fontsize=6.3, ha='left', va='center', color=INK)
        ax.text(0.5, y - 0.27, 'cell $n$', fontsize=6.0, ha='center', va='center', color=LATE)
        ax.text(1.5, y - 0.27, 'cell $n+1$', fontsize=6.0, ha='center', va='center', color=LATE)
    ax.set_xlim(-0.03, 2.03); ax.set_ylim(-0.6, 1.8); ax.axis('off')
    ax.set_title('(a) neighbouring cells, $7$ sub-intervals each;\nworst position $R$, jitter $\\leq\\frac{1}{7}$ (shaded)', pad=3)
    # (b) f_1(1, sigma) (coordinate moves to the next cell) and f_1(0, sigma) (coordinate stays) over F_7
    ax = fig.add_subplot(gs[1]); S = np.arange(-3, 4)
    own = np.array([f_j(1, s, p) for s in S]); crs = np.array([f_j(0, s, p) for s in S])
    ax.bar(S - 0.19, own, 0.36, color=ACC, label=r'$f_1(1,\sigma)$: own (moving)')
    ax.bar(S + 0.19, crs, 0.36, color=LATE, label=r'$f_1(0,\sigma)$: cross (at rest)')
    for s, v in zip(S, own):
        if v == 0: ax.text(s - 0.19, 0.02, 'fatal', rotation=90, fontsize=5.8, ha='center', va='bottom', color=ACC2)
    for s, v in zip(S, crs):
        if v == 0: ax.text(s + 0.19, 0.02, '0', fontsize=5.8, ha='center', va='bottom', color=LATE)
    ax.set_xticks(S); ax.set_xticklabels([f'{s:+d}' if s else '0' for s in S])
    ax.set_yticks([0, 2 / 7, 4 / 7, 6 / 7]); ax.set_yticklabels(['0', '2/7', '4/7', '6/7'])
    ax.set_xlabel(r'shift $\sigma$ of the geometric digit (mod 7)', labelpad=1); ax.set_ylim(0, 1.15)
    ax.legend(frameon=False, loc='upper left', fontsize=6.0, handlelength=1.2, borderaxespad=0.1)
    for sp in ('top', 'right'): ax.spines[sp].set_visible(False)
    ax.set_title('(b) guaranteed gap per coordinate:\nown backward, cross near $\\pm\\frac{1}{2}$', pad=3)
    # (c) 2D: a cell and its neighbours (4 steps up to sign); one diagonal step sigma = (-3, -2): 3/7, 4/7 -> 5/7
    ax = fig.add_subplot(gs[2]); grid(ax, -1, 2, -1, 2, lw=0.7)
    fine = []
    for (cx, cy) in ((0, 0), (1, 1)):
        for k in range(1, p):
            fine += [[(cx + k / p, cy), (cx + k / p, cy + 1)], [(cx, cy + k / p), (cx + 1, cy + k / p)]]
    ax.add_collection(LineCollection(fine, colors=FINE, linewidths=0.4, zorder=0))
    R0, R1, s0, s1 = 5, 5, -3, -2
    g0, g1 = f_j(1, s0, p), f_j(1, s1, p); dist = math.hypot(g0, g1)
    a = np.array([R0 / p, R1 / p]); b = np.array([1 + (R0 + s0) % p / p, 1 + (R1 + s1) % p / p])
    jit_box(ax, *a, 1 / p, 1 / p); jit_box(ax, *b, 1 / p, 1 / p)
    pa, pb = a + 1 / p, b
    assert abs(pb[0] - pa[0] - g0) < 1e-12 and abs(pb[1] - pa[1] - g1) < 1e-12
    ax.add_patch(plt.Circle(pa, dist, fc=ACC, alpha=0.08, ec=ACC, lw=0.5, zorder=1))
    for e in ((1, 0), (0, 1), (1, -1), (-1, 0), (0, -1), (-1, 1), (-1, -1)):
        arrow(ax, (0.5, 0.5), (0.8 * e[0], 0.8 * e[1]), col=GRID, lw=0.6, ms=5, z=1)
    ax.scatter(*zip(a, b), s=S_LAT, facecolors='none', edgecolors=LATE, lw=0.6, zorder=4)
    ax.scatter(*zip(pa, pb), s=S_PT + 2, c=INK, lw=0, zorder=5)
    ax.plot([pa[0], pb[0]], [pa[1], pa[1]], color=ACC, lw=0.8, zorder=6)
    ax.plot([pb[0]] * 2, [pa[1], pb[1]], color=ACC, lw=0.8, zorder=6)
    ax.plot(*zip(pa, pb), color=ACC, lw=0.9, ls=DASH, zorder=6)
    label(ax, (pa[0] + pb[0]) / 2, pa[1] - 0.14, r'$\frac{3}{7}$', fs=7)
    label(ax, pb[0] + 0.15, (pa[1] + pb[1]) / 2, r'$\frac{4}{7}$', fs=7)
    label(ax, (pa[0] + pb[0]) / 2 - 0.12, (pa[1] + pb[1]) / 2 + 0.1, r'$\frac{5}{7}$', fs=7)
    clean(ax, ((-1, 2), (-1, 2)))
    ax.set_title(r'(c) diagonal step, $\sigma=(-3,-2)$:' + '\n' + r'$\sqrt{f_1(1,-3)^2+f_1(1,-2)^2}=\frac{5}{7}$', pad=3)
    fig.legend(handles=legend_handles(['lat', 'pt']) + [Rectangle((0, 0), 1, 1, fc=JITC, ec='none', label='possible jitter'),
               Line2D([], [], color=ACC, lw=0.8, label='worst-case gap'),
               Rectangle((0, 0), 1, 1, fc=ACC, alpha=0.08, ec=ACC, lw=0.5, label='excluded disc (radius = bound)')],
               loc='lower center', ncol=5, frameon=False, bbox_to_anchor=(0.5, -0.01), handlelength=1.8, columnspacing=1.3)
    save(fig, 'fig_cert')
    return dict(gaps={k: round(v * p, 6) for k, v in out.items()},
                own7=dict(zip(S.tolist(), (own * p).round().astype(int).tolist())),
                cross7=dict(zip(S.tolist(), (crs * p).round().astype(int).tolist())), diag7=round(dist * p, 6))

# ------------------------------------------------------------------ F10: dislocation hierarchy of the running example W^- (p = 7)
RAMP = ['#cfcfcf', '#7fa6d1', '#2b6cb0', '#173f6e']             # carry length 1, 2, 3, >= 4 (light -> dark)


def carry_len(n, p, K):
    """carry length of the boundary between cells n-1 and n (level K): v_p(n) + 1, the wrap n = 0 has l = K."""
    n %= p ** K
    if n == 0: return K
    l = 1
    while n % p == 0: n //= p; l += 1
    return l


def wm_table(net, L=8):
    D8, D9 = law_D(net, L, L), law_D(net, L + 1, L)
    assert (D8 == D9).all(), 'law depends on K'                                  # level invariance (Prop. law), CHECK
    Cl = [[list(map(int, r)) for r in Cc] for Cc in net['C']]
    Dw = wbuild.direct_law(Cl, net['q'], L, 1)                                    # builder's own direct law
    assert all(Dw[src][l] == (D8[l, 0, 0, src], D8[l, 0, 1, src]) for src in (0, 1) for l in range(1, L + 1))
    return D8[:, 0]                                                               # [l, c, c']


def fig_hierarchy():
    p, K = 7, 3; g = p ** K; net = mats_wf(p, Dfor(p)); D = wm_table(net, 8)
    x0, y0, W, H = 40, 100, 14, 10
    cells = np.array([(x0 + u, y0 + v) for u in range(W) for v in range(H)])
    X, sc = points_cells(net, K, cells); ideal, A = cellview(X, sc, g, 1, p)
    Rd = {tuple(c): tuple(np.rint((ideal[k] - np.floor(ideal[k])) * p).astype(int)) for k, c in enumerate(cells)}
    seen = {}
    for u in range(W - 1):                                                        # every x-step in the window
        l = carry_len(x0 + u + 1, p, K)
        for v in range(H):
            dl = tuple((np.array(Rd[(x0 + u + 1, y0 + v)]) - Rd[(x0 + u, y0 + v)]) % p)
            assert dl == (D[l, 0, 0], D[l, 1, 0]), (u, v, l, dl)                  # the jump depends only on l
            seen[l] = dl
    fig = plt.figure(figsize=(WIDTH, 3.0))
    gs = fig.add_gridspec(1, 2, width_ratios=[3.25, 1.0], wspace=0.06, left=0.01, right=0.99, top=0.86, bottom=0.13)
    ax = fig.add_subplot(gs[0])
    segs, cols, lws = [], [], []
    for n in range(x0, x0 + W + 1):
        l = carry_len(n, p, K); segs.append([(n, y0), (n, y0 + H)]); cols.append(RAMP[min(l, 4) - 1])
        lws.append(0.4 + 0.55 * (l - 1))
    for n in range(y0, y0 + H + 1):
        segs.append([(x0, n), (x0 + W, n)]); cols.append(GRID); lws.append(0.35)
    ax.add_collection(LineCollection(segs, colors=cols, linewidths=lws, zorder=1))
    draw_points(ax, ideal, A, s_lat=20, s_pt=6)
    look = {tuple(c): ideal[k] for k, c in enumerate(cells)}
    vr = y0 + 4                                                                   # one row of x-step arrows
    for u in range(W - 1):
        l = carry_len(x0 + u + 1, p, K); a = look[(x0 + u, vr)]; b = look[(x0 + u + 1, vr)]
        arrow(ax, a, b - a, col='#173f6e' if l > 1 else LATE, lw=1.5 if l > 1 else 0.7, ms=7 if l > 1 else 6)
        if l > 1:                       # ghost: where a carry-free step D(1) would have put the lattice image
            r = np.array(Rd[(x0 + u, vr)]); gh = np.array([x0 + u + 1, vr]) + ((r + [D[1, 0, 0], D[1, 1, 0]]) % p) / p
            ax.scatter(*gh, s=20, facecolors='none', edgecolors=ACC2, lw=0.7, ls=(0, (1.5, 1)), zorder=6)
            arrow(ax, gh, b - gh, col=ACC2, lw=0.7, ms=4.5, z=7)
    for n_b, tx, ty, ha in ((44, 44.5, vr - 1.5, 'center'), (42, 41.85, vr + 2.45, 'right'), (49, 49.15, vr + 2.45, 'left')):
        l = carry_len(n_b, p, K); o, xx = seen[l]
        label(ax, tx, ty, rf'$D({l})=({o},{xx})$', fs=6.6, ha=ha, col=RAMP[min(l, 4) - 1] if l > 1 else INK)
    for n_b, txt in ((42, r'$n_0=42=6\cdot7$: depth 2'), (49, r'$n_0=49=7^2$: depth 3')):
        ax.text(n_b, y0 + H + 0.12, txt, fontsize=6.2, ha='center', va='bottom', color=RAMP[carry_len(n_b, p, K) - 1])
    clean(ax, ((x0, x0 + W), (y0, y0 + H + 0.75)))
    for sp in ax.spines.values(): sp.set_visible(False)
    ax.set_title(r'(a) W$^-$, $p=7$, $P_6$: cells $n_0\in[40,54)$, $n_1\in[100,110)$ of $343\times343$;'
                 '\n' + r'every $x$-step changes $(r_0,r_1)$ by the column $D(l)$ of its boundary depth $l$', pad=3)
    # (b) the responses l = 1..8 (the running example's table)
    ax = fig.add_subplot(gs[1]); ax.axis('off'); ax.set_xlim(0, 5); ax.set_ylim(-9.6, 1.2)
    hdr = [r'$l$', r'$O_0^{(l)}$', r'$X_{1\leftarrow0}^{(l)}$', r'$O_1^{(l)}$', r'$X_{0\leftarrow1}^{(l)}$']
    for k, h in enumerate(hdr): ax.text(0.5 + k, 0.2, h, ha='center', va='center', fontsize=6.8)
    ax.plot([0.05, 4.95], [-0.35, -0.35], color=INK, lw=0.5)
    for l in range(1, 9):
        row = [l, D[l, 0, 0], D[l, 1, 0], D[l, 1, 1], D[l, 0, 1]]
        for k, v in enumerate(row):
            col = (RAMP[min(l, 4) - 1] if l > 1 else INK) if k in (1, 2) and l <= 3 else INK
            ax.text(0.5 + k, -l + 0.1, str(v), ha='center', va='center', fontsize=6.8, color=col)
    ax.text(2.5, -9.15, r'residues mod $7$ ($4=\frac{1}{2}$)', ha='center', va='center', fontsize=6.0, color=LATE)
    ax.set_title('(b) carry responses\n(the same at every level $K$)', pad=3)
    fig.legend(handles=legend_handles(['lat', 'pt', 'jit']) +
               [Line2D([], [], color=RAMP[l - 1], lw=0.4 + 0.55 * (l - 1) + 0.3, label=f'depth $l={l}$') for l in (1, 2, 3)] +
               [Line2D([], [], ls='none', marker='o', ms=4.2, mfc='none', mec=ACC2, mew=0.7, label='image if carry-free')],
               loc='lower center', ncol=7, frameon=False, bbox_to_anchor=(0.5, 0.0), handlelength=1.8, columnspacing=1.2)
    save(fig, 'fig_hierarchy')
    return dict(table={l: tuple(int(v) for v in (D[l, 0, 0], D[l, 1, 0], D[l, 1, 1], D[l, 0, 1])) for l in range(1, 9)},
                jumps_seen={l: tuple(map(int, v)) for l, v in seen.items()})

# ------------------------------------------------------------------ F11: the covering condition and the steering (Theorem GA)
# ------------------------------------------------------------------ F8 (revision 2, D4): Theorem L_3 -- lattice, wrap and sweep, slab
# ------------------------------------------------------------------ F13: finite carry patterns -- lacunary roots, octave shift, toy automaton
def series_faure_u(p, n):
    """local root u of the 2D Faure frame: u + u^2 = x (coefficients mod p)."""
    u = [0] * n
    for k in range(1, n):
        u[k] = ((1 if k == 1 else 0) - sum(u[i] * u[k - i] for i in range(1, k))) % p
    return u


def series_kummer3_tauinv(n):
    """tau^{-1} over F_3 with tau^2 = 1 + x, by coefficient recurrence of t^2 (1 + x) = 1 (no product formula)."""
    t = [1] + [0] * (n - 1)
    for k in range(1, n):
        rest = sum(t[i] * t[k - i] for i in range(1, k)) + sum(t[i] * t[k - 1 - i] for i in range(0, k))
        t[k] = (-rest * 2) % 3                                    # 1/2 = 2 in F_3
    return t


def b2_big(K, j):
    """B2 generator columns (b2core closed form) with enough precision for level K, j digits; law via b2core.law."""
    nt = 2 * K + j + 8; ncol = 2 * K
    u = 0; k = 1
    while k < nt: u |= 1 << k; k *= 2
    g0 = b2core.mul(1 | 2, 1 ^ u, nt); g1 = u >> 1
    def cols(g, t):
        out = []; q = g
        for _ in range(ncol): out.append(q); q = b2core.mul(q, t, nt)
        return out
    C = [cols(g0, u), cols(g1, 1 ^ u)]
    m200 = (1 << 200) - 1
    assert all((C[c][k] & m200) == b2core.B2[c][k] for c in (0, 1) for k in range(min(ncol, 180)))
    return b2core.law(C, K, j)[0]


def fig_automaton():
    from matplotlib.colors import ListedColormap
    Nn = 81
    uF = series_faure_u(7, Nn)
    ub = [1 if n >= 1 and (n & (n - 1)) == 0 else 0 for n in range(Nn)]
    tk = series_kummer3_tauinv(Nn)
    dig3 = lambda n: [] if n == 0 else dig3(n // 3) + [n % 3]
    assert all(tk[n] == (1 if 2 not in dig3(n) else 0) for n in range(Nn))         # = prod (1 + x^{3^i})
    cat = [1, 1, 2, 5, 14, 42, 132, 429, 1430]                                     # u_n = (-1)^{n-1} Cat_{n-1}
    assert all(uF[n] == ((-1) ** (n - 1) * cat[n - 1]) % 7 for n in range(1, 10))
    fig = plt.figure(figsize=(WIDTH, 3.2))
    gs = fig.add_gridspec(2, 2, height_ratios=[0.85, 1.25], width_ratios=[2.05, 1.0], hspace=0.62, wspace=0.12,
                          left=0.14, right=0.99, top=0.92, bottom=0.12)
    ax = fig.add_subplot(gs[0, :])
    rows = [(uF, 7, r'Faure $u$, $\mathbb{F}_7$'), (ub, 2, r'B2: $\sum x^{2^k}$, $\mathbb{F}_2$'),
            (tk, 3, r'Kummer $\tau^{-1}$, $\mathbb{F}_3$')]
    for r_, (ser, q, nm) in enumerate(rows):
        for n, v in enumerate(ser):
            if v: ax.add_patch(Rectangle((n, -r_ - 0.4), 0.92, 0.8, fc=ACC if q != 7 else plt.cm.Blues(0.35 + 0.1 * v),
                                         ec='none'))
            else: ax.add_patch(Rectangle((n, -r_ - 0.4), 0.92, 0.8, fc='#f2f2f2', ec='none'))
        nz = sum(1 for v in ser if v) / len(ser)
        ax.text(-1.2, -r_, nm, ha='right', va='center', fontsize=6.6)
        ax.text(Nn + 0.8, -r_, f'{100 * nz:.0f}%', ha='left', va='center', fontsize=6.0, color=LATE)
    ax.set_xlim(-0.3, Nn + 4); ax.set_ylim(-2.6, 0.6); ax.set_yticks([])
    ax.set_xticks([0, 1, 2, 4, 8, 16, 27, 32, 64, 80]); ax.tick_params(axis='x', labelsize=5.6)
    for sp in ('top', 'right', 'left'): ax.spines[sp].set_visible(False)
    ax.set_title(r'(a) coefficients $[x^n]$ of the local roots, $n=0,\dots,80$ (blank $=0$; right: share of nonzero): '
                 'irregular vs lacunary', pad=3)
    # (b) octave shift (Lemma octave): the type of l = parity + bits floor(log2 n) mod 2 on [l, l+j], j = 12
    ax = fig.add_subplot(gs[1, 0]); j = 12; Lmax = 270
    for k in range(0, 9):
        a0, a1 = 2 ** k, min(2 ** (k + 1), Lmax)
        if a0 < Lmax: ax.add_patch(Rectangle((a0, 0), a1 - a0, 1, fc='#dde6f2' if k % 2 else '#f4f4f4', ec='none'))
    for k in range(1, 9):
        ax.plot([2 ** k] * 2, [0, 1], color=LATE, lw=0.4)
        if 2 ** k >= 16: ax.text(2 ** k, 1.06, f'${2 ** k}$', fontsize=5.6, ha='center', va='bottom', color=LATE)
    Dbig = b2_big(270, j)
    tup = lambda l: tuple(tuple(Dbig(c, s, l)) for c in (0, 1) for s in (0, 1))
    pairs = [(250, 250 - 3 * 64, 'crossing $2^8$'), (150, 40, 'inside one octave')]
    for yy, (l, l2, txt) in zip((-0.55, -1.45), pairs):
        assert l % 2 == l2 % 2 and tup(l) == tup(l2), (l, l2)                     # same type -> same responses (CHECK)
        for x_ in (l, l2):
            ax.add_patch(Rectangle((x_, yy - 0.18), j, 0.36, fc=ACC, alpha=0.85, ec='none'))
        ax.annotate('', xy=(l2 + j / 2, yy + 0.22), xytext=(l + j / 2, yy + 0.22),
                    arrowprops=dict(arrowstyle='-|>', color=INK, lw=0.6, mutation_scale=5, connectionstyle='arc3,rad=0.12'))
        ax.text(l2 + j + 4, yy, rf'$[{l2},{l2 + j}]$', fontsize=6.0, va='center')
        if l > 200: ax.text(l - 4, yy, rf'{txt}: $[{l},{l + j}]$', fontsize=6.0, va='center', ha='right')
        else: ax.text(l + j + 4, yy, rf'$[{l},{l + j}]$: {txt}', fontsize=6.0, va='center')
        for x_ in (l, l2): ax.plot([x_, x_], [yy - 0.18, 0], color=ACC, lw=0.4, ls=(0, (1, 1)))
    ax.set_xlim(0, Lmax); ax.set_ylim(-1.9, 1.35); ax.set_yticks([])
    ax.set_xticks([1, 64, 128, 192, 256]); ax.set_xlabel(r'carry length $l$ (bands: octaves $[2^k,2^{k+1})$)', labelpad=1)
    for sp in ('top', 'right', 'left'): ax.spines[sp].set_visible(False)
    ax.set_title(r'(b) B2, octave shift: windows $[l,l+12]$ of the same type have the same $D_i(l)$', pad=3)
    # (c) the toy automaton (schematic): coefficient of x^n in tau^{-1} over F_3, reading the base-3 digits of n
    ax = fig.add_subplot(gs[1, 1]); ax.set_xlim(-1.5, 1.6); ax.set_ylim(-1.2, 1.2); ax.set_aspect('equal'); ax.axis('off')
    for (x_, nm, val) in ((-0.75, 'alive', '1'), (0.85, 'dead', '0')):
        ax.add_patch(plt.Circle((x_, 0), 0.38, fc='white', ec=ACC if nm == 'alive' else LATE, lw=1.0))
        ax.text(x_, 0.06, nm, ha='center', va='center', fontsize=6.6)
        ax.text(x_, -0.16, f'output {val}', ha='center', va='center', fontsize=5.4, color=LATE)
    ax.annotate('', xy=(0.45, 0.0), xytext=(-0.35, 0.0), arrowprops=dict(arrowstyle='-|>', color=INK, lw=0.7, mutation_scale=6))
    ax.text(0.05, 0.1, 'digit 2', ha='center', va='bottom', fontsize=6.0)
    for x_, txt in ((-0.75, 'digits 0, 1'), (0.85, 'digits 0, 1, 2')):
        ax.add_patch(matplotlib.patches.Arc((x_, 0.5), 0.42, 0.42, theta1=-40, theta2=220, color=INK, lw=0.7))
        ax.annotate('', xy=(x_ + 0.165, 0.37), xytext=(x_ + 0.19, 0.42), arrowprops=dict(arrowstyle='-|>', color=INK, lw=0.6, mutation_scale=5))
        ax.text(x_, 0.78, txt, ha='center', va='bottom', fontsize=6.0)
    ax.annotate('', xy=(-1.13, 0.0), xytext=(-1.45, 0.0), arrowprops=dict(arrowstyle='-|>', color=INK, lw=0.7, mutation_scale=6))
    ax.text(0.05, -0.75, r'e.g. $4=11_3\mapsto1$, $5=12_3\mapsto0$', ha='center', va='center', fontsize=6.0)
    ax.set_title('(c) schematic: two-state automaton\nfor $[x^n]\\,\\tau^{-1}$ over $\\mathbb{F}_3$', pad=3)
    save(fig, 'fig_automaton')
    return dict(nonzero_share={nm: round(sum(1 for v in s_ if v) / len(s_), 3) for s_, _, nm in rows},
                octave_pairs=[(l, l2) for l, l2, _ in pairs])

# ------------------------------------------------------------------ F14: the direction count, 2D vs 3D (schematic, exact small cases)
# ------------------------------------------------------------------ F15: the evidence curve for Section 1 (compact c vs N)
# ------------------------------------------------------------------ F16: fig_B2 (Section 6) -- XOR staggering in base 2 (D9)
def fig_B2():
    from matplotlib.colors import ListedColormap
    K = 6; g = 1 << K; net = mats_b2(); X, sc = points_int(net, 2 * K)
    c, i, j = sep(X, sc, g=g)
    ideal, A = cellview(X, sc, g, 2, 2)
    jd, KL, L = 12, 70, 64
    Dl, _ = b2core.law(b2core.B2, KL, jd)
    m0, m1 = ''.join(map(str, Dl(0, 0, 1))), ''.join(map(str, Dl(1, 0, 1)))
    assert (m0, m1) == ('111110011000', '101000100000')                       # binding case: x-step, l = 1
    fig = plt.figure(figsize=(WIDTH, 2.95))
    gs = fig.add_gridspec(1, 3, width_ratios=[1.0, 1.15, 0.95], wspace=0.5, left=0.035, right=0.985, top=0.86,
                          bottom=0.2)
    ax = fig.add_subplot(gs[0])
    a, b = pair_images(A, i, j, g); W = 12
    na, nb = np.floor(a).astype(int), np.floor(b).astype(int)
    assert nb[1] == na[1] and abs(nb[0] - na[0]) == 1                           # the closest pair is an x-step ...
    nx = int(max(na[0], nb[0]) % g); lx = (nx & -nx).bit_length(); assert lx == 1   # ... across l = 1
    x0 = int(np.floor((a[0] + b[0]) / 2)) - W // 2; y0 = int(np.floor((a[1] + b[1]) / 2)) - W // 2
    ramp = ['#d0d0d0', '#a9c3e0', '#7fa6d1', '#4f84bf', '#2b6cb0', '#173f6e']
    carry = lambda n: K if n % g == 0 else (int(n % g) & -int(n % g)).bit_length()
    segs, cols, lws = [], [], []
    for n in range(x0, x0 + W + 1):
        l = carry(n); segs.append([(n, y0), (n, y0 + W)]); cols.append(ramp[l - 1]); lws.append(0.35 + 0.3 * (l - 1))
    for n in range(y0, y0 + W + 1):
        l = carry(n); segs.append([(x0, n), (x0 + W, n)]); cols.append(ramp[l - 1]); lws.append(0.35 + 0.3 * (l - 1))
    ax.add_collection(LineCollection(segs, colors=cols, linewidths=lws, zorder=1))
    I, P = window_pts(ideal, A, x0, y0, W, W, g)
    draw_points(ax, I, P, s_lat=16, s_pt=5)
    mark_pair(ax, (a, b), 0.36)
    label(ax, (a[0] + b[0]) / 2, max(a[1], b[1]) + 1.7, r'staggered pair ($x$-step, $l=1$)', fs=6.0)
    clean(ax, ((x0, x0 + W), (y0, y0 + W)))
    ax.set_title(rf'(a) B2, $P_{{12}}$: ${W}\times{W}$ of $64^2$ cells' + '\n' + rf'$c(P_{{12}}) = {fmtc(c)}$', pad=3)
    hand = [Line2D([], [], color=ramp[l - 1], lw=0.35 + 0.3 * (l - 1) + 0.4, label=f'$l={l}$') for l in (1, 2, 3, 4)]
    ax.legend(handles=hand, loc='upper center', bbox_to_anchor=(0.5, -0.01), ncol=4, frameon=False, fontsize=6.2,
              handlelength=1.3, columnspacing=0.8, handletextpad=0.3, title='boundary: carry length', title_fontsize=6.2)
    # (b) the XOR masks D_i(l), first 6 digit rows, with the type strips (parity of l, octave parity) on top
    js = 6
    entries = [(0, 0, '$x$-step\nown'), (1, 0, '$x$-step\ncross'), (0, 1, '$y$-step\ncross'), (1, 1, '$y$-step\nown')]
    gap = 2; ras = np.full((4 * (js + gap) - gap + 4, L), np.nan)
    ras[0, :] = [(l % 2) for l in range(1, L + 1)]                              # parity strip
    ras[1, :] = [(int(math.log2(l)) % 2) for l in range(1, L + 1)]              # octave strip b(l)
    off = 4
    for e, (cc, src, _) in enumerate(entries):
        for l in range(1, L + 1): ras[off + e * (js + gap):off + e * (js + gap) + js, l - 1] = Dl(cc, src, l)[:js]
    ax = fig.add_subplot(gs[1])
    show = np.where(np.isnan(ras), 0.5, ras)
    rgb = np.ones(ras.shape + (3,))
    for rr in range(ras.shape[0]):
        for cc_ in range(L):
            v = ras[rr, cc_]
            if np.isnan(v): continue
            if rr < 2: rgb[rr, cc_] = matplotlib.colors.to_rgb('#2b6cb0' if v else '#dde6f2')
            else: rgb[rr, cc_] = matplotlib.colors.to_rgb(INK if v else '#f2f2f2')
    ax.imshow(rgb, aspect='auto', interpolation='nearest', extent=(0.5, L + 0.5, ras.shape[0] - 0.5, -0.5))
    for pw in (2, 4, 8, 16, 32, 64): ax.axvline(pw + 0.5, color=ACC, lw=0.5, ls=DASH)
    ax.add_patch(Rectangle((0.5, off - 0.5), 1, js, fc='none', ec=ACC2, lw=1.0, zorder=5))
    ax.add_patch(Rectangle((0.5, off + js + gap - 0.5), 1, js, fc='none', ec=ACC2, lw=1.0, zorder=5))
    yt = [0, 1] + [off + e * (js + gap) + k for e in range(4) for k in range(js)]
    ylab = [r'$l$ odd', r'$\lfloor\log_2 l\rfloor$ odd'] + \
           [(f'{nm.replace(chr(10), " ")}  ' if k == 0 else '') + r'$2^{-%d}$' % (k + 1) for (_, _, nm) in entries for k in range(js)]
    ax.set_yticks(yt); ax.set_yticklabels(ylab, fontsize=4.6)
    ax.set_xticks([1, 8, 16, 32, 48, 64]); ax.set_xlabel(r'carry length $l$ (dashed: $l = 2^k$)', labelpad=1)
    ax.text(0.5, -0.17, rf'boxed ($x$-step, $l=1$, binding): $\sigma_0={m0}$, $\sigma_1={m1}$', fontsize=5.6,
            color=ACC2, va='top', ha='center', transform=ax.transAxes)
    ax.set_title(r'(b) XOR masks $D_i(l)$, first $6$ digits (weights' + '\n' + r'$2^{-1},\dots,2^{-6}$ of a cell); top: type of $l$', pad=3)
    # (c) worst-case neighbour distance per carry length (as fig_dislocations (c))
    def fval(e, Dm):
        msk = int(''.join(map(str, Dm)), 2); R = np.arange(1 << jd)
        return max(0, np.abs(e * (1 << jd) + (R ^ msk) - R).min() - 1) / (1 << jd)
    lbx = [math.hypot(fval(1, Dl(0, 0, l)), fval(0, Dl(1, 0, l))) for l in range(1, L + 1)]
    lby = [math.hypot(fval(0, Dl(0, 1, l)), fval(1, Dl(1, 1, l))) for l in range(1, L + 1)]
    ax = fig.add_subplot(gs[2]); ll = np.arange(1, L + 1)
    ax.step(ll, lbx, where='mid', color=ACC, lw=1.0, label=r'$x$-step')
    ax.step(ll, lby, where='mid', color=INK, lw=0.8, ls=DASH, label=r'$y$-step')
    ax.axhline(min(lbx + lby), color=LATE, lw=0.5)
    ax.text(L, min(lbx + lby) - 0.012, rf'min ${min(lbx + lby):.4f}$ ($x$-step, $l=1$)', ha='right', va='top',
            fontsize=6.0, color=LATE)
    assert int(np.argmin(lbx + lby)) == 0
    ax.set_ylim(0.3, 1.16); ax.set_xlim(0.5, L + 0.5); ax.set_xticks([1, 16, 32, 48, 64])
    ax.set_xlabel(r'carry length $l$', labelpad=1); ax.set_ylabel('guaranteed distance (cells)', labelpad=1)
    ax.set_title('(c) neighbour across a boundary\nof carry length $l$ (axis steps)', pad=3)
    ax.legend(frameon=False, loc='upper center', ncol=2, fontsize=6.3, handlelength=1.6, borderaxespad=0.1)
    for sp in ('top', 'right'): ax.spines[sp].set_visible(False)
    save(fig, 'fig_B2')
    return dict(c=c, pair_cells=(na.tolist(), nb.tolist()), masks=(m0, m1), min_axis=min(lbx + lby))

# ------------------------------------------------------------------ main
FIGS = dict(F2=fig2, F5=fig5, cert=fig_cert, hier=fig_hierarchy, auto=fig_automaton, B2=fig_B2)
