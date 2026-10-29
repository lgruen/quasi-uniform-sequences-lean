"""b9_hammersley.py -- Figure fig:hammersley (Section sec:hammersley): separation of the Hammersley lifts
{(i/p^m, x_i)} of two-dimensional sequences against the three-dimensional nets of the companion paper, in its metric
(toroidal, delta*N^{1/3}).

    PY scripts/b9_hammersley.py [--out DIR]     (from paper/; < 5 s)

Data: data/lift_results.csv (exact toroidal separations of the lifts; the same file as archive/hammersley/, where the
programs that compute it are). Nets-paper values: Thm thm:col (exact, m = 3), Table tab:c (exact P_{2,q}, m = 6),
Thm thm:main (certified c(q), m = 3k, k >= 2), Table tab:perprime (certified, m = 3k+1 >= 10, 3k+2 >= 8).
Panels: (a) p = 5, every m <= 10: the four lifts, the nets of the companion paper, and the carry-pair upper bound of
prop:liftcarry (valid for every scrambled frame with the places 0, 1); (b) m = 6, by p; (c) the carry-pair upper bound
against m for p = 5, 7, 11, 13 (log scale), one V-shaped curve per r (best k at each m), circles = the closed form
sqrt(2+p^2) p^{-p^r/3} at m = 2p^r (r = 1; r = 2 for p = 5): the minima tend to 0. Output: fig_hammersley.pdf/.png.
"""
import _paths
import os, csv, math
import numpy as np
import make_figs_v3 as V
import matplotlib.pyplot as plt

DATA = os.path.join(_paths.DATA, 'lift_results.csv')
R = {}
for row in csv.DictReader(open(DATA)):
    if row['s'] == '2':
        R[(row['construction'], int(row['p']), int(row['m']))] = float(row['c'])

def colnet(q):                                             # thm:col (exact), gcd(q, 6) = 1
    d2 = q**4 - 2/3*q**3 - 5/3*q**2 + 2*q + 3 if q % 3 == 2 else q**4 - 4/3*q**3 + 4/3*q**2
    return math.sqrt(d2) / q**2
def cmain(q):                                              # thm:main certified c(q)
    return math.sqrt(min((1-1/q)**2, (1-2/q)**2 + (1-4/q)**2, 3*(1-3/q)**2))
EXACT6 = {5: .7322, 7: .8578, 11: .9091, 13: .9231}        # tab:c, exact c of P_{2,q}
PERPRIME = {5: {1: .6306, 2: .5098}}                       # tab:perprime, m = 1 (>= 10), 2 (>= 8) mod 3

def carry_bound(p, m, s=2, rs=range(1, 5)):               # prop:liftcarry, places 0, 1 (n = 1); best k (and r in rs)
    best = None
    for r in rs:
        P = p ** r
        for k in range(1, m):
            if k + (s - 1) * P > m: continue
            b2 = p ** (2*m/(s+1)) * (p ** (2*(k-m)) + p ** (-2*k) + (s-1) * p ** (-2*(P-1)))
            best = b2 if best is None or b2 < best else best
    return None if best is None else math.sqrt(best)

STY = {'faure': ('Faure $(I,\\mathrm{P})$', V.SOB, 'x'), 'bw': ('brick wall', V.ACC2, 'o'),
       'res': ('residue $\\mathcal{R}_v$', V.ACC, 's'), 'blk': ('block-periodic', V.INK, '^')}
fig, axs = plt.subplots(1, 3, figsize=(V.WIDTH, 1.85))
fig.subplots_adjust(left=0.065, right=0.985, top=0.86, bottom=0.2, wspace=0.32)

# (a) p = 5 against m
ax = axs[0]; p = 5
for c, (lab, col, mk) in STY.items():
    ms = sorted(m for (cc, pp, m) in R if cc == c and pp == p)
    ax.plot(ms, [R[(c, p, m)] for m in ms], color=col, lw=0.8, marker=mk, ms=2.6, mfc='white' if mk != 'x' else col, mew=0.6, label=lab)
geo = [(3, colnet(5)), (6, EXACT6[5])]
ax.plot(*zip(*geo), ls='none', marker='D', ms=3.2, color=V.INK, label='nets paper (exact)')
cert = [(8, PERPRIME[5][2]), (9, cmain(5)), (10, PERPRIME[5][1])]
ax.plot(*zip(*cert), ls='none', marker='D', ms=3.2, mfc='white', mec=V.INK, mew=0.7, label='nets paper (certified)')
bm = [(m, carry_bound(p, m)) for m in range(6, 12) if carry_bound(p, m) is not None and carry_bound(p, m) < 1]
ax.plot(*zip(*bm), color=V.LATE, lw=0.8, ls=V.DASH, marker='v', ms=2.6, label='carry-pair upper bound')
ax.set_xlim(1.5, 11.5); ax.set_ylim(0, 1.0); ax.set_xticks(range(2, 12))
ax.set_xlabel('$m$  ($p=5$, $N=5^m$)', labelpad=1); ax.set_ylabel(r'$\delta N^{1/3}$', labelpad=2)
ax.set_title('(a) lifts vs nets, $p=5$', pad=3)

# (b) m = 6 against p
ax = axs[1]; m = 6; ps = [5, 7, 11, 13, 17]
for c, (lab, col, mk) in STY.items():
    pp = [q for q in ps if (c, q, m) in R]
    ax.plot(pp, [R[(c, q, m)] for q in pp], color=col, lw=0.8, marker=mk, ms=2.6, mfc='white' if mk != 'x' else col, mew=0.6)
ax.plot(list(EXACT6), list(EXACT6.values()), ls='none', marker='D', ms=3.2, color=V.INK)
x = np.linspace(4.5, 18, 200); ax.plot(x, [cmain(q) for q in x], color=V.INK, lw=0.6, ls=V.DASH)
ax.text(17.6, cmain(17.6) - 0.07, r'$c(q)$', fontsize=6.5, ha='right', color=V.INK)
ax.set_xlim(4, 18); ax.set_ylim(0, 1.0); ax.set_xticks(ps)
ax.set_xlabel('prime $p$  ($m=6$)', labelpad=1); ax.set_title('(b) $m=6$: lifts vs nets', pad=3)

# (c) carry-pair upper bound against m
ax = axs[2]
for q, col in ((5, V.ACC2), (7, V.ACC), (11, V.LATE), (13, V.INK)):
    first = True
    for r in (1, 2):                                       # one V-shaped curve per carry pair (one r), best k at each m
        if 2 * q ** r > 60: continue
        ms = np.arange(6, 61); b = [carry_bound(q, int(mm), rs=(r,)) for mm in ms]
        b2 = [bb if (bb is not None and bb < 1) else np.nan for bb in b]  # shown where the bound is < 1
        ax.plot(ms, b2, color=col, lw=0.8, marker='.', ms=2.0, label=f'$p={q}$' if first else None); first = False
        ax.plot([2 * q ** r], [math.sqrt(2 + q * q) * q ** (-q ** r / 3)], ls='none', marker='o', ms=3.2, mfc='white', mec=col, mew=0.7)
ax.set_yscale('log'); ax.set_ylim(1e-6, 1.5); ax.set_xlim(5, 60)
ax.set_xlabel('$m$', labelpad=1); ax.set_ylabel(r'bound on $\delta N^{1/3}$', labelpad=1)
ax.set_title('(c) proved upper bound, places $0,1$', pad=3)
ax.legend(loc='lower left', frameon=False, handlelength=1.2, fontsize=6.2)
for a in axs:
    a.tick_params(length=2, pad=1.5)
    for sp in ('top', 'right'):
        a.spines[sp].set_visible(False)
h, l = axs[0].get_legend_handles_labels()
fig.legend(h, l, loc='upper center', ncol=7, frameon=False, fontsize=6.0, bbox_to_anchor=(0.5, 1.0), handlelength=1.4, columnspacing=0.9)
fig.subplots_adjust(top=0.82)
V.save(fig, 'fig_hammersley')
