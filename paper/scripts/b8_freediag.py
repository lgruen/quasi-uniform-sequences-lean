"""b8_freediag.py -- Figure fig:freediag (Section sec:block): certified LB(F) of the block-periodic designs,
thm:block(c) vs (d).

    PY scripts/b8_freediag.py [--out DIR]       (from paper/; < 5 s)

Data: data/freediag.json, computed by b8_freediag_data.py (exact one-digit relaxation by lb.cpp on the design files
data/ustar<s>.txt, asserted against the paper's closed forms and quoted values).
Drawn per s = 4..7: U*_s (grey, dashed: written proof for p >= 5a*_s+4; open squares: exact evaluations of the c.a.
range of thm:block(c)); free diagonal (blue, solid: 1-(A+1)/p from the threshold of lem:signclass on; filled dots:
exact evaluations below it; open circles: quoted small-prime values).  Vertical ticks: the two thresholds.
Output: fig_freediag.pdf/.png.
"""
import _paths
import os, sys, json
import numpy as np
import make_figs_v3 as V
import matplotlib.pyplot as plt

D = json.load(open(os.path.join(_paths.DATA, 'freediag.json')))
THR = {4: 23, 5: 67, 6: 127, 7: 587}                  # first prime past the threshold of lem:signclass
fig, axs = plt.subplots(1, 4, figsize=(V.WIDTH, 1.6), sharey=True)
fig.subplots_adjust(left=0.075, right=0.975, top=0.86, bottom=0.27, wspace=0.1)
P0, P1 = 5, 1200
for ax, s in zip(axs, (4, 5, 6, 7)):
    S = D['series'][str(s)]; a1 = D['astar'][str(s)] + 1; A1 = D['A'][str(s)] + 1
    pu = 5 * D['astar'][str(s)] + 4                       # written proof range of thm:block(c)
    x = np.geomspace(pu, P1, 200)
    if pu < P1:
        ax.plot(x, 1 - a1 / x, color=V.LATE, lw=1.0, ls=V.DASH, zorder=2)
    cu = [(p, v) for p, v in S['ustar'] if p < pu and p <= 109]
    if cu:
        ax.plot([p for p, _ in cu], [v for _, v in cu], ls='none', marker='s', ms=2.4, mfc='white', mec=V.LATE, mew=0.6, zorder=3)
    fd = D['fromD'][str(s)]
    x = np.geomspace(THR[s], P1, 200)
    ax.plot(x, 1 - A1 / x, color=V.ACC, lw=1.3, zorder=4)
    cd = [(p, v) for p, v in S['diag'] if p < THR[s] and p >= fd]
    ax.plot([p for p, _ in cd], [v for _, v in cd], ls='none', marker='o', ms=2.4, color=V.ACC, zorder=5)
    ex = [(p, v) for p, v in S['diag'] if p < fd]
    if ex:
        ax.plot([p for p, _ in ex], [v for _, v in ex], ls='none', marker='o', ms=3.0, mfc='white', mec=V.ACC, mew=0.8, zorder=5)
    for t, c in ((THR[s], V.ACC), (pu, V.LATE)):
        if t < P1:
            ax.axvline(t, color=c, lw=0.5, ls=(0, (1, 1.5)), zorder=1)
    ax.set_xscale('log'); ax.set_xlim(P0, P1); ax.set_ylim(0, 1.02)
    ax.set_xticks([10, 100, 1000]); ax.set_xticklabels(['10', '100', '1000'], fontsize=7)
    ax.tick_params(axis='y', labelsize=7); ax.tick_params(length=2, pad=1.5)
    for sp in ('top', 'right'):
        ax.spines[sp].set_visible(False)
    ax.set_title(rf'$s={s}$:  $1-{A1}/p$ vs $1-{a1}/p$', fontsize=7.5, pad=3)
    ax.set_xlabel('prime $p$', fontsize=7, labelpad=1)
axs[0].set_ylabel(r'$\mathrm{LB}(F)$', fontsize=7.5, labelpad=2)
V.save(fig, 'fig_freediag')
