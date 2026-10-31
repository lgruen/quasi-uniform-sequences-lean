"""step01_fig_checkpoints.py -- step01_checkpoints.png from step01_checkpoints.json (step01_checkpoints.cjs) and the
explicit Faure pairs of faure_far.py (rem:faurerate). Left: separation at the checkpoints N = 5^m (Sobol': 2^m),
linear axis. Right: the Faure pairs at N = 5^5, 5^25, 5^125 against the guarantee of the residue sequence."""
import json, numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
D = json.load(open('step01_checkpoints.json'))
plt.rcParams.update({'font.size': 13, 'font.family': 'DejaVu Sans'})
INK, MUTED, RED, BLUE, PURPLE = '#15191f', '#7a8494', '#c0392b', '#2b6cb0', '#8e44ad'
G = 1 / np.sqrt(5)
fig, (ax, bx) = plt.subplots(1, 2, figsize=(11, 6), gridspec_kw={'width_ratios': [1.7, 1]})
x5 = np.arange(1, 8)
ax.plot(x5, D['rand']['sep'], '-o', color=MUTED, lw=1.5, ms=5, label='random (typical)')
ax.plot(x5, D['faure5']['sep'], '-o', color=RED, lw=2, ms=7, label='Faure, base 5')
r = np.array(D['res5']['sep'])
ax.plot(x5, r, '-', color=BLUE, lw=2, label='residue sequence, base 5')
ax.plot(x5[0::2], r[0::2], 'o', color=BLUE, ms=8)
ax.plot(x5[1::2], r[1::2], 'o', mfc='white', mec=BLUE, mew=2, ms=8)
ax.axhline(G, color=BLUE, ls='--', lw=1.2, label='residue: guaranteed ≥ 0.447 at filled dots')
for m, v in zip(x5, D['faure5']['sep']): ax.text(m + 0.13, v - 0.01, f'{v:.2f}', color=RED, ha='left', va='top', fontsize=10)
for m, v in zip(x5, r): ax.text(m - 0.13, v + 0.012, f'{v:.2f}', color=BLUE, ha='right', va='bottom', fontsize=10)
ax.set_xticks(x5); ax.set_xticklabels([f'5$^{m}$\n{5**m:,}' for m in x5], fontsize=10.5)
ax.set_yticks(np.arange(0, 1.01, 0.1)); ax.set_ylim(0, 1.02); ax.set_xlim(0.6, 7.9)
ax.grid(axis='y', color='#dde2e8', lw=0.8)
ax.set_xlabel('checkpoint N = 5$^m$'); ax.set_ylabel('closest distance × √N')
ax.set_title('Separation at the checkpoints', fontsize=14)
ax.legend(loc='upper right', fontsize=10, frameon=True, framealpha=0.95)

Q = [5, 25, 125]; L = [-1.132, -8.122, -43.070]       # log10 sep of the explicit pairs (faure_far.py)
bx.plot(range(3), L, 'o-', color=RED, ms=8, lw=2)
for i, (q, l) in enumerate(zip(Q, L)):
    bx.text(i + 0.15, l - 1, f'N = 5$^{{{q}}}$\n≈ 10$^{{{l:.0f}}}$' if i else f'N = 5$^{{5}}$ = 3125\n0.074', color=RED, fontsize=10.5)
bx.axhline(np.log10(G), color=BLUE, ls='--', lw=1.5)
bx.text(2.7, np.log10(G) + 1.0, 'residue sequence: ≥ 0.447\nat every 5$^{odd}$, forever', color=BLUE, fontsize=10.5, ha='right', va='bottom')
bx.set_xticks(range(3)); bx.set_xticklabels(['5$^5$', '5$^{25}$', '5$^{125}$'])
bx.set_yticks([0, -10, -20, -30, -40]); bx.set_yticklabels(['1', '10$^{-10}$', '10$^{-20}$', '10$^{-30}$', '10$^{-40}$'])
bx.set_ylim(-50, 9); bx.set_xlim(-0.4, 2.8); bx.grid(axis='y', color='#dde2e8', lw=0.8)
bx.set_title("Faure's close pairs never stop", fontsize=14)
bx.set_xlabel('checkpoint (log scale of N)')
fig.tight_layout(); fig.savefig('step01_checkpoints.png', dpi=160); plt.close(fig)
