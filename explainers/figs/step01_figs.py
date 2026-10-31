"""step01_figs.py -- the two figures of step 1 from step01_data.json (run step01_data.cjs first).
step01_holes_clumps.png: 125 random points vs the first 125 points of a residue sequence, with the closest pair
and the largest empty circle (found on a 400x400 grid of candidate centres, so approximate) marked.
step01_sep_vs_N.png: sep(P_[N]) = delta * sqrt(N) of the first N points, for every N, four sequences."""
import json, numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
D = json.load(open('step01_data.json'))
plt.rcParams.update({'font.size': 13, 'font.family': 'DejaVu Sans'})
INK, MUTED, RED, BLUE = '#15191f', '#7a8494', '#c0392b', '#2b6cb0'

def tdist(a, b):
    d = np.abs(a - b); d = np.minimum(d, 1 - d); return np.sqrt((d ** 2).sum(-1))

def panel(ax, key, N, title):
    P = np.array(D[key]['pts']).T[:N]
    ax.scatter(P[:, 0], P[:, 1], s=14, color=INK, zorder=3)
    # closest pair (toroidal)
    dd = tdist(P[:, None, :], P[None, :, :]); np.fill_diagonal(dd, 9); i, j = np.unravel_index(dd.argmin(), dd.shape)
    m = (P[i] + P[j]) / 2
    ax.add_patch(plt.Circle(m, max(dd[i, j], 0.012) * 1.6, fill=False, color=RED, lw=2.2, zorder=4))
    # largest empty circle (Euclidean, centres in the square)
    g = (np.arange(400) + 0.5) / 400; G = np.stack(np.meshgrid(g, g), -1).reshape(-1, 2)
    nd = np.sqrt(((G[:, None, :] - P[None, :, :]) ** 2).sum(-1)).min(1); k = nd.argmax()
    ax.add_patch(plt.Circle(G[k], nd[k], fill=True, color=BLUE, alpha=0.18, zorder=1))
    ax.add_patch(plt.Circle(G[k], nd[k], fill=False, color=BLUE, lw=1.5, zorder=2))
    ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.set_aspect('equal'); ax.set_xticks([]); ax.set_yticks([])
    ax.set_title(title, fontsize=14)
    s = dd[i, j] * np.sqrt(N); h = nd[k] * np.sqrt(N)
    ax.text(0.5, -0.08, f'closest pair {s:.2f}   biggest hole {h:.2f}\n(in units of 1/√N)', transform=ax.transAxes,
            ha='center', va='top', fontsize=11.5, color=INK)

fig, axs = plt.subplots(1, 2, figsize=(9, 5.4))
panel(axs[0], 'rand', 125, '125 random points')
panel(axs[1], 'res5', 125, '125 points of a residue sequence')
fig.text(0.5, 0.965, 'red: the two closest points   ·   blue: the largest empty disc', ha='center', fontsize=12, color=MUTED)
fig.tight_layout(rect=(0, 0.06, 1, 0.94)); fig.savefig('step01_holes_clumps.png', dpi=160); plt.close(fig)

fig, ax = plt.subplots(figsize=(9, 5.6))
lab = {'rand': ('random', MUTED), 'sobol': ("Sobol' (2D)", '#8e44ad'), 'faure5': ('Faure, base 5', RED), 'res5': ('residue sequence, base 5', BLUE)}
for key in ['rand', 'sobol', 'faure5', 'res5']:
    ax.plot(D[key]['Ns'], D[key]['seps'], color=lab[key][1], lw=2.2, label=lab[key][0])
ax.set_xscale('log'); ax.set_yscale('log'); ax.set_ylim(5e-4, 2)
ax.axhline(1, color=MUTED, lw=1, ls=':'); ax.text(2.2, 1.08, 'square grid = 1', color=MUTED, fontsize=11)
ax.axhline(1 / np.sqrt(5), color=BLUE, lw=1, ls='--')
ax.text(1.2e3, 1.3e-3, 'dashed: guaranteed for the residue\nsequence at N = 5, 125, 3125, 78125, …', color=BLUE, fontsize=10.5,
        bbox=dict(facecolor='white', edgecolor='none', alpha=0.9))
ax.annotate('Faure: points #1 and #3120\nalmost touch', xy=(3125, 0.074), xytext=(250, 0.012), fontsize=11, color=RED,
            arrowprops=dict(arrowstyle='->', color=RED))
ax.set_xlabel('number of points N'); ax.set_ylabel('closest distance × √N')
ax.set_title('Closest pair among the first N points, for every N', fontsize=14)
ax.legend(loc='lower left', fontsize=11, frameon=False)
fig.tight_layout(); fig.savefig('step01_sep_vs_N.png', dpi=160); plt.close(fig)
