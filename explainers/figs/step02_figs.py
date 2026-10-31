"""step02_figs.py -- figures of step 2 (digit reversal and boxes), pure Python.
step02_vdc.png: van der Corput in base 2, the first 2, 4, 8, 16 points, each labelled by its index.
step02_boxes.png: the first 16 points of the 2D sequence (identity, Pascal mod 2) (= Sobol' in 2D = Faure in base 2)
with the five box shapes of area 1/16: every box holds exactly one point."""
import matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
from math import comb
plt.rcParams.update({'font.size': 13, 'font.family': 'DejaVu Sans'})
INK, MUTED, RED, BLUE = '#15191f', '#7a8494', '#c0392b', '#2b6cb0'
M = 4
def digits(i, m=M): return [(i >> k) & 1 for k in range(m)]                 # index digits V_0 (least significant) ...
def point(C, i): d = digits(i); return sum((sum(C[n][k] * d[k] for k in range(M)) % 2) / 2 ** (n + 1) for n in range(M))
I = [[int(n == k) for k in range(M)] for n in range(M)]
P = [[comb(k, n) % 2 for k in range(M)] for n in range(M)]                    # Pascal mod 2: P[n][k] = binom(k, n)

fig, ax = plt.subplots(figsize=(9, 4.2))
for r, n in enumerate([2, 4, 8, 16]):
    y = 3 - r
    ax.plot([0, 1], [y, y], color=MUTED, lw=1)
    for j in range(n + 1): ax.plot([j / n] * 2, [y - 0.18, y + 0.18], color=MUTED, lw=1)
    for i in range(n):
        x = point(I, i); new = i >= n // 2
        ax.plot(x, y, 'o', color=RED if new else INK, ms=8, zorder=3)
        ax.text(x, y + 0.24, str(i), ha='center', fontsize=10, color=RED if new else INK)
    ax.text(-0.03, y, f'first {n}', ha='right', va='center', fontsize=12)
ax.set_xlim(-0.2, 1.03); ax.set_ylim(-0.5, 3.6); ax.axis('off')
ax.set_title('Digit reversal in base 2: the first 2, 4, 8, 16 points (red = the newest half)', fontsize=13)
fig.tight_layout(); fig.savefig('step02_vdc.png', dpi=160); plt.close(fig)

pts = [(point(I, i) + 1 / 32, point(P, i) + 1 / 32) for i in range(16)]   # drawn mid-way into their 1/16 strip
fig, axs = plt.subplots(2, 3, figsize=(9.5, 6.8))
for ax, d0 in zip(axs.flat, range(M + 1)):
    d1 = M - d0
    for j in range(2 ** d0 + 1): ax.axvline(j / 2 ** d0, color=BLUE, lw=0.9, alpha=0.7)
    for j in range(2 ** d1 + 1): ax.axhline(j / 2 ** d1, color=BLUE, lw=0.9, alpha=0.7)
    for i, (x, y) in enumerate(pts):
        ax.plot(x, y, 'o', color=INK, ms=5.5, zorder=3)
    ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.set_aspect('equal'); ax.set_xticks([]); ax.set_yticks([])
    ax.set_title(f"{2**d0} column{'s' if d0 else ''} × {2**d1} row{'s' if d1 else ''}", fontsize=12)
ax = axs.flat[5]
for i, (x, y) in enumerate(pts):
    ax.plot(x, y, 'o', color=INK, ms=5.5); ax.text(x + 0.015, y + 0.015, str(i), fontsize=9, color=RED)
ax.set_xlim(0, 1); ax.set_ylim(0, 1); ax.set_aspect('equal'); ax.set_xticks([]); ax.set_yticks([])
ax.set_title('the same 16 points, numbered', fontsize=12)
fig.suptitle('16 points, five box shapes of area 1/16: exactly one point per box, every time', fontsize=13)
fig.text(0.5, 0.005, 'each point is drawn 1/32 to the right and up: with 4 digits it would sit exactly on a box corner', ha='center', fontsize=10, color=MUTED)
fig.tight_layout(rect=(0, 0.025, 1, 1)); fig.savefig('step02_boxes.png', dpi=160); plt.close(fig)

