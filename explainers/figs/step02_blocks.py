"""step02_blocks.py -- step02_blocks.png: the first 64 points of 2D Sobol' (identity, Pascal mod 2), in blocks of 16.
Each block alone has one point in each of the 16 cells of the 4x4 grid (it is a digital (XOR) shift of the first
block); the four blocks together fill the 8x8 grid; any N (here 40 = 16 + 16 + 8) is a stack of such blocks."""
import matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
from math import comb
plt.rcParams.update({'font.size': 13, 'font.family': 'DejaVu Sans'})
M = 6
I = [[int(n == k) for k in range(M)] for n in range(M)]
P = [[comb(k, n) % 2 for k in range(M)] for n in range(M)]
def coord(C, i):
    d = [(i >> k) & 1 for k in range(M)]
    return sum((sum(C[n][k] * d[k] for k in range(M)) % 2) / 2 ** (n + 1) for n in range(M)) + 1 / 128  # off the corners
pts = [(coord(I, i), coord(P, i)) for i in range(64)]
COL = ['#2b6cb0', '#d35400', '#27ae60', '#8e44ad']
GRID = '#9aa5b4'
def frame(ax, g, title):
    for j in range(g + 1): ax.axvline(j / g, color=GRID, lw=0.8); ax.axhline(j / g, color=GRID, lw=0.8)
    ax.set_xlim(-0.02, 1.02); ax.set_ylim(-0.02, 1.02); ax.set_aspect('equal'); ax.set_xticks([]); ax.set_yticks([])
    ax.set_title(title, fontsize=12)
fig, axs = plt.subplots(2, 3, figsize=(9.5, 7))
for b in range(4):
    ax = axs.flat[b]
    for bb in range(b):                                    # earlier blocks, faint
        ax.scatter(*zip(*pts[16 * bb:16 * bb + 16]), s=14, color=COL[bb], alpha=0.18)
    ax.scatter(*zip(*pts[16 * b:16 * b + 16]), s=30, color=COL[b], zorder=3)
    frame(ax, 4, f'points {16*b}–{16*b+15}: one per cell')
ax = axs.flat[4]
for b in range(4): ax.scatter(*zip(*pts[16 * b:16 * b + 16]), s=22, color=COL[b], zorder=3)
frame(ax, 8, 'all 64: one per cell of 8×8')
ax = axs.flat[5]
for (a, n, c) in [(0, 16, COL[0]), (16, 16, COL[1]), (32, 8, COL[2])]:
    ax.scatter(*zip(*pts[a:a + n]), s=26, color=c, zorder=3)
frame(ax, 4, 'first 40 = 16 + 16 + 8')
fig.suptitle("2D Sobol' in blocks of 16: each block is a complete net of its own", fontsize=13)
fig.text(0.5, 0.01, 'faint dots: earlier blocks. Green in the last panel: 8 points, one per cell of a 4×2 grid (a net of 8)',
         ha='center', fontsize=10, color='#7a8494')
fig.tight_layout(rect=(0, 0.03, 1, 1), h_pad=2.2); fig.savefig('step02_blocks.png', dpi=160); plt.close(fig)
