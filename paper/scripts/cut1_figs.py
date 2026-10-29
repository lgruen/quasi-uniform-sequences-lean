"""cut1_figs.py -- Figures fig:principles (fig_halfcell_v4) and fig:cost (fig_volume_v4) of Appendix
app:LFdata.

    PY scripts/cut1_figs.py [--out DIR]         (from paper/; < 5 s)

Runs the builders of make_figs_v3.py unchanged (through interception of `save`, with the relabelling of b5_figs.py)
and keeps only the panels that do not show ordered window systems:
  fig_halfcell_v4  = panel (b) of fig_principles (the one-digit gap curves, Lemma lem:antipode)
  fig_volume_v4    = panels (a), (b) of fig_cost (the volume bound, Lemma lem:volume, s = 2, p = 7)
(the ordered window system p = 31 of the discarded panels is read from data/pp_s3_p31.cfg). Output: <name>.pdf/.png.
"""
import os, sys, time
import _paths
import b5_figs  # provides relabel()
import make_figs_v3 as V

orig = V.save


def save_cut(fig, name):
    b5_figs.relabel(fig)
    axes = fig.get_axes()
    if name == 'fig_principles':
        for ax in axes[:2]:
            fig.delaxes(ax)
        ax = axes[2]
        fig.set_size_inches(3.0, 2.55)
        ax.set_position([0.15, 0.15, 0.82, 0.62])
        t = ax.get_title().replace('(b) ', '')
        ax.set_title(t, pad=2)
        orig(fig, 'fig_halfcell_v4')
    elif name == 'fig_cost':
        fig.delaxes(axes[2])
        fig.set_size_inches(4.2, 2.45)
        axes[0].set_position([0.07, 0.1, 0.44, 0.7])
        axes[1].set_position([0.55, 0.1, 0.44, 0.7])
        orig(fig, 'fig_volume_v4')


V.save = save_cut
for key in ('principles', 'cost'):
    t = time.time()
    getattr(V, 'fig_' + key)()
    print(f'{key}: {time.time() - t:.1f}s', flush=True)
