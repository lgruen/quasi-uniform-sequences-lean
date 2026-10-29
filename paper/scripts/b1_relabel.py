"""b1_relabel.py -- Figures fig:idea (fig_idea_v4), fig:hierarchy (fig_hierarchy_v4) and fig:cert (fig_cert_v4) of
Section sec:law.

    PY scripts/b1_relabel.py [--out DIR] [F2 hier cert]     (from paper/; < 5 s; default: all three)

Runs the builders of make_figs.py (real generator matrices of the brick wall W^-) and renames the embedded text to
the wording of the paper ("grid position" -> "lattice image", "wrap-around" -> "slip plane"). Keys: F2 = fig_idea,
hier = fig_hierarchy, cert = fig_cert; output <name>_v4.pdf/.png.
"""
import _paths
import os, sys, time
import matplotlib.text
import make_figs as M

RENAME = [('grid position', 'lattice image'), ('wrap-around', 'slip plane')]
_orig_save = M.save


def save_v4(fig, name):
    for t in fig.findobj(matplotlib.text.Text):
        s = t.get_text()
        for a, b in RENAME:
            s = s.replace(a, b)
        t.set_text(s)
        if t.get_bbox_patch() is not None:       # F4: labels with a white backing above the point markers
            t.set_zorder(20)
    _orig_save(fig, name + '_v4')


M.save = save_v4
for key in sys.argv[1:] or ['F2', 'hier', 'cert']:
    t = time.time(); res = M.FIGS[key]()
    print(f'{key}: ({time.time() - t:.1f}s)', flush=True)
