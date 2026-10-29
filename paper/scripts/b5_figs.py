"""b5_figs.py -- Figure fig:HB (Section sec:antipode) and Figure fig:bsgeom of
Appendix app:LFdata (fig_bs_slab_v4, fig_bs_3d_v4: the staggered window system), with the wording of the paper.

    PY scripts/b5_figs.py [--out DIR] HB        (from paper/; < 5 s)
    PY scripts/b5_figs.py [--out DIR] bs        (< 10 s; needs bin/mdist)

Runs the builders unchanged (real generator matrices and real window systems):
  HB          make_figs.fig5              (hexagonal brick wall of Theorem thm:HB, p = 401; exact sep of P_2)
  bs          make_figs_v3._restyle_child (staggered window system p = 101: slabs, 3D links; generator matrices
              data/bs3_p101.txt; exact nearest neighbours by mdist.cpp)
Only the embedded text is renamed ("grid position" -> "lattice image", "design" -> "window system", c(P) -> sep(P),
"slip (offset wraps)" -> "slip plane"). Output: <name>_v4.pdf/.png. The keys principles, cost, lex of the
development version are not used by the paper (cut1_figs.py builds the two panels that remain).
"""
import _paths
import os, sys, time, re
import matplotlib.text

RENAME = [('grid position', 'lattice image'), ('ordered design', 'ordered window system'),
          ('staggered design', 'staggered window system'), ('mixed-radix design', 'mixed-radix window system'),
          ('slip (offset wraps)', 'slip plane'), ('(b) HB, ', '(b) '), ('(c) HB, ', '(c) '),
          ('wrap-around', 'digit wrap')]
CPAT = re.compile(r'(?<![A-Za-z\\])c\((P)')


class Stop(Exception):
    pass


def relabel(fig):
    for t in fig.findobj(matplotlib.text.Text):
        s = t.get_text()
        for a, b in RENAME:
            s = s.replace(a, b)
        s = CPAT.sub(r'\\mathrm{sep}(\1', s)
        if s == 'slip':
            s = 'slip plane'
        t.set_text(s)


def patch(mod, stop_after=None):
    if getattr(mod, '_b5_patched', False):
        return
    mod._b5_patched = True
    orig = mod.save

    def save_v4(fig, name):
        relabel(fig)
        orig(fig, name + '_v4')
        print(f'  saved {name}_v4', flush=True)
        if stop_after is not None and name == stop_after:
            raise Stop
    mod.save = save_v4


def run(key):
    t = time.time()
    if key == 'HB':
        import make_figs as M
        patch(M); res = M.fig5(); print('  values:', res)
    elif key in ('principles', 'cost', 'lex'):
        import make_figs_v3 as V
        patch(V); getattr(V, 'fig_' + key)()
    elif key == 'bs':
        import make_figs_v3 as V
        patch(V, stop_after='fig_bs_3d')
        try:
            V._restyle_child()
        except Stop:
            pass
    print(f'{key}: {time.time() - t:.1f}s', flush=True)


if __name__ == '__main__':
    for k in sys.argv[1:] or ['HB']:
        run(k)
