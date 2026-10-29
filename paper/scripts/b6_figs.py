"""b6_figs.py -- figures of Sections sec:frames and sec:practice.

    PY scripts/b6_figs.py [--out DIR] [evidence coverage B2 automaton]   (from paper/; default: all four; ~15 s,
                                                                         `evidence` needs bin/mdist)

  evidence  fig_evidence3d_v4 (fig:evidence): exact sep(P_[N]) for every N <= 2^23 in dimension three, p = 31: the
            residue sequence of tab:practice (generator matrices data/best_U_31.txt; places (8,0,16), theta = 9,
            v = (10,30,7)), Faure, Owen-scrambled Sobol' (precomputed drop data data/drops_fa31.txt,
            data/drops_sob{1,2,3}.txt); slabs at the N where Faure is worst.  The residue-sequence drops are computed
            here with mdist.cpp (about 10 s) and compared with data/drops_res31.txt (exit 1 if they differ).
  coverage  fig_coverage (fig:dim3): which bases are certified for which level family, s = 2..7 (thm:coverage).
  B2, automaton   fig_B2_v4 (fig:B2), fig_automaton_v4 (fig:automaton): make_figs.fig_B2, make_figs.fig_automaton with
            the embedded text renamed to the wording of the paper (c(P) -> sep(P), "type of l" -> "pattern of l",
            "windows [l, l+12]" -> "ranges").
Output: <name>.pdf/.png.
"""
import _paths
import os, sys, time, math, re, subprocess
import numpy as np
DATA = _paths.DATA
import matplotlib
matplotlib.use('agg')
import matplotlib.text
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

RENAME = [('windows $[l,l+12]$ of the same type', 'ranges $[l,l+12]$ of the same pattern'),
          ('top: type of $l$', 'top: pattern of $l$'), ('grid position', 'lattice image')]
CPAT = re.compile(r'(?<![A-Za-z\\])c\((P)')


def relabel(fig):
    for t in fig.findobj(matplotlib.text.Text):
        s = t.get_text()
        for a, b in RENAME:
            s = s.replace(a, b)
        t.set_text(CPAT.sub(r'\\mathrm{sep}(\1', s))
        if t.get_fontsize() < 5.0 and 'odd' not in s:   # F4: fig_B2 digit-row labels 4.6pt -> 5.4pt (not the two single-row strip labels)
            t.set_fontsize(5.4)


def patch(mod):
    if getattr(mod, '_b6_patched', False):
        return
    mod._b6_patched = True
    orig = mod.save

    def save_v4(fig, name):
        relabel(fig); orig(fig, name + '_v4'); print(f'  saved {name}_v4', flush=True)
    mod.save = save_v4


# ------------------------------------------------------------------ evidence
def residue_drops(p=31):
    out = os.path.join(_paths.TMP, f'drops_res{p}.txt')
    import make_figs_v3 as V
    B = V.B
    q, M = V.load_dump3(os.path.join(DATA, f'best_U_{p}.txt')); assert q == p
    Nmax = 2 ** 23
    X = B.digit_points(p, M, Nmax)
    b = os.path.join(_paths.TMP, '_pts_b6.bin'); X.tofile(b)
    subprocess.run([_paths.exe('mdist'), 'drops', b, '3', str(Nmax), out], check=True,
                   capture_output=True)
    os.remove(b)
    ref = os.path.join(DATA, f'drops_res{p}.txt')
    if open(out).read() != open(ref).read():
        sys.exit(f'drops of the residue sequence differ from data/drops_res{p}.txt')
    print(f'  drops of the residue sequence: identical to data/drops_res{p}.txt', flush=True)
    return out


def fig_evidence():
    import make_figs_v3 as V
    B = V.B; p = 31; s = 3
    LB = 2 * p ** (-1 / 3)                       # Theorem thm:residue, lambda_jit(Lambda_v) = 2 (b6_check.py)
    dd = {'res': V.drops(residue_drops(p)), 'fa': V.drops(os.path.join(DATA, 'drops_fa31.txt'))}
    for k in (1, 2, 3):
        dd[f'sob{k}'] = V.drops(os.path.join(DATA, f'drops_sob{k}.txt'))
    J = {k: V.Jmin(v) for k, v in dd.items()}
    fig = plt.figure(figsize=(V.WIDTH, 2.9))
    gs = fig.add_gridspec(2, 2, width_ratios=[2.15, 1.0], wspace=0.06, hspace=0.32, left=0.075, right=0.995, top=0.95,
                          bottom=0.27)
    ax = fig.add_subplot(gs[:, 0])
    for k in (1, 2, 3):
        x, y = V.sawtooth(dd[f'sob{k}'])
        ax.plot(x, y, color=V.SOB, lw=0.45, zorder=1, label="Owen-scrambled Sobol', 3 seeds (min %.3f to %.3f)" % (
            min(J[f'sob{q}'][0] for q in (1, 2, 3)), max(J[f'sob{q}'][0] for q in (1, 2, 3))) if k == 1 else None)
    x, y = V.sawtooth(dd['fa']); ax.plot(x, y, color=V.ACC2, lw=0.7, zorder=2, label=r'Faure $(I,P,P^2)$ (min %.3f)' % J['fa'][0])
    # CUT1 (2026-10-28): the ordered window system curve ('pp') was removed with the ordered windows.
    x, y = V.sawtooth(dd['res']); ax.plot(x, y, color=V.ACC, lw=1.1, zorder=4, label=r'residue sequence (min %.3f)' % J['res'][0])
    x2 = 2 * math.log2(p)
    ax.plot([x2 - 0.45, x2 + 0.45], [LB, LB], color=V.ACC, lw=2.4, solid_capstyle='butt', zorder=5,
            label=rf'certified: $\mathrm{{sep}}(P_{{3K-1}})\geq{math.floor(LB * 1000) / 1000:.3f}$ (every $K$)')
    ax.axhline(LB / p, color=V.ACC, lw=0.6, ls=V.DASH, zorder=3,
               label=rf'every $N$: $\mathrm{{sep}}(P_{{[N]}})\geq\mathrm{{LB}}/p={math.floor(LB / p * 1e3) / 1e3:.3f}$')
    for m in range(2, 5):
        ax.axvline(m * math.log2(p), color=V.GRID if m == 2 else V.FINE, lw=0.6, zorder=0)
        ax.text(m * math.log2(p), 1.55, rf'$p^{m}$', fontsize=6, color=V.LATE, ha='center', va='bottom')
    for k, col in (('res', V.ACC), ('fa', V.ACC2), ('sob1', V.SOB), ('sob2', V.SOB), ('sob3', V.SOB)):
        c, n = J[k]; ax.plot(math.log2(n), c, 'o', ms=3.0, mfc='white', mec=col, mew=0.8, zorder=6)
    ax.set_yscale('log'); ax.set_ylim(8e-3, 2.2); ax.set_xlim(6, 23); ax.set_xticks(range(6, 24, 2))
    ax.set_xlabel(r'$\log_2 N$', labelpad=1); ax.set_ylabel(r'$\mathrm{sep}(P_{[N]})=\delta(P_{[N]})\,N^{1/3}$', labelpad=1)
    ax.spines['right'].set_visible(False); ax.spines['top'].set_visible(False)
    h, l = ax.get_legend_handles_labels()
    fig.legend(h, l, loc='lower center', ncol=3, frameon=False, bbox_to_anchor=(0.5, 0.0), handlelength=2.0,
               columnspacing=1.0, fontsize=6.3)
    N = J['fa'][1]
    q, M = V.load_dump3(os.path.join(DATA, f'best_U_{p}.txt')); assert q == p
    Xr = B.digit_points(p, M, N); Xfa = B.faure_points(p, 3, N)
    cf, prf, axf = V.slab_at_N(fig.add_subplot(gs[0, 1]), Xfa, 'Faure')
    cr, prr, axr = V.slab_at_N(fig.add_subplot(gs[1, 1]), Xr, 'residue')
    fig.axes[-2].set_title(rf'Faure, $N={N}$: $\mathrm{{sep}}(P_{{[N]}})={cf:.3f}$', pad=2.5, fontsize=6.6)
    fig.axes[-1].set_title(rf'residue sequence, same $N$: $\mathrm{{sep}}(P_{{[N]}})={cr:.3f}$', pad=2.5, fontsize=6.6)
    assert abs(cf - J['fa'][0]) < 1e-3 and abs(cr - B.c_at(dd['res'], N)) < 1e-3, (cf, cr)
    V.save(fig, 'fig_evidence3d_v4')
    print('  J:', {k: (round(v[0], 4), int(v[1])) for k, v in J.items()}, ' N_slab', N, 'c_fa', round(cf, 4), 'c_res', round(cr, 4),
          'slab counts', V.VAL.get('slab_counts'), ' res at p^2:', round(B.c_at(dd['res'], p ** 2), 4),
          'res at p^3:', round(B.c_at(dd['res'], p ** 3), 4), 'res at 2^23:', round(B.c_at(dd['res'], 2 ** 23), 4))


# ------------------------------------------------------------------ coverage
def primes_upto(n):
    return [k for k in range(2, n + 1) if all(k % d for d in range(2, int(k ** 0.5) + 1))]


def fig_coverage():
    import make_figs_v3 as V
    P = primes_upto(113)
    bases = [2, 3, 4] + [x for x in P if x > 3]
    X = {q: i for i, q in enumerate(bases)}
    PRF, CA = V.ACC, '#9cc0e6'
    # status per (s, row, q): 'P' proof, 'C' computer-assisted; rows: 0: m = 0 mod s, 1: m = -1 mod s, 2: m = 0 mod s^2
    st = {}
    def put(s, r, qs, t):
        for q in qs:
            if (s, r, q) not in st or (st[(s, r, q)] == 'C' and t == 'P'):
                st[(s, r, q)] = t
    big = [x for x in P]
    put(2, 0, [2, 3], 'C'); put(2, 0, [x for x in big if x >= 5], 'P')
    put(2, 1, [x for x in big if x >= 5], 'P'); put(2, 2, [x for x in big if x >= 3], 'P')
    put(3, 0, [3, 4, 7], 'C'); put(3, 0, [x for x in big if x >= 11], 'P')
    put(3, 1, [x for x in big if x >= 11], 'P'); put(3, 2, [x for x in big if x >= 5], 'P')
    put(4, 0, [4], 'C'); put(4, 0, [x for x in big if x >= 17], 'P'); put(4, 1, [x for x in big if x >= 17], 'P')
    put(4, 2, [x for x in big if 7 <= x <= 109], 'C'); put(4, 2, [x for x in big if x >= 29], 'P')
    put(5, 0, [x for x in big if x >= 37], 'P'); put(5, 1, [x for x in big if x >= 37], 'P')
    put(5, 2, [x for x in big if 19 <= x <= 109], 'C'); put(5, 2, [x for x in big if x >= 89], 'P')
    put(4, 2, [x for x in big if x >= 11], 'C'); put(5, 2, [x for x in big if x >= 11], 'C')   # thm:block(d), free diagonal (c.a.)
    for s_ in (6, 7):                                   # case (e)/(f): residue sequences for p > 2^s (none up to 113 for s = 7)
        put(s_, 0, [x for x in big if x > 2 ** s_], 'P'); put(s_, 1, [x for x in big if x > 2 ** s_], 'P')
    put(6, 2, [x for x in big if x >= 17], 'C')         # thm:block(d), s = 6 (c.a.)
    put(7, 2, [x for x in big if x in (17, 19, 23) or x >= 31], 'C')   # thm:block(d), s = 7 (c.a.)
    for (s_, r_, q_), t_ in list(st.items()):          # s^2 N is contained in s N
        if r_ == 0:
            put(s_, 2, [q_], t_)
    lab = lambda s_, r_: [rf'$m\in{s_}\mathbb{{N}}$', rf'$m\in{s_}\mathbb{{N}}-1$', rf'$m\in{s_ * s_}\mathbb{{N}}$'][r_]
    from matplotlib.transforms import blended_transform_factory
    fig, ax = plt.subplots(figsize=(V.WIDTH, 2.6))
    fig.subplots_adjust(left=0.175, right=0.985, top=0.93, bottom=0.135)
    tr = blended_transform_factory(ax.transAxes, ax.transData)
    y = 0; yt, yl = [], []
    for s in (2, 3, 4, 5, 6, 7):
        for r in (0, 1, 2):
            for q in bases:
                x = X[q]
                if q < s:
                    ax.add_patch(Rectangle((x - 0.45, y - 0.4), 0.9, 0.8, fc='white', ec=V.FINE, hatch='////', lw=0.3))
                    continue
                t = st.get((s, r, q))
                ax.add_patch(Rectangle((x - 0.45, y - 0.4), 0.9, 0.8, lw=0.25, ec='white' if t else V.FINE,
                                       fc=PRF if t == 'P' else CA if t == 'C' else 'white'))
            yt.append(y); yl.append(lab(s, r)); y -= 1
        ax.text(-0.175, y + 2, rf'$s={s}$', ha='left', va='center', fontsize=7.5, transform=tr)
        y -= 0.3
    ax.set_yticks(yt); ax.set_yticklabels(yl, fontsize=5.8)
    ax.set_xticks(range(len(bases))); ax.set_xticklabels([str(q) for q in bases], fontsize=5.4, rotation=90)
    ax.set_xlim(-0.6, len(bases) - 0.4); ax.set_ylim(y + 0.2, 0.6)
    ax.tick_params(axis='y', length=0, pad=2); ax.tick_params(axis='x', length=0, pad=1.5)
    for sp in ax.spines.values(): sp.set_visible(False)
    ax.set_xlabel(r'base $q$ (all primes up to $113$, and $q=4$); larger primes: see the caption', labelpad=2)
    h = [Rectangle((0, 0), 1, 1, fc=PRF), Rectangle((0, 0), 1, 1, fc=CA),
         Rectangle((0, 0), 1, 1, fc='white', ec=V.FINE, lw=0.5),
         Rectangle((0, 0), 1, 1, fc='white', ec=V.FINE, hatch='////', lw=0.3)]
    fig.legend(h, ['written proof', 'computer-assisted', 'no certified bound', r'$q<s$: no $(0,s)$-sequence'],
               loc='upper center', ncol=4, frameon=False, bbox_to_anchor=(0.56, 1.0), fontsize=6.4, handlelength=1.2)
    V.save(fig, 'fig_coverage')


def run(key):
    t = time.time()
    if key == 'evidence':
        fig_evidence()
    elif key == 'coverage':
        fig_coverage()
    elif key in ('B2', 'automaton'):
        import make_figs as M
        patch(M); getattr(M, 'fig_' + key)()
    print(f'{key}: {time.time() - t:.1f}s', flush=True)


if __name__ == '__main__':
    for k in sys.argv[1:] or ['evidence', 'coverage', 'B2', 'automaton']:
        run(k)
