#!/usr/bin/env python3
r"""figcmp.py -- compare regenerated figures with the figures of the paper.

    PY scripts/figcmp.py NEWDIR [REFDIR]        (from paper/; REFDIR default: figs/ next to scripts/)

For every figure that the paper includes (\paperfig{...} and \includegraphics{....pdf} in main.tex and sections/*.tex,
found at run time, LaTeX comments ignored): IDENTICAL if the PDF bytes agree; otherwise both PDFs are rasterized with
pdftoppm (poppler, 150 dpi) and compared pixel by pixel: SAME-PIXELS or DIFFERENT (with the number of differing pixels).
The PDFs of the paper were written with matplotlib 3.11.0 and carry their creation date, so their bytes are not
reproduced; the drawn content is. Without pdftoppm a byte difference is reported as NOT-COMPARED. Exit status 1 if
anything is DIFFERENT or missing. Needs numpy + matplotlib (PNG reader) only when pixels are compared.
"""
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)


def included_figs():
    tex = ''
    for fn in [os.path.join(PAPER, 'main.tex')] + sorted(glob.glob(os.path.join(PAPER, 'sections', '*.tex'))):
        tex += re.sub(r'(?<!\\)%.*', '', open(fn).read()) + '\n'
    names = set(re.findall(r'\\paperfig\{([^}#]+)\}', tex))
    names |= {f[:-4] for f in re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}#]+)\}', tex) if f.endswith('.pdf')}
    return sorted(names)


def raster(pdf, outdir, tag):
    subprocess.run(['pdftoppm', '-r', '150', '-png', pdf, os.path.join(outdir, tag)], check=True)
    return sorted(os.path.join(outdir, f) for f in os.listdir(outdir) if f.startswith(tag) and f.endswith('.png'))


def pixels_equal(a, b):
    import numpy as np
    import matplotlib.image as mi
    tmp = tempfile.mkdtemp(prefix='figcmp_')
    try:
        ra, rb = raster(a, tmp, 'a'), raster(b, tmp, 'b')
        if len(ra) != len(rb):
            return False, 'page count differs'
        for x, y in zip(ra, rb):
            X, Y = mi.imread(x), mi.imread(y)
            if X.shape != Y.shape:
                return False, f'size {X.shape} vs {Y.shape}'
            d = np.abs(X.astype(float) - Y.astype(float))
            if d.max() > 0:
                return False, f'{int((d.max(-1) > 0).sum())} of {X.shape[0] * X.shape[1]} pixels differ (max {d.max():.3f})'
        return True, ''
    finally:
        shutil.rmtree(tmp)


def main():
    new = os.path.abspath(sys.argv[1])
    ref = os.path.abspath(sys.argv[2]) if len(sys.argv) > 2 else os.path.join(PAPER, 'figs')
    have_raster = shutil.which('pdftoppm') is not None
    bad = 0
    figs = included_figs()
    for n in figs:
        a, b = os.path.join(new, n + '.pdf'), os.path.join(ref, n + '.pdf')
        if not os.path.exists(a):
            print(f'  MISSING      {n}.pdf (not regenerated)'); bad += 1; continue
        if open(a, 'rb').read() == open(b, 'rb').read():
            print(f'  IDENTICAL    {n}.pdf'); continue
        if not have_raster:
            print(f'  NOT-COMPARED {n}.pdf (bytes differ; pdftoppm not found)'); continue
        ok, why = pixels_equal(a, b)
        print(f'  {"SAME-PIXELS " if ok else "DIFFERENT   "} {n}.pdf {why}')
        bad += not ok
    print(f'figcmp: {len(figs)} figures;', 'all agree' if not bad else f'{bad} DIFFERENCE(S)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
