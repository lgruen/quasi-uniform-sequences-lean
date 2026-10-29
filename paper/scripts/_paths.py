"""_paths.py -- directories used by the figure scripts (imported by every script before anything else).

SCRIPTS  this directory (paper/scripts); the scripts import each other from here
DATA     SCRIPTS/data: the input data of the figures (see README.md)
BIN      SCRIPTS/bin, or $BINDIR: the compiled C++ programs (build commands in README.md)
OUT      where the figures are written: `--out DIR` on the command line (removed from sys.argv before the script reads
         its own arguments), else $FIGOUT, else ../figs (= paper/figs, the figures of the paper)
TMP      a temporary directory for point dumps, removed when the script exits
"""
import os, sys, atexit, shutil, tempfile

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(SCRIPTS, 'data')
BIN = os.environ.get('BINDIR') or os.path.join(SCRIPTS, 'bin')
OUT = os.environ.get('FIGOUT') or os.path.join(SCRIPTS, '..', 'figs')
if '--out' in sys.argv:
    _i = sys.argv.index('--out')
    OUT = sys.argv[_i + 1]
    del sys.argv[_i:_i + 2]
OUT = os.path.abspath(OUT)
os.makedirs(OUT, exist_ok=True)
TMP = tempfile.mkdtemp(prefix='qus_figs_')
atexit.register(shutil.rmtree, TMP, True)
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)


def exe(name):
    """path of a compiled C++ program of this directory (bin/<name>)."""
    p = os.path.join(BIN, name)
    if not os.path.exists(p):
        sys.exit(f'{p} is missing: build the C++ programs first (README.md, or run_all.sh)')
    return p
