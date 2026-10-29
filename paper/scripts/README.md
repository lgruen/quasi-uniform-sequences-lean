# scripts/ — the programs that draw the figures of the paper

Every figure of the paper (the 18 PDFs in `../figs/`) is drawn by the scripts in this directory from the generator
matrices of the constructions; the scripts need no file outside this directory. Run them from the paper directory
(the one containing `main.tex`, `figs/` and `scripts/`).

Requirements: [uv](https://docs.astral.sh/uv/) (Python 3 with NumPy and matplotlib 3.11.0, installed by uv on the
fly), a C++17 compiler, and `pdftoppm` (poppler) for the comparison with the committed figures.

    bash scripts/run_all.sh          # builds the C++, regenerates every figure, compares; about 1 minute

`run_all.sh` writes the figures to a temporary directory (`$FIGOUT` if set), never over `figs/`; it reruns the data
generators against the data files they produced, and exits non-zero if a data file or a figure differs. Measured on an
Apple-silicon laptop (2026-10-29): 51 s for all scripts (one core), of which 24 s for `fig:evidence` (the exact
separation of every prefix up to 2^23 points).

The committed PDFs were written with matplotlib 3.11.0 and carry their creation date, so their bytes are not
reproduced; `figcmp.py` compares the rasterized pages (150 dpi) pixel by pixel. With matplotlib 3.11.0 all 18 figures
are pixel-identical to `figs/` (checked 2026-10-29).

## Commands

Build the C++ programs (done by `run_all.sh`):

    mkdir -p scripts/bin
    g++ -O3 -std=c++17 -o scripts/bin/sepx  scripts/sepx.cpp     # exact toroidal separation of a digital prefix (cell list)
    g++ -O3 -std=c++17 -o scripts/bin/mdist scripts/mdist.cpp    # exact minimum distance of every prefix / nearest neighbours
    g++ -O3 -std=c++17 -o scripts/bin/lb    scripts/lb.cpp       # one-digit relaxation LB(F) of lem:cert

`PY` stands for `uv run --no-project --with numpy --with matplotlib==3.11.0 python`. Every figure script accepts
`--out DIR` (default `figs/`, i.e. it overwrites the committed figure) and also writes a PNG preview next to each PDF.

| figure (label) | file in `figs/` | command | time |
|---|---|---|---|
| `fig:levels` | `fig_levels` | `PY scripts/b7_levels.py --out DIR` | 1 s |
| `fig:carry` | `fig_carry` | `PY scripts/b2_carry.py --out DIR` | 2 s |
| `fig:hierarchy`, `fig:idea`, `fig:cert` | `fig_hierarchy_v4`, `fig_idea_v4`, `fig_cert_v4` | `PY scripts/b1_relabel.py --out DIR` | 1 s |
| `fig:residue`, `fig:block` | `fig_residue`, `fig_block` | `PY scripts/b3_figs.py --out DIR` | 2 s |
| `fig:freediag` | `fig_freediag` | `PY scripts/b8_freediag.py --out DIR` | 1 s |
| `fig:count` | `fig_count` | `PY scripts/b4_figs.py --out DIR` | 1 s |
| `fig:HB` | `fig_HB_v4` | `PY scripts/b5_figs.py --out DIR HB` | 1 s |
| `fig:automaton`, `fig:B2` | `fig_automaton_v4`, `fig_B2_v4` | `PY scripts/b6_figs.py --out DIR automaton B2` | 1 s |
| `fig:dim3` | `fig_coverage` | `PY scripts/b6_figs.py --out DIR coverage` | 1 s |
| `fig:evidence` | `fig_evidence3d_v4` | `PY scripts/b6_figs.py --out DIR evidence` (needs `bin/mdist`) | 25 s |
| `fig:principles`, `fig:cost` | `fig_halfcell_v4`, `fig_volume_v4` | `PY scripts/cut1_figs.py --out DIR` | 1 s |
| `fig:bsgeom` | `fig_bs_slab_v4`, `fig_bs_3d_v4` | `PY scripts/b5_figs.py --out DIR bs` (needs `bin/mdist`) | 3 s |
| (comparison) | | `PY scripts/figcmp.py DIR` | 5 s |

Data generators (each compares its result with the committed data file and exits 1 if they differ; `--write`
rewrites the file):

| data file | read by | command | time |
|---|---|---|---|
| `data/levels_p5.txt` (exact sep(P_m), s = 2, p = 5, m ≤ 10) | `b7_levels.py`, `explainers/gen_data.py` | `PY scripts/b7_levels_data.py` (needs `bin/sepx`) | 5 s |
| `data/freediag.json` (LB(F) of `thm:block`(c), (d)) | `b8_freediag.py`, `explainers/gen_data.py` | `PY scripts/b8_freediag_data.py` (needs `bin/lb`) | 9 s |
| `data/drops_res31.txt` (drops of the residue sequence of `tab:practice`) | `explainers/gen_data.py` | recomputed by `b6_figs.py evidence` | (above) |

`PY scripts/b3_gen.py` runs the self-test of the residue generator (Example `ex:running`, agreement with the
independent generator `audit_gen.py`, the relations of `lem:residue-rel` and `lem:residuestar-rel`).

## Files

- Figure scripts: `b1_relabel.py`, `b2_carry.py`, `b3_figs.py`, `b4_figs.py`, `b5_figs.py`, `b6_figs.py`, `b7_levels.py`,
  `b8_freediag.py`, `cut1_figs.py`; data generators `b7_levels_data.py`, `b8_freediag_data.py`; `run_all.sh`,
  `figcmp.py`; `_paths.py` (directories, `--out`).
- Builders and generators: `make_figs.py`, `make_figs_v3.py`, `make_figs_bs.py` (figure builders; extracted from the
  development scripts with only the functions these figures use, code unchanged except for paths), `b3_gen.py`
  (residue formulas), `audit_gen.py` (independent generator of the block-periodic residue sequences), `wbuild.py` +
  `w_alib.py` (brick walls), `hlib.py`, `hverify.py`, `dlib.py`, `t2d_alib.py` (window rules, hexagonal brick wall),
  `b2core.py` (`thm:B2`), `bslib.py` (point sets of the window-system figures), `klib.py` (field arithmetic).
- C++: `sepx.cpp`, `mdist.cpp`, `lb.cpp` (standard library only).
- `data/`: `best_U_31.txt` (generator matrices of the residue sequence of `tab:practice`, s = 3, p = 31),
  `bs3_p101.txt` (generator matrices of the staggered window system p = 101), `pp_s3_p31.cfg` (the ordered window
  system p = 31 of the panels of the development version from which `fig_halfcell_v4`, `fig_volume_v4` are cut),
  `ustar4.txt` … `ustar7.txt` (the designs U*_s, identical to `archive/block_lb/`), and the precomputed data
  `levels_p5.txt`, `freediag.json`, `drops_res31.txt` (recomputed above) and `drops_fa31.txt`, `drops_sob1.txt`,
  `drops_sob2.txt`, `drops_sob3.txt` (exact minimum distance of every prefix up to 2^23 points of the Faure sequence
  (I, P, P²) in base 31 and of three Owen-scrambled Sobol' sequences (base 2), dimension three, computed with
  `mdist.cpp` in the development repository; the program that generated the point sets is not included, so these
  four files are inputs, not recomputed).

The three Sobol' coordinates use the first three direction-number sets (x, x+1, x²+x+1), which are written into the
generator of the development repository; no table of direction numbers is needed or shipped.
