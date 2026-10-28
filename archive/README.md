# Data and verification archive

Archive accompanying the paper "Low-discrepancy quasi-uniform digital sequences in every dimension" (Appendix
`app:cert`, subsection `app:archive`). Every computer-assisted statement of the paper consists of a written reduction
(a theorem with a proof in the text) and an explicit finite predicate checked over an explicit finite set
(Table `tab:ca`); the exact computations quoted in the paper without being part of a proof are listed in Table
`tab:checks`. This archive holds, per item, the finite data and the programs that re-check the predicate from the
data. The searches that produced the data (random and exhaustive searches over check vectors, randomized searches for
window systems, SAT solvers) are provenance only and are not archived; correctness never depends on them.

Paper statements are cited by their LaTeX labels (e.g. `thm:block`, `tab:residue`).

All commands are run from this directory (the archive root). Commands that compile C++ or C write the binaries to
`bin/` (created on first use; delete it afterwards). Requirements: Python 3 (standard library), a C++17 compiler
(`g++`), a C99 compiler for `b2_dropin/`, and, through `uv` (or any Python environment with these packages), SymPy for
`bs_ruleB_s3/` and `bs_s45_thresholds/`, and NumPy for `practice/rebuild_check.py` (also used by `primepower/`) and
`practice/j_check.py`. Every single command below ran in less than a minute on one core on 2026-10-29 (most in a few
seconds; the longest, `practice/j_check.py`, 25–32 s per sequence); the full log of that run is summarised in each
directory's README.

| directory | paper statement (label) | finite check | re-run (from the archive root) |
|---|---|---|---|
| `verify/` | common verifier of the window systems: hypotheses of `prop:steer`, crosses by `prop:LI`(c), coverings (exact or by `lem:ws`), window bound `lem:cert` (j = 1); the five archived systems (`sec:practice` comparison, `fig:bsgeom`); negative controls | per record | `python3 verify/verify_designs.py practice/pp_designs_s3.txt selection_rule/cfg/bs_s3_p101.cfg` (record format in `verify/README.md`) |
| `common/` | shared C++ header (F_p arithmetic, one-digit certificate, coverings) used by `selection_rule/` | — | — |
| `residue_tables/` | `tab:residue` (`thm:residue`, `cor:korobov`); the four check vectors of `tab:practice` | exact ljit(Λ_v)² of every listed v; all (x,−1) for the rows marked E; Korobov column | `python3 residue_tables/run_programs.py`; `sh residue_tables/audit2_run.sh` (after compiling, see README); `python3 residue_tables/box_check.py` |
| `block_lb/` | `thm:block`(c) below its proof range | exact LB(F) of U*_4, U*_5 at every prime 7 ≤ p ≤ 109 (s = 4), 19 ≤ p ≤ 109 (s = 5) | `python3 block_lb/lbcheck_allR.py`; `python3 block_lb/lbF.py 4 7 109`; `python3 block_lb/lbF.py 5 19 109`; `python3 block_lb/run_third.py` |
| `primepower/` | `prop:primepower`, `tab:primepower` | exact β_q for every weight vector, 13 rows; every power-basis encoding | `sh primepower/run_all.sh`; `uv run --with numpy python practice/rebuild_check.py primepower` |
| `p7_graph_certificate/` | `thm:p7` (Appendix `app:p7`) | LB(w) ≥ 1/7 (two programs); law, t = 0; LB_K of the archived instance, K ≤ 140 | README there |
| `bs_ruleB_s3/` | `thm:A3` (predicate of `prop:P0` at p_0 = 19 673 600), `rem:A3range` | Π(p_0); per-prime hypotheses on [3·10⁶, 1.97·10⁷] | README there |
| `bs_s45_thresholds/` | thresholds quoted after `thm:A` (s = 4, 5) | Π(p_0) by exact bisection; spot checks above p_0 | README there |
| `selection_rule/` | the rule of `rem:steerrule`, applied to the staggered window system of `fig:bsgeom` | rule, law, t = 0, exact sep(P_3); record verified by `verify/` | README there |
| `practice/` | `tab:practice` (`sec:practice`): four residue sequences (certified bounds and 𝒥) and the ordered window systems of the comparison; point generator | matrices rebuilt from `def:residue`; exact ljit²; 𝒥 by exact minimum distances of all prefixes; records verified by `verify/` | README there |
| `b2_dropin/` | `thm:B2`: drop-in table of 32-bit direction numbers, reference implementation in C | 64 words rebuilt from the series; t = 0; elementary intervals and sep(P_m) with the table | README there |
| `failure/` | `tab:sobolpar` (s = 2, ..., 7); explicit pairs of `sec:fail` (`thm:nonqu`, `cor:halton`, `cor:sobol`, `cor:faure`, `cor:unscrambled`, `rem:faurerate`, `rem:toeplitz`) | exact parameters; exact distances of the pairs; 244 Halton-type cases (fixed seed) | `python3 failure/check_f4_sobol.py`; `python3 failure/check_fail.py`; `bash failure/campaign.sh P` |
| `exact_relations/` | `rem:skelsearch` (exhaustive in its scope); example after `cor:nodesign` | exhaustive branch and bound; dimension of a space of relations | README there |

Summary of the run of 2026-10-29: all checks listed in the directory READMEs passed (window-system records: 5 / 5
PASS, see `verify/results/`); the negative controls described there behaved as stated. Where a re-check differs from
the paper's description, or something is not archived, the README of the directory concerned says so.

Items of `tab:ca` that are not in this archive because they are part of the Lean development of the paper
(Appendix `app:lean`): the automata of `thm:B2`, `thm:S3`, `thm:K4`, `thm:S4`, `rem:B3` (Table `tab:frames`) and the
range 3677 < p < 10⁴ of `cor:HB17`.
