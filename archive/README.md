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
`bs_ruleB_s3/`, `bs_s45_thresholds/` and `block_lb/fd_s45_check.py`, and NumPy for `practice/rebuild_check.py` (also
used by `primepower/`), `practice/j_check.py` and `hammersley/brute_check.py`. Every single command below ran in less
than a minute on one core on 2026-10-29 and again on 2026-10-30 with `hammersley/` (most in a few seconds; the longest
are the exact evaluations of LB(F) for s = 7 in `block_lb/`, split by prime ranges into runs of 23–45 s,
`practice/j_check.py`, 22–26 s per sequence, and the separations of the lifts in `hammersley/`, split into runs of at
most 46 s); the full log of that run is summarised in each directory's README.

| directory | paper statement (label) | finite check | re-run (from the archive root) |
|---|---|---|---|
| `verify/` | common verifier of the window systems: hypotheses of `prop:steer`, crosses by `prop:LI`(c), coverings (exact or by `lem:ws`), window bound `lem:cert` (j = 1); the five archived systems (`sec:practice` comparison, `fig:bsgeom`); negative controls | per record | `python3 verify/verify_designs.py practice/pp_designs_s3.txt selection_rule/cfg/bs_s3_p101.cfg` (record format in `verify/README.md`) |
| `common/` | shared C++ header (F_p arithmetic, one-digit certificate, coverings) used by `selection_rule/` | — | — |
| `residue_tables/` | `tab:residue` (`thm:residue`, `cor:korobov`); the four check vectors of `tab:practice` | exact ljit(Λ_v)² of every listed v; all (x,−1) for the rows marked E; Korobov column | `python3 residue_tables/run_programs.py`; `sh residue_tables/audit2_run.sh` (after compiling, see README); `python3 residue_tables/box_check.py` |
| `block_lb/` | `thm:block`(c) below its proof range; `thm:block`(d) with `lem:signclass` (`tab:block`, `fig:freediag`); data check of U*_4, ..., U*_7; optimality remark after `thm:block`(d) | exact LB(F) of U*_4, U*_5 at every prime 7 ≤ p ≤ 109 (s = 4), 19 ≤ p ≤ 109 (s = 5); hypothesis of `lem:signclass` (A, S) and exact LB(F) of the free-diagonal designs, s = 4, ..., 7, below the threshold; U*_s files vs an independent implementation of its definition, reachability over Q; no δ ∈ [0,A]^s with A ≤ 2, 6, 13 | `python3 block_lb/lbcheck_allR.py`; `python3 block_lb/lbF.py 4 7 109`; `python3 block_lb/lbF.py 5 19 109`; `python3 block_lb/run_third.py`; `python3 block_lb/run_freediag.py ...` (after compiling, see README) |
| `primepower/` | `prop:primepower`, `tab:primepower`; zeros of β_q in the text after it | exact β_q of the 26 rows; for s ≤ 3 the maximum over every monic irreducible f and every weight; zeros over every digit code / F_p-linear code / power-basis code in the stated cases | `python3 primepower/rows_check.py audit2`; `python3 primepower/best_check.py fq` (after compiling, see README); first version: `sh primepower/run_all.sh` |
| `p7_graph_certificate/` | `thm:p7` (Appendix `app:p7`) | LB(w) ≥ 1/7 (two programs); law, t = 0; LB_K of the archived instance, K ≤ 140 | README there |
| `bs_ruleB_s3/` | `thm:A3` (predicate of `prop:P0` at p_0 = 19 673 600), `rem:A3range` | Π(p_0); per-prime hypotheses on [3·10⁶, 1.97·10⁷] | README there |
| `bs_s45_thresholds/` | thresholds quoted after `thm:A` (s = 4, 5) | Π(p_0) by exact bisection; spot checks above p_0 | README there |
| `selection_rule/` | the rule of `rem:steerrule`, applied to the staggered window system of `fig:bsgeom` | rule, law, t = 0, exact sep(P_3); record verified by `verify/` | README there |
| `practice/` | `tab:practice` (`sec:practice`): four residue sequences (certified bounds and 𝒥) and the ordered window systems of the comparison; point generator | matrices rebuilt from `def:residue`; exact ljit²; 𝒥 by exact minimum distances of all prefixes; records verified by `verify/` | README there |
| `b2_dropin/` | `thm:B2`: drop-in table of 32-bit direction numbers, reference implementation in C | 64 words rebuilt from the series; t = 0; elementary intervals and sep(P_m) with the table | README there |
| `failure/` | `tab:sobolpar` (s = 2, ..., 7); explicit pairs of `sec:fail` (`thm:nonqu`, `cor:halton`, `cor:sobol`, `cor:faure`, `cor:unscrambled`, `rem:faurerate`, `rem:toeplitz`) | exact parameters; exact distances of the pairs; 244 Halton-type cases (fixed seed) | `python3 failure/check_f4_sobol.py`; `python3 failure/check_fail.py`; `bash failure/campaign.sh P` |
| `exact_relations/` | `rem:skelsearch` (exhaustive in its scope); example after `cor:nodesign` | exhaustive branch and bound; dimension of a space of relations | README there |
| `hammersley/` | `sec:hammersley`: exact separations of the Hammersley lifts (comparison after `prop:liftcarry`, `fig:hammersley`); closest pairs of `prop:liftcarry`; checks of `prop:liftcarry` on explicit pairs | the 183 rows of `lift_results.csv` recomputed (the 70 smallest also by an all-pairs program); closest-pair index polynomials; the pair of the proof against the bound, exactly | README there |

Summary of the runs of 2026-10-29 and 2026-10-30: all checks listed in the directory READMEs passed (window-system records: 5 / 5
PASS, see `verify/results/`); the negative controls described there behaved as stated. Where a re-check differs from
the paper's description, or something is not archived, the README of the directory concerned says so.

Items of `tab:ca` that are not in this archive because they are part of the Lean development of the paper
(Appendix `app:lean`): the automata of `thm:B2`, `thm:S3`, `thm:K4`, `thm:S4`, `rem:B3` (Table `tab:frames`) and the
range 3677 < p < 10⁴ of `cor:HB17`.
