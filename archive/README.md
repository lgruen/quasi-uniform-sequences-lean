# Data and verification archive

Archive accompanying the paper "Low-discrepancy quasi-uniform digital sequences in every dimension" (Appendix
`app:cert`, subsection `app:archive`). Every computer-assisted statement of the paper consists of a written reduction
(a theorem with a proof in the text) and an explicit finite predicate checked over an explicit finite set
(Table `tab:ca`); the exact computations quoted in the paper without being part of a proof are listed in Table
`tab:checks`. This archive holds, per item, the finite data and the programs that re-check the predicate from the
data. The searches that produced the data (random and exhaustive searches over check vectors, randomized searches for
window systems, SAT solvers) are provenance only and are not archived; correctness never depends on them.

Paper statements are cited by their LaTeX labels (e.g. `thm:block`, `tab:residue`).

All commands are run from this directory (the archive root). Commands that compile C++ write the binaries to `bin/`
(created on first use; delete it afterwards). Requirements: Python 3 (standard library), a C++17 compiler (`g++`),
a C99 compiler for the optional demo in `b2_dropin/`, and, through `uv` (or any Python environment with these
packages), SymPy for `p1_certificates/`, `mrA_designs/` (cross-check), `bs_ruleB_s3/`, `bs_s45_thresholds/`, and NumPy
for `practice/rebuild_check.py` (also used by `primepower/`). Every single command below ran in less than half a
minute on one core on 2026-10-29 (the s = 5 window systems in chunks of 400 records); the full log of that run is
summarised in each directory's README.

| directory | paper statement (label) | finite check | re-run (from the archive root) |
|---|---|---|---|
| `verify/` | common verifier of the window systems: hypotheses of `prop:steer`, crosses by `prop:LI`(c), coverings (exact or by `lem:ws`), window bound `lem:cert` (j = 1) | per record | `python3 verify/verify_designs.py FILE...` (record format in `verify/README.md`) |
| `common/` | shared C++ header (F_p arithmetic, one-digit certificate, coverings) used by `mrA_designs/` and `selection_rule/` | — | — |
| `residue_tables/` | `tab:residue` (`thm:residue`, `cor:korobov`); the four check vectors of `tab:practice` | exact ljit(Λ_v)² of every listed v; all (x,−1) for the rows marked E; Korobov column | `python3 residue_tables/run_programs.py`; `sh residue_tables/audit2_run.sh` (after compiling, see README); `python3 residue_tables/box_check.py` |
| `block_lb/` | `thm:block`(c) below its proof range | exact LB(F) of U*_4, U*_5 at every prime 7 ≤ p ≤ 109 (s = 4), 19 ≤ p ≤ 109 (s = 5) | `python3 block_lb/lbcheck_allR.py`; `python3 block_lb/lbF.py 4 7 109`; `python3 block_lb/lbF.py 5 19 109` |
| `primepower/` | `prop:primepower`, `tab:primepower` | exact β_q for every weight vector, 13 rows; every power-basis encoding | `sh primepower/run_all.sh`; `uv run --with numpy python practice/rebuild_check.py primepower` |
| `p1_certificates/` | earlier version of this work (ordered window systems), not used in this paper | G(u*) < 1 at one rational u* per s = 3..7 | `uv run --with sympy python p1_certificates/p1_eval.py` |
| `mrA_designs/` | earlier version of this work (ordered window systems), not used in this paper | per prime below P_1: archived ordered system | `python3 verify/verify_designs.py mrA_designs/mrA_designs_s3.txt ...` |
| `lf_designs/` | earlier version of this work (ordered window systems), not used in this paper | per prime: archived ordered system | `python3 verify/verify_designs.py lf_designs/lf_designs_s3.txt ...`; s = 5 with `--range a b` |
| `p7_graph_certificate/` | `thm:p7` (Appendix `app:p7`) | finite certificate, law and t = 0 | `python3 p7_graph_certificate/code/verify_cert3.py ...` (README there) |
| `bs_ruleB_s3/` | `thm:A3` (predicate of `prop:P0` at p_0 = 19 673 600), `rem:A3range` | Π(p_0); per-prime hypotheses on [3·10⁶, 1.97·10⁷] | README there |
| `bs_s45_thresholds/` | thresholds quoted after `thm:A` (s = 4, 5) | Π(p_0) by exact bisection; spot checks above p_0 | README there |
| `selection_rule/` | the rule of `rem:steerrule`; the window systems of the sequences in the figures | rule, law, t = 0, exact sep(P_3); records verified by `verify/` | README there |
| `practice/` | `tab:practice` (`sec:practice`): four residue sequences and the ordered window systems of the comparison; point generator | matrices rebuilt from `def:residue`; exact ljit²; records verified by `verify/` | README there |
| `b2_dropin/` | `thm:B2`: drop-in table of 32-bit direction numbers, reference implementation in C | 64 words rebuilt from the series; t = 0 | `python3 b2_dropin/b2build.py` (README there) |
| `failure/` | `tab:sobolpar`; explicit pairs of `sec:fail` (`thm:nonqu`, `cor:halton`, `cor:sobol`, `cor:faure`, `cor:unscrambled`, `rem:faurerate`, `rem:toeplitz`) | exact parameters; exact distances of the pairs | `python3 failure/check_f4_sobol.py`; `python3 failure/check_fail.py`; `bash failure/campaign.sh P` |
| `exact_relations/` | `rem:skelsearch` (exhaustive in its scope); example after `cor:nodesign` | exhaustive branch and bound; dimension of a space of relations | README there |

Summary of the run of 2026-10-29: all checks listed in the directory READMEs passed (window-system records:
2846 / 2846 PASS, see `verify/results/`); the negative controls described there were rejected as intended. What is
not archived, and where a re-check is weaker than the paper's description, is stated in the README of the directory
concerned.

Items of `tab:ca` that are not in this archive because they are part of the Lean development of the paper
(Appendix `app:lean`): the automata of `thm:B2`, `thm:S3`, `thm:K4`, `thm:S4`, `rem:B3` (Table `tab:frames`) and the
range 3677 < p < 10⁴ of `cor:HB17`.
