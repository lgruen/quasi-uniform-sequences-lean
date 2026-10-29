# primepower/ — the bounds β_q of the staggered residue sequence over F_q

Supports: `prop:primepower` and Table `tab:primepower` (26 rows: s = 2, q = 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125,
128; s = 3, q = 25, 32, 49, 64, 81, 121, 125, 128, 169; s = 4, q = 49, 121, 125; s = 5, q = 121, 169). Listed in Table
`tab:ca` ("exact β_q(k); for s ≤ 3 for every f, k"):
* the value β_q of every row at its (f, k), by two programs (all rows) and a third (rows with s ≤ 3);
* for s ≤ 3: the row's value is the maximum over all monic irreducible f of degree r and all weights (exhaustive), by
  three programs; for s = 4, 5 the rows were found by search (only their values are checked);
* the caption: q = 25, s = 2: β_q from 5/25 (x²+2) to 8/25 (x²+3) over the irreducible quadratics; q = 32, s = 3:
  positive for 2 of the 6 irreducible quintics;
* the zeros in the text after the table (exact computations, exhaustive in the stated scope): β_q = 0 for every digit
  code and every weight for q = 8, 9 in dimension three (two programs), for every F_p-linear code for q = 16, 27 in
  dimension three (one program, `pp_search lin`), and for every power-basis code (every monic irreducible f) and every
  weight for q = 16, 25, 27, 32, 64, 81 in dimension four and q = 49 in dimension five (two programs);
* illustrations (not part of a proof): the last column, exact sep(P_3) for the s = 3 rows (places with codes 0, 1, 2,
  c⋆ = 2, θ = 1), and the range 0.0144 (q = 32) to 0.1484 (q = 49) of the smallest sep(P_[N]) over all N ≤ 10⁷ for the
  s = 3 rows, above β_q/q in every case — both reproduced.
The coverage of prime powers in `thm:coverage`(a)–(d) is the list of rows.

Encoding: an element Σ c_i b^i of F_q (b a root of the monic irreducible f) has the code Σ c_i p^i (power basis).
β_q(k) is the one-digit, one-coordinate bound of `lem:cert` (j = 1) on the staggered coordinate with the carry rule
over F_q.

Data: `table_primepower.tsv` — the 26 rows of `tab:primepower` (s, q, p, coefficients of f, f, weights k, β_q, and
the exact sep(P_3) of the s = 3 rows), transcribed from the table; `rows_check.py` checks that the f column is the
polynomial of the coefficients.

Programs:
* `original_fq_residue.py` — the original program (smallest monic irreducible f, ordered by the codes of the
  coefficients below the leading one); usage `p r s`.
* `audit_fq.cpp` — the audit's own F_q arithmetic, exhaustive over the weights, for one f or for every monic
  irreducible f of degree r (`all`); usage `p r f s beta`. Its mode `sep` computes exact separations (and checks the
  relation of the staggered coordinate on the points and t = 0 at the full levels).
* `audit2_primepower.py` — a second audit: β_q at the weights of the 13 rows of the first version of the table
  (`rows`; smallest f), or the best over all weights for every irreducible f (`best s p r`); its functions are also
  used by `rows_check.py` for the 26 rows.
* `pp_beta_audit.py` — the audit of the Lean stage: its own field arithmetic, β_q at given weights (or the maximum over
  all weights); used by `rows_check.py`.
* `pp_best_audit.cpp` — the same audit: maximum of β_q over every monic irreducible f and every weight (`V=1`: per f).
* `pp_anycode_audit.cpp` — the same audit: maximum over every digit code (bijection F_q → {0, ..., q−1}, 0 ↦ 0) and
  every weight, for tiny q.
* `pp_search.cpp` — the exact search of the Lean stage that found the new rows: modes `pb` (every monic irreducible f,
  power-basis code, every weight up to the order of the weights), `lin` (every ordered F_p-basis), `any` (every digit
  code).
* Third program: `practice/rebuild_check.py` (independent re-implementation, exhaustive over the weights for a given f):
  `practice/rebuild_check.py primepower` for the 13 rows of the first version, `rows_check.py third` for the 21 rows
  with s ≤ 3 of the current table.
* `run_all.sh`, `rows_check.py`, `best_check.py`, `sep_check.py` — drivers (no mathematics of their own; they compare
  the programs' output with the table and the text).

## Re-run (from the archive root)

First version of the table (13 rows, smallest f; as run for the first version of the archive):

    sh primepower/run_all.sh
    uv run --with numpy python practice/rebuild_check.py primepower

Current table, after compiling (`mkdir -p bin && for x in audit_fq pp_best_audit pp_search pp_anycode_audit; do
g++ -O2 -std=c++17 -o bin/$x primepower/$x.cpp; done`):

    python3 primepower/rows_check.py audit2
    python3 primepower/rows_check.py ppbeta
    uv run --with numpy python primepower/rows_check.py third
    python3 primepower/best_check.py fq          (and: ppb, pb)
    python3 primepower/best_check.py codes
    python3 primepower/best_check.py zeros pb    (and: zeros ppb)
    python3 primepower/sep_check.py P3
    python3 primepower/sep_check.py min 25,32,49 (and: min 64,81,121; min 125,128,169; about 0.6 GB of memory)

Expected, first version: (1) the original program prints `best beta_Q = ` 1/8, 1/9, 1/16, 5/25, 3/27, 17/49 (s = 2)
and 1/25, 0/32, 5/49, 2/64, 1/81, 19/121, 8/125 (s = 3; 0/32 because its encoding of F_32 is the smallest quintic
x⁵+x²+1, not the table's); (2) the audit prints one line per irreducible f: F_25 (s = 2) ranges over 5/25 ... 8/25,
F_32 (s = 3) is 1/32 exactly for x⁵+x³+x²+x+1 and x⁵+x⁴+x²+x+1 and 0 for the other four, and every encoding of F_8,
F_9, F_16, F_27 (s = 3) gives 0; (3) the second audit prints `beta*q` = 1, 1, 1, 5, 3, 17, 1, 1, 5, 2, 1, 19, 8 for the
13 rows; the third program prints the same 13 values (and 1/32, 0/32 for the two other quintics). Six of these rows
are rows of the current table (s = 2: q = 8, 9, 16; s = 3: q = 32, 49, 64); for the other seven the current table has a
better f.

Expected, current table: `rows_check.py` prints one line per row and `audit2: 26/26 rows OK`, `ppbeta: 26/26 rows OK`,
`third: 21/21 rows OK`; `best_check.py fq|ppb|pb` prints for each s ≤ 3 row the number of irreducible f, the maximum
over f and weights (= the table value) and the value of the table's f, the two caption statements, and
`23/23 statements OK`; `codes` prints 0/8, 0/9 over 5040 and 40320 digit codes (both programs), 0/16, 0/27 over 20160
and 11232 ordered bases, `ALL OK`; `zeros pb|ppb` prints max 0 for s = 4, q = 16 (3 irreducible f), 25 (10), 27 (8),
32 (6), 64 (9), 81 (18) and s = 5, q = 49 (21), `ALL OK`; `sep_check.py P3` prints sep(P_3) = 0.1961, 0.1814, 0.3565,
0.1781, 0.1848, 0.2719, 0.2323, 0.1767, 0.2320 (to 4 decimals; q = 25, ..., 169), `ALL OK`; `min` prints 0.069802
(q = 25), 0.014447 (32), 0.148359 (49), 0.025585 (64), 0.073699 (81), 0.109381 (121), 0.066975 (125), 0.043869 (128),
0.056729 (169), each above β_q/q, `ALL OK`.

Requirements: Python 3, a C++17 compiler; NumPy for the third program.

Last run 2026-10-29: PASS. First version: 2.4 s + 0.6 s. Current table: rows 1.3 s (audit2 + ppbeta), third 1.2 s;
maxima 3.5 s (fq), 2.4 s (ppb), 1.5 s (pb); codes 2.3 s; zeros 3.6 s (pb), 29.6 s (ppb); sep(P_3) 4.0 s; minima over
N ≤ 10⁷ 25.5 s, 23.6 s, 22.8 s (one core).
