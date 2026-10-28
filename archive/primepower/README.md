# primepower/ — the bounds β_q of the staggered residue sequence over F_q

Supports: `prop:primepower` and Table `tab:primepower` (the 13 rows: s = 2, q = 8, 9, 16, 25, 27, 49; s = 3,
q = 25, 32, 49, 64, 81, 121, 125), including the statements in the caption and text that β_q depends on the
encoding (q = 25, s = 2: 5/25 to 8/25 over the irreducible quadratics; q = 32, s = 3: positive for 2 of the 6
irreducible quintics) and that for q = 8, 9, 16, 27 in dimension three every power-basis encoding gives β_q = 0 for
every choice of weights. Listed in Table `tab:ca`.

Encoding: an element Σ c_i b^i of F_q (b a root of the monic irreducible f) has the code Σ c_i p^i (power basis).
β_q(k) is the one-digit, one-coordinate bound of `lem:cert` (j = 1) on the staggered coordinate with the carry rule
over F_q; the best value is the maximum over all weight vectors k (exhaustive).

Data: `table_primepower.tsv` — the 13 rows of `tab:primepower` (s, q, f, weights k, β_q), transcribed from the
table; the same rows are written into `audit2_primepower.py` (compared: equal).

Programs:
* `original_fq_residue.py` — the original program (smallest monic irreducible f, ordered by the codes of the
  coefficients below the leading one); usage `p r s`.
* `audit_fq.cpp` — the audit's own F_q arithmetic, exhaustive over the weights, for one f or for every monic
  irreducible f of degree r (`all`); usage `p r f s beta`. (Its mode `sep` computes exact separations, the
  illustration column of the table; not part of the check.)
* `audit2_primepower.py` — a second audit: β_q at the weights of the 13 table rows (`rows`), or the best over all
  weights for every irreducible f (`best s p r`).
* Third program: `practice/rebuild_check.py primepower` (independent re-implementation, exhaustive over the weights,
  for the encodings of the table and the two other quintics over F_2).
* `run_all.sh` — driver (no mathematics of its own) for the first three.

## Re-run (from the archive root)

    sh primepower/run_all.sh
    uv run --with numpy python practice/rebuild_check.py primepower

Expected: (1) the original program prints `best beta_Q = ` 1/8, 1/9, 1/16, 5/25, 3/27, 17/49 (s = 2) and 1/25, 0/32,
5/49, 2/64, 1/81, 19/121, 8/125 (s = 3; 0/32 because its encoding of F_32 is the smallest quintic x⁵+x²+1, not the
table's); (2) the audit prints one line per irreducible f: the table's encodings give the table's values, F_25 (s = 2)
ranges over 5/25 ... 8/25, F_32 (s = 3) is 1/32 exactly for x⁵+x³+x²+x+1 and x⁵+x⁴+x²+x+1 and 0 for the other four,
and every encoding of F_8, F_9, F_16, F_27 (s = 3) gives 0; (3) the second audit prints `beta*q` = 1, 1, 1, 5, 3, 17,
1, 1, 5, 2, 1, 19, 8 for the 13 rows; the third program prints the same 13 values (and 1/32, 0/32 for the two other
quintics).

Requirements: Python 3, a C++17 compiler; NumPy for the third program.

Last run 2026-10-29: PASS, 2.6 s + 0.6 s (one core).
