# b2_dropin/ — drop-in table for the base-two sequence

Supports: `thm:B2` in practice (`sec:practice`: "the archive lists 32-bit direction numbers that replace the first two
dimensions of a Sobol' table"). Not a computer-assisted proof item (the automata of `thm:B2` are checked in the Lean
development, Appendix `app:lean`).

Files:
* `B2_dropin_table.tex` — the table (formerly an appendix of a draft): the generator matrices of `thm:B2` as 32-bit
  direction numbers M_c[k] (column k of C_c, digit 0 in the most significant bit), the formula
  x_c(i) = 2⁻³² ⊕_{k: i_k = 1} M_c[k], the reference implementation in C and its description. Standalone LaTeX
  (`\input` into an amsart document with booktabs).
* `b2_dropin.c` — the reference implementation as a C file: the function `b2_point` and the Gray-code note exactly as
  printed in the table file, with the array `M` transcribed from the table; an optional demo `main` (compile with
  `-DB2_DEMO`) prints points or the 64 words.
* `b2build.py` — independent rebuild of the generator matrices from the series (1+x)(1+u)u^k and (u/x)(1+u)^k of
  `thm:B2` (u = Σ_k x^{2^k}), written without the code that produced the table: compares the 64 words with the
  printed table and checks t = 0 (rank criterion) for every m ≤ 48 on 64 × 64 matrices; writes the 64-bit columns to
  `b2_cols_64bit.txt` (included: the first 64 digits of columns 0..63 of C_0 and C_1).

## Re-run (from the archive root)

    python3 b2_dropin/b2build.py
    mkdir -p bin && cc -O2 -std=c99 -Wall -DB2_DEMO -o bin/b2demo b2_dropin/b2_dropin.c
    ./bin/b2demo words > bin/words.txt
    python3 -c "W=[l.split() for l in open('bin/words.txt')]; C=[[x[:8] for x in l.split()[:32]] for l in open('b2_dropin/b2_cols_64bit.txt')]; print(W==C)"
    ./bin/b2demo 4

Expected: `M_0 mismatches at columns: []`, `M_1 mismatches at columns: []`, `t=0 failures for m<=48: []`; `True`
(the C table equals the top 32 bits of the rebuilt columns); the first points (0, 0), (0.6123161316, 0.8164215090),
(0.375, 0.5), (0.9873161316, 0.3164215090).

GAP: the table file also states that "a loop over all elementary intervals" with the table and the snippet confirms the
(0,m,2)-net property for m ≤ 14 and that a brute-force toroidal minimum distance gives sep(P_m) = 0.6334, 0.4589,
0.3998, 0.3998, 0.3998, 0.3968 (m = 2, 4, ..., 12). The program that did this is not in the archive. The net property
of every prefix P_m, m ≤ 32, of the table follows from the t = 0 check of `b2build.py` together with the equality of the
table with the rebuilt columns; the separation values are not re-checked here.

Requirements: Python 3, a C99 compiler (demo only).

Last run 2026-10-29: PASS, < 0.1 s + 0.4 s (one core).
