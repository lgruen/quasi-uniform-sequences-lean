# exact_relations/ — the exhaustive search of `rem:skelsearch` and the example after `cor:nodesign`

Supports (Table `tab:checks`):
1. `rem:skelsearch` (exhaustive in its scope): s = 2, p = 11, 13, 17, K_max = 10, 8, 11: over every sequence
   u_0, ..., u_{K_max} of check directions in which u_1, ..., u_{K_max−1} have the largest possible ljit(Λ_u)
   (u_0, u_{K_max} arbitrary), the maximum of the smallest one-digit relaxation (`lem:cert`, j = 1) of the actual
   responses over the full levels K ≤ K_max equals the inclusion bound 0.1818, 0.1720, 0.1765 of the best direction.
2. The example after `cor:nodesign`: s = 4, places 0, 1, 2, 3 over F_p, J = 3: the relations of top index K and depth
   ≤ 3 among the residue digits form a space of dimension 2 at p = 11, K = 4, dimension 1 at p = 11 for 5 ≤ K ≤ 11, and
   dimension 1 at p = 13 and p = 17 for K = 4 (two methods, and the audit).

Data: `lam_11_2.txt`, `lam_13_2.txt`, `lam_17_2.txt` (the search's law Λ of the residue digits, places (0, 1), θ = 1:
first line `p s D`, then Λ[c][c'][d]) and `lam_audit_*_2.txt` (the audit's own computation of the same law, format
`p s D` then all entries on one line). Both are reproduced byte-identically by their generators (below).

Programs:
* `bb_search.cpp` — the search program: exact branch and bound over all sequences (global scale fixed), constraint
  ljit² ≥ J_min for every direction (J_min = 4, 5, 9 = the best value at p = 11, 13, 17).
* `bb_audit.cpp` — the audit's independent branch and bound (integer arithmetic p²LB²): mode `max` (exact maximum) and
  mode `cnt` (number of prefixes whose bound stays above a threshold, per K; 0 survivors above the inclusion bound at
  K = K_max).
* `law_search.py` (+ `gen.py`) and `law_audit.py` (+ `gen7.py`, `gen.py`) — the two generators of Λ from the generator
  matrices (each also validates the response formula against generator matrices of random digit-scaled scrambles).
* `reldim_rows.py` — method A: rows of the residue digits from `def:residue`, dimension of the left kernel;
  `reldim_wadic.py` — method B: the w-adic criterion of `lem:reltype`; `reldim_audit.py` (+ `fp.py`) — the audit,
  both methods (K = J ... J+5, and further cases).

## Re-run (from the archive root)

    mkdir -p bin && g++ -O2 -std=c++17 -o bin/bb_search exact_relations/bb_search.cpp && g++ -O2 -std=c++17 -o bin/bb_audit exact_relations/bb_audit.cpp
    ./bin/bb_search exact_relations/lam_11_2.txt bb 10 - 4 50
    ./bin/bb_search exact_relations/lam_13_2.txt bb 8 - 5 50
    ./bin/bb_search exact_relations/lam_17_2.txt bb 11 - 9 50
    ./bin/bb_audit exact_relations/lam_audit_11_2.txt max 10 4 0 50;  ./bin/bb_audit exact_relations/lam_audit_11_2.txt cnt 10 4 4 50
    ./bin/bb_audit exact_relations/lam_audit_13_2.txt max 8 5 0 50;   ./bin/bb_audit exact_relations/lam_audit_13_2.txt cnt 8 5 5 50
    ./bin/bb_audit exact_relations/lam_audit_17_2.txt max 11 9 0 50;  ./bin/bb_audit exact_relations/lam_audit_17_2.txt cnt 11 9 9 50
    python3 exact_relations/law_search.py 17 2 0,1 bin/ls.txt && cmp bin/ls.txt exact_relations/lam_17_2.txt          (also 11, 13)
    python3 exact_relations/law_audit.py 17 2 0,1 16 bin/la.txt && cmp bin/la.txt exact_relations/lam_audit_17_2.txt  (11 and 13 with 12)
    for K in 4 5 6 7 8 9 10 11; do python3 exact_relations/reldim_rows.py 11 4 3 $K 0 | head -1; done
    python3 exact_relations/reldim_rows.py 13 4 3 4 0 | head -1;  python3 exact_relations/reldim_rows.py 17 4 3 4 0 | head -1
    python3 exact_relations/reldim_wadic.py 11 4 3 0,1,2,3   (also 13, 17)
    python3 exact_relations/reldim_audit.py

Expected: `max ... = 0.1818 (exact)`, `0.1720 (exact)`, `0.1765 (exact)` from both branch-and-bound programs (with the
same witnesses); survivor counts ending in `0 (EXACT)`; `cmp` silent; method A: `dim 2` at p = 11, K = 4, `dim 1`
otherwise; method B: `[(3, 4), (4, 2), (5, 1), ...]` at p = 11 and `(4, 1)` at p = 13, 17; the audit prints the pairs
(dimension by A, by B) `(4, 2, 2)` at p = 11 and `(4, 1, 1)` at p = 13, 17.

Scope (as in `rem:skelsearch`): s = 2, these three primes, these K_max, the best check directions and the one-digit
relaxation; nothing is claimed for other primes, dimensions, weaker directions or multi-digit certificates.

Requirements: Python 3, a C++17 compiler.

Last run 2026-10-29: PASS, 3.0 s (search B&B, incl. compilation) + 2.7 s (audit B&B, incl. compilation) + 0.3 s (laws)
+ 0.2 s + 0.1 s + 0.1 s (relation dimensions) (one core).
