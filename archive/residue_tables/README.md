# residue_tables/ — exact jitter minima of the check-vector lattices

Supports: Table `tab:residue` (certified bounds sep(P_{sK−1}) ≥ p^{−1/s} ljit(Λ_v) of `thm:residue`, and the Korobov
column, `cor:korobov`), and the four check vectors of Table `tab:practice`. Listed in Table `tab:ca`; verification
described in Appendix `app:verification` ("Residue and block-periodic sequences").

Data: `check_vectors.tsv` — for every row of `tab:residue`: s, p, the check vector v = (x, −1), the exact integer
ljit(Λ_v)², the search label (E = exhaustive over all (x, −1), R = random over 3·10⁶ vectors x, a lower bound on the
best possible value), the truncated bound and the truncated Korobov bound; plus the four `tab:practice` vectors.
(The same lists are also written into `box_check.py`; they were compared and agree.)

Programs (Λ_v = {b ∈ Zˢ : Σ v_c b_c ≡ 0 mod p}, ljit(Λ)² = min over b ≠ 0 in Λ of Σ_c max(0, |b_c| − 1)²):
* `search_lat.cpp` — the enumeration program of the search (modes: given v, `kor`, and `search N seed`, which
  re-runs an exhaustive or random search over v = (x, −1); the search mode uses 10 threads and is not needed for the
  check).
* `audit_jit.cpp` — the audit's independent enumeration (shell-wise box enumeration with exact stopping rule).
* `run_programs.py` — driver (no mathematics of its own): runs both programs on every row of `check_vectors.tsv` and on
  the Korobov vectors, and compares with the stored values.
* `audit2_jit.cpp` + `audit2_run.sh` — a second audit implementation, with the exhaustive maximum over all x for the
  rows marked E.
* `box_check.py` — the third program: for a claimed value L it enumerates the box |b_c| ≤ 1 + ⌊√L⌋ (every lattice
  vector with ljit-value ≤ L lies in it), written from the definitions.
* `full_box_brute.py` — the additional brute force over the full box |b_c| ≤ 6 for s = 4, p = 1009.

## Re-run (from the archive root)

    python3 residue_tables/run_programs.py
    mkdir -p bin && g++ -O2 -std=c++17 -o bin/audit2_jit residue_tables/audit2_jit.cpp && sh residue_tables/audit2_run.sh
    python3 residue_tables/box_check.py
    python3 residue_tables/full_box_brute.py 1009 443,201,758,1008 6

Expected: `run_programs.py` and `box_check.py` end with `ALL OK` (every stored ljit² and the Korobov value (ρ − 1)²
reproduced); `audit2_run.sh` prints the same ljit² for the listed vectors and the Korobov vectors, and in its last
block the exhaustive maxima for the E rows, equal to the stored ljit² (the printed argmax may be a different vector
with the same value); the brute force prints `jit2=25 at (-5, 1, -4, -1)`.

Requirements: Python 3, a C++17 compiler. Programs compile into `bin/`.

Not archived: the random searches that found the R rows (they only produced data; e.g. `bin/search_lat 10007 3 search 3000000 1`
re-runs a random search of the same size, multi-threaded, and is not part of the check).

Last run 2026-10-29: PASS, 1.3 s + 1.6 s + < 0.1 s + < 0.1 s (one core).
