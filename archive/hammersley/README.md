# hammersley/ — the Hammersley lifts of `sec:hammersley`

Supports:
1. The exact separations quoted in `sec:hammersley` (the comparison paragraph after `prop:liftcarry`, Figure
   `fig:hammersley`): the toroidal separation c = δ(P̂_m) N^{1/(s+1)} of the Hammersley lift
   P̂_m = {(i/p^m, x_i) : i < p^m} of the Faure sequence, the brick wall (`def:WF`, θ = −1/4), the residue sequence with
   a Korobov vector (`cor:korobov`, θ = 1) and the block-periodic sequence of `thm:block`(a) (s = 2) or (b) (s = 3), and
   of the staggered residue sequence with dyadic weights (s = 3), for the (p, m) of `lift_results.csv` (183 rows,
   N = p^m ≤ 2.5·10⁷; columns: construction, s, p, m, d = s + 1, c, the minimum inside one slab `c_inslab` and the slab
   depth K0 = ⌊m/(s+1)⌋, the closest pair (i, j), |i − j|, exactness flag). The figure reads the same file
   (`paper/scripts/data/lift_results.csv`).
2. The statement after the comparison that at p = 5, m = 9, 10 the exact closest pairs of the brick-wall, residue and
   block-periodic lifts are pairs of `prop:liftcarry` (l = 4; k = 4, or k = 5 for the residue and block-periodic
   lifts at m = 10; three across the torus boundary).
3. A check of `prop:liftcarry` on explicit pairs: the two lifted points of the pair of its proof, computed exactly
   (rational arithmetic), are at most the bound of the display apart, with the constant of the proposition
   (order k at 0, p^r − 1 at 1, p^r at the other roots of unity), for places {0, 1} (s = 2, up to m = 50),
   {0, 1, −1} and μ_3 ⊂ F_7, μ_3 ⊂ F_13 (s = 3).

`prop:liftslab` and `prop:liftcarry` themselves are proved in the text (and formalized, Appendix `app:lean`); the
computations here are illustrations and checks, not part of a proof.

Programs:
* `gen_lift.py` — generator matrices of the lifts (coordinate 0 = the matrix reversing the m index digits, then the
  generator matrices of the sequence), in the input format `p d m R` + d·R rows of m entries. Uses `b3_gen.py`
  (residue formulas of `def:residuestar`, `def:residue`; brick wall) and `audit_gen.py` (block-periodic sequences,
  Pascal matrices), unchanged copies of `paper/scripts/b3_gen.py`, `paper/scripts/audit_gen.py`.
* `liftsep.cpp` — exact toroidal separation of a digital point set (grid cell list; reports `exact=yes` when the
  minimum is certified by the cell size), with the split into pairs inside one slab and across slabs.
* `brute_check.py` — independent all-pairs computation (integer arithmetic, NumPy), small N only.
* `verify_pair.py` — the pair of the proof of `prop:liftcarry`, both points computed exactly, against the bound
  (exit status 0 iff PASS); also the minimum over the pairs (i + u, j + u), u < p^k.
* `check_lift.py` — driver: recomputes the rows of `lift_results.csv` with `liftsep` (mode `sep`) or `brute_check.py`
  (mode `brute`), and decodes the closest pairs (mode `pairs`).

## Re-run (from the archive root)

    mkdir -p bin && g++ -O2 -std=c++17 -o bin/liftsep hammersley/liftsep.cpp
    python3 hammersley/check_lift.py sep 0 1e5                    # 116 rows,  5 s
    python3 hammersley/check_lift.py sep 1e5 1e6                  #  38 rows, 27 s
    python3 hammersley/check_lift.py sep 1000001 5e6              #  22 rows, 46 s
    python3 hammersley/check_lift.py sep 5000001 1e7              #   4 rows (p = 5, m = 10), 33 s
    python3 hammersley/check_lift.py sep 1e7 3e7 blk              #   1 row (p = 17, m = 6), 16 s; also bw, res
    uv run --with numpy python hammersley/check_lift.py brute 4000   # 70 rows (N ≤ 4000), 5 s
    python3 hammersley/check_lift.py pairs
    python3 hammersley/verify_pair.py faure 5 2 50 25 2            # CONSTR p s m k r [places], places default 0..s-1
    python3 hammersley/verify_pair.py bw 5 2 10 4 1                # also: res 5 2 9 4 1; res 5 2 10 5 1; blk 5 2 10 5 1
    python3 hammersley/verify_pair.py faure 7 3 21 0 1 1 2 4       # mu_3 in F_7 (k = 0)
    python3 hammersley/verify_pair.py res 7 3 21 7 1 0 1 6         # places 0, 1, -1; also faure, stag
    python3 hammersley/verify_pair.py faure 13 3 39 0 1 1 3 9      # mu_3 in F_13
    python3 hammersley/b3_gen.py                                   # self-test of the residue generator

Expected (run of 2026-10-30, one core): every `sep` and `brute` line ends in `0 differ` (183 rows by `liftsep`, the
70 smallest also by the all-pairs program); `pairs`: 6 rows, all pairs of the proposition, k = 4 except residue and
block-periodic at m = 10 (k = 5), across the torus boundary for residue m = 9, 10 and block-periodic m = 9; every
`verify_pair.py` line ends in `PASS` (for example `c_pair(u=0)=0.134670 … bound=0.237063` for μ_3 ⊂ F_7, m = 21,
against the closed form √(3+49)·7^{−7/4} = 0.239 of `prop:liftcarry`; `min over 625 u: 0.117294` for the residue lift
at m = 9, its exact separation). The self-test prints `True`, `True`, `0`, `0`.

Scope: the rows of `lift_results.csv` only (the comparison in the paper is an illustration over this computed range).
`liftsep` measures every coordinate toroidally, the index coordinate included, as the nets paper does.
