# block_lb/ — the one-digit relaxation LB(F) of the designs U*_4, U*_5

Supports: `thm:block`(c) below its proof range — the exact value LB(F) = 1 − (a*_s + 1)/p of the designs U*_4
(a*_4 = 5) and U*_5 (a*_5 = 16) at every prime 7 ≤ p ≤ 109 (s = 4) and 19 ≤ p ≤ 109 (s = 5), computed from
`lem:cert` (j = 1, carry lengths capped at s − 1). Listed in Table `tab:ca`; verification described in Appendix
`app:verification`.

Data: `ustar_finite.json` — the designs F_0, ..., F_{s−1} (s × s integer matrices; F_{s−1} = 0) of U*_s for s = 3..7 at
the places 0, 1, 1/2, ..., 1/(s−1) with the multipliers v = (1, 1, 2, ..., s−1). Its s = 4 entries are the matrices
printed after `thm:block` (asserted by `lbcheck_allR.py`). Only s = 4, 5 are used here.

Programs (the first two written from `lem:cert`; all three read the designs from the same data file):
* `lbF.py` (+ helper `fp.py`) — first program: the term of a coordinate from the two possible differences of
  positions (two lifts); steps up to sign; prints, per prime, (p·LB)², the target (p − a* − 1)² and `OK`/`DIFF`, and a
  reachability check of the design at that prime (`reach True`).
* `lbcheck_allR.py` — second program: the term of a coordinate by the minimum over ALL positions R (a table per prime),
  both signs of the step; asserts that the s = 4 design equals the printed matrices and that the largest diagonal entry
  of F_0 is a*_s, so a design whose largest diagonal entry is changed by one is rejected.
* `lb.py` (+ `blockgen.py`, of which only the design loader is used) — third program: the program of the search, the
  one-digit relaxation with jitter 1 on every coordinate (variant `noH2`) and carry depths capped at s − 1, from the
  sums M^(j) = F_0 + ... + F_j; `run_third.py` (driver) evaluates it on the designs of `ustar_finite.json` at the primes
  named in Table `tab:ca` (7 ≤ p ≤ 31 and p = 101 for s = 4; 37 ≤ p ≤ 101 for s = 5), or with `all` at every prime of
  the range.

## Re-run (from the archive root)

    python3 block_lb/lbcheck_allR.py
    python3 block_lb/lbF.py 4 7 109
    python3 block_lb/lbF.py 5 19 109
    python3 block_lb/run_third.py          (or: python3 block_lb/run_third.py all)

Expected: `lbcheck_allR.py` prints `LB(F) = 1-(a*+1)/p at every prime 7..109: yes` (s = 4), the same for 19..109
(s = 5), and `ALL OK`; `lbF.py` prints one line per prime, all `OK reach True` (26 primes for s = 4, 22 for s = 5); `run_third.py` prints one `OK` line per prime, `9/9 primes OK`
(s = 4) and `15/15 primes OK` (s = 5), and `ALL OK` (with `all`: 26/26 and 22/22).

Negative control (2026-10-29): a copy of the data file with the largest diagonal entry of F_0 of U*_5 changed by one
(written to `bin/`) makes `lbcheck_allR.py` stop with `AssertionError: (5, 15)`.

The third evaluation reported in Table `tab:ca` was run in the research repository on designs produced by its transfer
program; the archived driver runs the same program on the archived designs instead.

Requirements: Python 3.

Last run 2026-10-29: PASS, 2.9 s + 0.1 s + 1.1 s + 4.4 s (with `all`: 6.6 s) (one core).
