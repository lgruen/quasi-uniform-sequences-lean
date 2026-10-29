# block_lb/ — the one-digit relaxation LB(F) of the block-periodic designs (`thm:block`(c), (d))

Supports:
* `thm:block`(c) below its proof range — the exact value LB(F) = 1 − (a*_s + 1)/p of the designs U*_4 (a*_4 = 5) and
  U*_5 (a*_5 = 16) at every prime 7 ≤ p ≤ 109 (s = 4) and 19 ≤ p ≤ 109 (s = 5), computed from `lem:cert` (j = 1, carry
  lengths capped at s − 1). Listed in Table `tab:ca`; verification described in Appendix `app:verification`.
* `thm:block`(d) (the free diagonal; rows of Table `tab:block` with δ; Figure `fig:freediag`) — (a) the hypothesis of
  `lem:signclass` with A = 3, 7, 14, 59 and S = 8, 23, 46, 211 for s = 4, 5, 6, 7, hence LB(F) ≥ 1 − (A+1)/p for every
  prime p ≥ 23, 67, 127, 587 (the first primes at or above the integer thresholds 22, 63, 125, 579); (b) exact LB(F) below these
  primes: 1 − 4/p at every prime 11 ≤ p ≤ 19 and √3/7 at p = 7 (s = 4); 1 − 8/p at every prime 23 ≤ p ≤ 61 and 1/11,
  3/13, 3√5/17, √101/19 at p = 11, 13, 17, 19 (s = 5); 1 − 15/p at every prime 37 ≤ p ≤ 113 and LB > 0 at every
  prime 17 ≤ p ≤ 31 (s = 6); 1 − 60/p at every prime 191 ≤ p ≤ 577 and LB > 0 at p = 17, 19, 23 and every prime
  31 ≤ p ≤ 181 (s = 7). Each by two programs (Table `tab:ca`). The checks run beyond these ranges (s = 4, 5 up to 109,
  s = 6 up to 131, s = 7 up to 593), so the exact range overlaps the range of `lem:signclass`; they also print the
  primes without a claim (LB = 0 at p = 7, 11, 13 for s = 6 and at p = 11, 13, 29 for s = 7).
* the data check of U*_4, ..., U*_7 in `app:verification`: the files agree with an independent implementation of the
  definition of U*_s in [Gru26geo], which reproduces a*_s = 5, 16, 43, 170 and the largest off-diagonal entries
  2, 6, 14, 86 listed there; reachability at the places 0, 1, 1/2, ..., 1/(s−1) with v = (1, 1, 2, ..., s−1) by exact
  interpolation over Q (every γ_{c,n} of exact degree n; only the primes 2, 3, 5 in denominators and leading
  coefficients).
* the optimality remark after the proof of `thm:block`(d) (lower block of `tab:ca`): with the off-diagonal entries of
  U*_s fixed and the deeper diagonals 0, no δ ∈ [0,A]^s satisfies the hypothesis of `lem:signclass` with A ≤ 2, 6, 13
  for s = 4, 5, 6 (exhaustive in this scope; an axis step forces 0 ≤ δ_c ≤ A, so [0,A]^s is the whole space, and the
  condition is monotone in A, so A = 2, 6, 13 suffice). For s = 7 the paper says "best found"; nothing is checked.
* the cases of `thm:coverage` that rest on `thm:block`(d): (d) s = 5, Lev = 25ℕ, every prime p ≥ 11 (p = 11, 13, 17,
  19 by the quoted exact values, 23 ≤ p ≤ 61 exactly, p ≥ 67 by `lem:signclass`; p ≥ 84 also by the written proof of
  (c)); (e) s = 6, Lev = 36ℕ, every prime p ≥ 17 (LB > 0 at 17 ≤ p ≤ 31, exact 1 − 15/p at 37 ≤ p ≤ 113, p ≥ 127 by
  `lem:signclass`) and s = 7, Lev = 49ℕ, p = 17, 19, 23 and every prime p ≥ 31 (LB > 0 at 17, 19, 23, 31 ≤ p ≤ 181,
  exact 1 − 60/p at 191 ≤ p ≤ 577, p ≥ 587 by `lem:signclass`). The reachability these cases also need is that of
  `thm:block`(c), checked for s = 6, 7 by `ustar_reach.py`.
* the proof range p ≥ (3+√2)a*_s + 1 of `thm:block`(c) (from p = 191, 757 on for s = 6, 7) is arithmetic; the
  `signclass` driver prints it from the files.

Data:
* `ustar_finite.json` — the designs F_0, ..., F_{s−1} (s × s integer matrices; F_{s−1} = 0) of U*_s for s = 3..7 at the
  places 0, 1, 1/2, ..., 1/(s−1) with the multipliers v = (1, 1, 2, ..., s−1). Its s = 4 entries are the matrices
  printed after `thm:block` (asserted by `lbcheck_allR.py`). Used by the checks of (c) (s = 4, 5).
* `ustar4.txt` ... `ustar7.txt` — the same designs U*_4, ..., U*_7 in the input format of the C++ programs (s, then the
  s − 1 matrices F_0, ..., F_{s−2}, row by row); `ustar_compare.py` asserts that they equal `ustar_finite.json`.
* `freediag.txt` — the diagonals δ of `thm:block`(d): (3,3,3,3), (7,...,7), (3,12,13,14,13,13),
  (41,44,59,57,56,6,32). The design has the off-diagonal entries of U*_s, F_0[c][c] = −δ_c, F_n[c][c] = 0 for n ≥ 1.

Programs for (c) (the first two written from `lem:cert`; all three read the designs from `ustar_finite.json`):
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

Programs for (d) (all read `ustar<s>.txt`; the diagonal is passed on the command line):
* `fd_lb_audit.cpp` — exact LB(F), written by the audit of the Lean stage: all steps up to sign, carry depths 0..s−2,
  the term of a coordinate from a table of f_1 by the minimum over all positions R (p ≤ 3000); prints (p·LB)² as the
  integer `sumsq`.
* `fd_signclass_audit.cpp` — the same audit: A(δ) (the least A in the hypothesis of `lem:signclass`, with integer
  changes σ), S = max_i Σ_c max_j |M^(j)[i][c]| and the integer threshold (least p > S with (p−A−1)² ≤ 2(p−S−1)²).
* `fd_diag.cpp` — the program of the Lean stage that found the diagonals: mode `A` (A(δ) over the distinct step
  classes; it reports the steps without any backward coordinate), mode `lb` (exact LB(F), the term from the closed form
  of f_1; prints `sumsq`), mode `csp` (exhaustive depth-first search over δ ∈ [0,A]^s). Its other modes (heuristic
  search, further decision procedures) are not used here.
* `fd_opt_audit.cpp` — the audit's exhaustive backtracking over δ ∈ [0,A]^s (the second optimality program; the same
  depth-first order as `fd_diag csp`, written independently; both report the same node counts).
* `fd_s45_check.py` — the program of the Lean stage for s = 4, 5 (its own copy of U*_4, U*_5, equal to the files; checked):
  LB(F) at the primes 5..109 and five larger primes, rounded to 3 decimals, and the hypothesis of `lem:signclass`
  (number of violating steps, S, threshold), also for U*_4, U*_5 with their own diagonal. A third evaluation for
  s = 4, 5; needs SymPy (`primerange`).
* `run_freediag.py` — driver: runs the compiled programs on `freediag.txt` and compares with the paper's values (it
  also recomputes S and the threshold from their formulas).
* `ustar_independent.py` — an independent implementation of def:Ustar of [Gru26geo] (written by an audit of the nets
  paper; exact rationals, own integer kernel, own lead functional, Babai rounding with ties up); `ustar_compare.py`
  compares the files with it (and with `ustar_finite.json`) and prints a*_s and the largest entry; `ustar_reach.py`
  checks reachability by exact interpolation over Q.

The free diagonal changes only the diagonal of F_0; reachability involves only off-diagonal entries, so the
reachability of (c) applies (proof of `thm:block`(d)).

## Re-run (from the archive root)

(c):

    python3 block_lb/lbcheck_allR.py
    python3 block_lb/lbF.py 4 7 109
    python3 block_lb/lbF.py 5 19 109
    python3 block_lb/run_third.py          (or: python3 block_lb/run_third.py all)

(d), after compiling (`mkdir -p bin && for x in fd_lb_audit fd_signclass_audit fd_diag fd_opt_audit; do
g++ -O2 -std=c++17 -o bin/$x block_lb/$x.cpp; done`):

    python3 block_lb/run_freediag.py signclass
    python3 block_lb/run_freediag.py lb audit 4 7 109       (and: lb audit 5 11 109; lb audit 6 7 131)
    python3 block_lb/run_freediag.py lb diag 4 7 109        (and: lb diag 5 11 109; lb diag 6 7 131)
    python3 block_lb/run_freediag.py lb audit 7 11 181      (and: lb audit 7 191 593)
    python3 block_lb/run_freediag.py lb diag 7 11 61        (and the ranges 67 131, 137 181, 191 283, 293 389, 397 491,
                                                             499 593: about 2.2 s per prime, so split for one minute)
    uv run --with sympy python block_lb/fd_s45_check.py
    python3 block_lb/ustar_compare.py
    python3 block_lb/ustar_reach.py block_lb/ustar7.txt     (and ustar4.txt, ustar5.txt, ustar6.txt)
    for a in "4 2" "5 6" "6 13" "4 3" "5 7" "6 14"; do set -- $a; ./bin/fd_opt_audit block_lb/ustar$1.txt $2;
        ./bin/fd_diag block_lb/ustar$1.txt csp $2 1; done

Expected, (c): `lbcheck_allR.py` prints `LB(F) = 1-(a*+1)/p at every prime 7..109: yes` (s = 4), the same for 19..109
(s = 5), and `ALL OK`; `lbF.py` prints one line per prime, all `OK reach True` (26 primes for s = 4, 22 for s = 5);
`run_third.py` prints one `OK` line per prime, `9/9 primes OK` (s = 4) and `15/15 primes OK` (s = 5), and `ALL OK`
(with `all`: 26/26 and 22/22).

Expected, (d): `signclass` prints for s = 4, 5, 6, 7: A = 3, 7, 14, 59 by both programs (no step without a backward
coordinate), S = 8, 23, 46, 211, thresholds p ≥ 22, 63, 125, 579, first primes 23, 67, 127, 587, `OK`, then
(3+√2)a*_s + 1 = 23.07, 71.63, 190.81, 751.42 (first primes 29, 73, 191, 757) and `ALL OK`. Each `lb` run prints one
line per prime with (p·LB)², LB, p − p·LB and the claim, and a summary `k/k claimed values OK`: s = 4: 26/26
(p = 7: (p·LB)² = 3, LB = √3/7 = 0.247436); s = 5: 25/25 ((p·LB)² = 1, 9, 45, 101 at p = 11, 13, 17, 19); s = 6: 26/26
(p − p·LB = 16, 17.5858, 19.1270, 17.7750, 16.7873 at p = 17, 19, 23, 29, 31; LB = 0 at 7, 11, 13, no claim); s = 7:
35/35 on 11..181 (LB = 0 at 11, 13, 29, no claim) and 66/66 on 191..593, both programs (the `diag` chunks 11/11, 14/14,
10/10, 19/19, 16/16, 17/17, 14/14). `fd_s45_check.py`: p − p·LB = 4.0 from p = 11 on and 5.268 at p = 7 (diagonal 3),
8.0 from p = 23 on and 10.0, 10.0, 10.292, 8.95 at p = 11, 13, 17, 19 (diagonal 7); 6.0 and 17.0 for U*_4, U*_5;
violating steps 0 in all four cases. `ustar_compare.py`: a* 5, 16, 43, 170, maxentry 2, 6, 14, 86, 0 entries differing,
`file == ustar_finite.json: True`, `ALL AGREE`; `ustar_reach.py`: 0 columns/depths with wrong degree, primes [2, 3]
(s = 4, 5) and [2, 3, 5] (s = 6, 7). Optimality: `none in [0,A]^s` and `CSP A=...: solutions=0` for (s, A) = (4, 2),
(5, 6), (6, 13); `FOUND` and `solutions=1+` for the controls (4, 3), (5, 7), (6, 14).

Negative controls (2026-10-29): a copy of `ustar_finite.json` with the largest diagonal entry of F_0 of U*_5 changed by
one (written to `bin/`) makes `lbcheck_allR.py` stop with `AssertionError: (5, 15)`; a copy of the files with one
off-diagonal entry of U*_7 changed by one (`bin/negu/`) makes `ustar_compare.py` report `entries differing from file: 1`,
`DIFFERENCES FOUND`, exit status 1.

The third evaluation for (c) reported in Table `tab:ca` was run in the research repository on designs produced by its
transfer program; the archived driver runs the same program on the archived designs instead. The programs for (d) are
those of the Lean stage and of its audit, as used for the paper; the only changes are paths in comments and an extra
output field `sumsq` (the integer minimum, already computed) in `fd_lb_audit.cpp` and `fd_diag.cpp` mode `lb`.

Requirements: Python 3, a C++17 compiler; SymPy for `fd_s45_check.py`.

Last run 2026-10-29: PASS. (c): 2.8 s + 0.1 s + 1.0 s + 4.1 s (with `all`: 6.1 s). (d): signclass 4.4 s; lb s = 4, 5, 6
0.8 s (audit) and 1.7 s (diag); lb s = 7 audit 13.4 s + 27.1 s; lb s = 7 diag 32.6 s, 32.4 s, 23.2 s, 44.0 s, 37.1 s,
39.4 s, 32.5 s; `fd_s45_check.py` 7.5 s; U*_s data check 0.1 s; optimality 1.5 s (one core).
