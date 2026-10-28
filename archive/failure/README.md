# failure/ — the close pairs of the classical sequences

Supports: Table `tab:sobolpar` (orders ν, k and the levels L_1, m_1 of the close pairs of `cor:sobol`, s = 2, ..., 7,
and the rounded-up bound column) and the explicit pairs of `sec:fail`: `lem:carrypair`/`thm:nonqu` on Halton-type
sequences (`cor:halton`, including non-monic and reducible bases), `cor:faure`, `cor:sobol`, `cor:unscrambled`,
`rem:faurerate`, `rem:toeplitz`, and `thm:nonqu` over F_4. Listed in Table `tab:checks` ("second program"; "exact
distances of the pairs"). The prime-base statements of `sec:fail` are also formalized in the Lean development
(Appendix `app:lean`).

Programs (audit programs, written from the statements):
* `check_f4_sobol.py` (+ `ff.py`) — recomputes `tab:sobolpar` (Sobol' polynomials z, z+1, z²+z+1, z³+z+1, z³+z²+1,
  z⁴+z+1, z⁴+z³+1: ν, k = 2^j, L_1, m_1, (s−1)E, bound rounded up to three digits), Lemma S1 (`lem:sobol`) on random
  direction numbers, the explicit `cor:sobol` pairs (both indices < 2^m, squared distance below the bound), the F_4
  pairs, and the `rem:toeplitz` witness. No Sobol' direction-number file is needed: the pairs do not depend on the
  direction numbers.
* `check_fail.py` (+ `ff.py`) — explicit pairs for Halton-type frames (irreducible, non-monic, reducible bases), the
  Faure-type frames, `cor:unscrambled` and `rem:faurerate`, with exact distances (Fractions).
* `u3.cpp`, `gen3.cpp`, `camp3.sh`, `campaign.sh` — the audit's campaign behind `cor:halton`: `gen3` draws random frames
  of given base degrees (modes: random non-monic; reducible with a repeated factor; a pure power of a linear factor;
  many linear factors), `u3` builds the pair of `thm:nonqu` directly from the formula, checks the carry and zero digit
  patterns from the definition of the radical inverse, the degrees, and the exact Euclidean distance against √(s+3)
  (levels w = 0, 1 with L ≤ 12000); `campaign.sh P` runs the profiles of the audit campaign for the prime P.

## Re-run (from the archive root)

    python3 failure/check_f4_sobol.py
    python3 failure/check_fail.py
    bash failure/campaign.sh 2      (then 3, 5, 7, 11, 13; one prime per call)

Expected: every line of the two scripts ends with `True`; `tab:sobolpar recomputed` lists s = 2..7 with
(E, ν, k, L, m, (s−1)E) = (1, 2, 2, 3, 5, 1), (2, 12, 16, 34, 98, 4), (6, 168, 256, 1542, 6150, 18),
(6, 168, 256, 1542, 7686, 24), (12, 1680, 2048, 24588, 147468, 60), (12, 1680, 2048, 24588, 172044, 72) and bounds
1.58114, 0.972081, 0.116927, 0.101532, 0.00292969, 0.00253333 (the table rounds up to two significant digits:
1.59, 0.98, 0.12, 0.11, 2.93·10⁻³, 2.54·10⁻³). `campaign.sh` ends with `TOTAL p=P ...: cases=n pass=n fail=0`
(a case is `notrun` when its level exceeds L = 12000; that is not a failure).

Negative control: `CTRL=1 ./bin/u3 3 '0,0,1;2,2,2;2,1,2' 0 1 12000` (N replaced by N − 1; `CTRL=2`: k by k + 1) makes the
checker report `RESULT FAIL` with distances far above the bound.

Result of the run of 2026-10-29 (count 2, seed 1 per profile): 244 cases, 243 PASS, 0 FAIL, 1 not run (p = 7, level
above 12000). GAP: the audit campaign quoted in Table `tab:checks` (395 cases of bases and carrying coordinate,
0 failures) drew its frames at random and did not store them, so exactly those 395 cases cannot be replayed; the archived
campaign re-draws frames of the same profiles (any count and seed: `bash failure/campaign.sh P COUNT SEED`). The second,
independent pipeline used in that campaign is a research program and is not archived (`camp3.sh` skips it).

Requirements: Python 3, a C++17 compiler, bash.

Last run 2026-10-29: PASS, 0.1 s + 0.6 s; campaign 10.4 / 1.9 / 3.2 / 6.3 / 2.7 / 11.1 s for p = 2, 3, 5, 7, 11, 13
(one core).
