# bs_ruleB_s3/ — the explicit staggered rule in dimension three

Supports: `thm:A3` (the predicate 𝒫 of `prop:P0` at p_0 = 19 673 600) and `rem:A3range` (the hypotheses of
`prop:steer` and `lem:W`, crosses computed in F_p, at the 1 035 877 primes in [3·10⁶, 1.97·10⁷], with
sep ≥ 1 − 779/p). Listed in Table `tab:ca`; `thm:A3` is also checked in the Lean development (Appendix `app:lean`).
No data files: the rule is in closed form.

Programs:
* `pi_check.py` — the audit's independent evaluation of 𝒫(p) (exact Fractions) for rule A (p_0 = 1 789 760) and rule B
  (p_0 = 19 673 600, the rule of `thm:A3`): 𝒫(p_0) true, 𝒫(0.99 p_0) false, and no true → false change on a geometric
  grid 10⁴ ... 10¹⁴.
* `indep_range.cpp` — the audit's per-prime checker: crosses in F_p from the gauge, forced crosses, the covering numbers,
  `lem:W`, and an exact window certificate computed independently of `lem:W`.

## Re-run (from the archive root)

    python3 bs_ruleB_s3/pi_check.py
    mkdir -p bin && g++ -O2 -std=c++17 -o bin/indep_range bs_ruleB_s3/indep_range.cpp
    ./bin/indep_range B 3000000 11000000 3000000
    ./bin/indep_range B 11000000 19700000 3000000

Expected: `B Pi(p0)= (True, (742.35..., ...)) Pi(0.99 p0)= False` and 0 flips; the two ranges report
`primes=509701 fails=0` and `primes=526176 fails=0` (together 1 035 877 primes), `LemmaW>exact count=0`, and
max (1 − LB)p = 779 at p = 3 078 857 (first range) resp. 746 (second range).
`range_rerun_2026-10-27.txt`: the output of the previous run (identical).

Requirements: Python 3 (standard library), a C++17 compiler.

Last run 2026-10-29: PASS, 0.1 s + 1.9 s (incl. compilation) + 1.4 s (one core).
