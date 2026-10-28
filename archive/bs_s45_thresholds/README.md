# bs_s45_thresholds/ — thresholds of the explicit staggered rule in dimensions four and five

Supports: the thresholds quoted after `thm:A` for s = 4, 5 (quoted, not part of its proof): s = 4: p_0 = 1.44·10¹⁶,
C = 32 044; s = 5: p_0 = 1.98·10²¹, C = 2.73·10⁹ (both rounded up). Listed in Table `tab:ca`; per Appendix
`app:verification` they rest on one program and the Lean kernel (Appendix `app:lean`); the spot checks below are an
additional, partial check above p_0.

Programs:
* `constants.py` (+ `bs_rule.py`, the explicit rule as exact rationals) — the authors' evaluation of the predicate 𝒫
  of `prop:P0` and of p_0, C by exact bisection on the monotone predicate.
* `sNaudit.py` — the audit's independent spot check at one prime above p_0 (own design from `lem:R`, crosses in F_p,
  the covering numbers, `lem:W`, and the exact window certificate over all steps).

## Re-run (from the archive root)

    python3 -B bs_s45_thresholds/constants.py 4 153 7/250 0
    python3 -B bs_s45_thresholds/constants.py 5 99 23/1000 4
    uv run --with sympy python bs_s45_thresholds/sNaudit.py 4 0 153 7/250 14300000000000021
    uv run --with sympy python bs_s45_thresholds/sNaudit.py 5 4 99 23/1000 1980000000000000000041

Expected: `p0=1.431e+16  C=32044.1` (s = 4; the exact bisection endpoint is 14 314 526 192 182 751, quoted rounded up
as 1.44·10¹⁶) and `p0=1.978e+21  C=2722234324.5` (s = 5); the spot checks print
`exact window LB^2*p^2 == (p-Mb)^2: True` with M_b = 31913 (s = 4) resp. 2719574398 (s = 5), i.e. exact LB = 1 − M_b/p
below the quoted C. Note: `sNaudit.py` reads the prime through a float, so the second call checks the prime
1 980 000 000 000 000 000 019 (printed), not the argument as typed. `rerun_2026-10-27.txt`: output of the previous run.

Requirements: Python 3; SymPy for `sNaudit.py`.

Last run 2026-10-29: PASS, < 0.1 s + < 0.1 s + 0.2 s + 0.2 s (one core).
