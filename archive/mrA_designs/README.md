# mrA_designs/ — closed-form ordered rule MR-A below its threshold (earlier version; not used in this paper)

Status: ordered window systems of an earlier version of this work (Appendix `app:archive`: "not used here"); no
statement of this paper depends on them. The records are checked by the common verifier `verify/`.

Statement checked (earlier version): the closed-form rule MR-A (Faure frame, θ = (s−1)!/g, heights
h_t = max(1, round(γ_t u)), windows by `lem:ws`) gives a digital (0,s)-sequence with sep(P_{sK}) ≥ (p − Γ)/p for every
prime p ≥ 41 (s = 3), ≥ 557 (s = 4), ≥ 6421 (s = 5): proof for p ≥ P_1 (`p1_certificates/`) and the finite check below
P_1 here.

Files: `mrA_designs_s3.txt` (every prime 41–61), `mrA_designs_s4.txt` (557–887), `mrA_designs_s5.txt` (6421–8053): one
record per prime (format: `verify/README.md`; with a `heights` line). `code/mrA_range.cpp` (uses `common/hd_common.h`)
applies rule MR-A to every prime of a range (s = 6, 7; not stored).

## Re-run (from the archive root)

    python3 verify/verify_designs.py mrA_designs/mrA_designs_s3.txt mrA_designs/mrA_designs_s4.txt mrA_designs/mrA_designs_s5.txt
    mkdir -p bin && g++ -O2 -std=c++17 -o bin/mrA_range mrA_designs/code/mrA_range.cpp
    ./bin/mrA_range 6 1800 860700 | tail -1
    ./bin/mrA_range 7 14600000 53300000 | tail -1
    uv run --with sympy python p1_certificates/mrA.py 6 281034 860700 | tail -1

Expected: `## TOTAL 237/237 PASS`; s = 6: last failure 281 033 (rule works on [281 053, 860 700]); s = 7: last failure
14 642 741, first success 14 642 759, no failure up to 5.33·10⁷; the independent implementation: 0 failures on
[281 034, 860 700]. With P_1(6) = 860 654 and P_1(7) = 5.32·10⁷: MR-A at every prime ≥ 281 053 (s = 6) and
≥ 14 642 759 (s = 7).

Requirements: Python 3, a C++17 compiler, SymPy (cross-check only).

Last run 2026-10-29: PASS, 4.3 s + 0.7 s + 10.3 s + 0.9 s (one core).
