# lf_designs/ — archived ordered window systems for every prime (earlier version; not used in this paper)

Status: ordered window systems of an earlier version of this work (Appendix `app:archive`: "not used here"); no
statement of this paper depends on them.

Statement checked (earlier version): for s = 3, 4, 5 and every prime p ≥ 13 / 47 / 269 there is an ordered window
system (frame and θ from an explicit finite list, integer superdiagonal d, windows by `lem:ws`) with Γ < p, hence
sep(P_{sK}) ≥ (p − Γ)/p for all K; the archived system for every prime below the threshold of the closed-form rule is
stored here.

Files: `lf_designs_s3.txt` (every prime 13–113, 25 records), `lf_designs_s4.txt` (47–1913, 279), `lf_designs_s5.txt`
(269–20857, 2290), `lf_designs_s5_below269.txt` (239, 241, 251, 257). Record format: `verify/README.md` (with
`superdiag`, `order`, `frame ... theta`, `member` lines; `member` names the list member, e.g. `s5_faure12b` = Faure
frame with θ = 12). Provenance (not part of the check): the systems were selected from dense scans by an exhaustive
branch and bound over integer superdiagonals (research programs, not archived).

## Re-run (from the archive root)

    python3 verify/verify_designs.py lf_designs/lf_designs_s3.txt lf_designs/lf_designs_s4.txt
    python3 verify/verify_designs.py --range 0 400 lf_designs/lf_designs_s5.txt
    python3 verify/verify_designs.py --range 400 800 lf_designs/lf_designs_s5.txt
    python3 verify/verify_designs.py --range 800 1200 lf_designs/lf_designs_s5.txt
    python3 verify/verify_designs.py --range 1200 1600 lf_designs/lf_designs_s5.txt
    python3 verify/verify_designs.py --range 1600 2000 lf_designs/lf_designs_s5.txt
    python3 verify/verify_designs.py --range 2000 2400 lf_designs/lf_designs_s5.txt
    python3 verify/verify_designs.py lf_designs/lf_designs_s5_below269.txt

Expected: `## TOTAL 304/304 PASS`, then 400/400 (five times), 290/290 and 4/4 PASS (s = 5: column 4 by the `lem:ws`
certificate, smaller columns exact for p ≤ 1414). Outputs of the last run: `verify/results/lf_*.txt`.

Requirements: Python 3, a C++ compiler (for `verify/cover_helper`).

Last run 2026-10-29: PASS (2598/2598 records), 16.6 s (s = 3, 4, incl. compilation), 13.8 / 0.6 / 1.1 / 1.6 / 2.0 /
2.2 s (s = 5 chunks), 0.1 s (one core).
