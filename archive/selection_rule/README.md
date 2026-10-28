# selection_rule/ — the greedy selection rule and the window systems of the figure sequences

Supports: the rule of `rem:steerrule` (deterministic choice among the admissible own values, `prop:depthdir` +
`prop:LI`(c); any admissible choice keeps the window certificate by `prop:steer`), and the window systems of the
sequences shown in the figures. Not a computer-assisted proof item: the rule changes only the actual point set, never
the certified bound.

Files:
* `steer_rule.cpp` (uses `common/hd_common.h`) — steering with deterministic selection. Mode `lb1` is the rule of
  `rem:steerrule`: at depth 1 maximise the exact `lem:cert` (j = 1) certificate of the actual level-1 responses over all
  combinations of admissible own values (ties: most central, then larger own value, columns in order); deeper: most
  central admissible own value. Other modes (`cenhi`, `cenlo`, `near0`, `psimin`, `force:...`) are the rules compared
  in `rem:steerrule`.
* `hv_dump.cpp` — rebuilds the generator matrices from the steered law, checks the direct level-K law against the
  steering and t = 0, and dumps the matrices; `bs_mind.cpp` (+ `bs_common.h`) — exact minimum distance of P_3 from a dump.
* `cfg/` — window-system records of the figure sequences (`lf_s3_p13`, `lf_s3_p31`, `lf_s3_p101`, `lf_s4_p47`,
  `lf_s4_p127`: archived ordered systems; `mr_s3_p31`, `mrA_s3_p101`: closed-form ordered rules of the earlier version);
  format `verify/README.md`.
* `bs2steer.py` — converts a brick-star record of the research build programs to this format (not needed for the check).

## Re-run (from the archive root)

    python3 verify/verify_designs.py selection_rule/cfg/*.cfg
    mkdir -p bin && g++ -O2 -std=c++17 -o bin/steer_rule selection_rule/steer_rule.cpp && g++ -O2 -std=c++17 -o bin/hv_dump selection_rule/hv_dump.cpp && g++ -O2 -std=c++17 -o bin/bs_mind selection_rule/bs_mind.cpp
    ./bin/steer_rule selection_rule/cfg/lf_s3_p31.cfg 40 bin/x lb1
    ./bin/hv_dump bin/x 3 1,2 6 0 8 3 bin/x_dump.txt
    ./bin/bs_mind bin/x_dump.txt

Expected: `## TOTAL 7/7 PASS`; `lb1: depth-1 actual LB_1 = 0.652379`, `never stuck, violations 0`;
`27/27 law responses agree; t=0 rank-deficient compositions: 0`; `R=8 digits: net(one point per cell)=yes
sep(P_3) = 0.679259`.

Not archived: the comparison of 35 cases quoted in `rem:steerrule` (research runs; the modes above re-run any case)
and the generator dumps and separation data of the figures (illustration only).

Requirements: Python 3, a C++17 compiler.

Last run 2026-10-29: PASS, 0.1 s + 2.4 s (compilation and pipeline) (one core).
