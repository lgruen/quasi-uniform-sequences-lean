# p7_graph_certificate/ — base seven in dimension three

Supports: `thm:p7` (Appendix `app:p7`): for any frame, μ and θ, the scramble steered by the archived certificate
gives c(P_{3K}) ≥ 1/7 for every K. Listed in Table `tab:ca` ("no vanishing combination in LB(w), 5 classes of steps,
≤ 7⁶ combinations each"); the statement is also checked in the Lean development (Appendix `app:lean`).

Data: `G_sym_p7.json` (the certificate: the table w found by a SAT solver).

Programs (two for the finite check of Table `tab:ca`, LB(w) ≥ 1/7, which does not depend on the frame; a third for the
archived instance):
* `code/verify_cert3.py` — first program; uses only `t3d_audit/alib3.py` (the auditor's from-the-definitions library:
  generator matrices, law, t-value, certificate). It checks the conditions of the graph rule, LB(w) over all 26 steps
  and all triples of the table, and rebuilds a witness sequence (places = the cube roots of unity 1, 2, 4 in F_7,
  θ = 1), which it writes to the file given as last argument (with its series Q in `.Q.json`);
  `J3_p7_graph_reference.txt` is the reference copy of that witness, and `J3_p7_graph_rebuilt.txt` (+ `.Q.json`) the
  output of the last run.
* `code/audit_cert.cpp` — second program (the audit's own code): LB(w) = min over all 26 steps and all choices of a
  triple of the table in every moving column; it does not use the frame.
* `code/li3.cpp` — third program: the bound LB_K from the actual responses of the archived instance (cube roots of
  unity, θ = 1, the series Q of the witness), computed from the level-independent law (`prop:LI`), for K = 1..140.
  LB_K is a minimum over carry lengths ≤ K, hence non-increasing in K.
* `code/run_programs.py` — driver for the second and third programs.

## Re-run (from the archive root)

    python3 p7_graph_certificate/code/verify_cert3.py p7_graph_certificate/G_sym_p7.json 0.1428 300 6 15 6 20 p7_graph_certificate/J3_p7_graph_rebuilt.txt
    cmp p7_graph_certificate/J3_p7_graph_rebuilt.txt p7_graph_certificate/J3_p7_graph_reference.txt
    mkdir -p bin && g++ -O2 -std=c++17 -o bin/audit_cert p7_graph_certificate/code/audit_cert.cpp && g++ -O2 -std=c++17 -o bin/li3 p7_graph_certificate/code/li3.cpp
    python3 p7_graph_certificate/code/run_programs.py

Expected: `ALL CHECKS PASSED` (law = partial sums for K ≤ 6, t = 0 for m ≤ 15, certificate LB_K = 0.1429 ≥ τ); `cmp`
prints nothing (rebuilt witness byte-identical to the reference); `run_programs.py` prints `minS 1  LB 0.142857` for
the second program and, for the third, LB_K = 0.3499, 0.2020, 0.2020 for K = 1, 2, 3 and LB_K = 0.1429 (= 1/7 to the
digits printed) for K = 4 and K = 140, hence for every 4 ≤ K ≤ 140 (the statement of `app:p7` for the archived
instance).

The SAT search that found the table is not archived; the Lean proof is part of the Lean development.

Requirements: Python 3, a C++17 compiler.

Last run 2026-10-29: PASS, 0.9 s + 1.3 s (compilation and both programs) (one core).
