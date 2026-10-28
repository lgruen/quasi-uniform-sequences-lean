# p7_graph_certificate/ — base seven in dimension three

Supports: `thm:p7` (Appendix `app:p7`): for any frame, μ and θ, the scramble steered by the archived certificate
gives c(P_{3K}) ≥ 1/7 for every K. Listed in Table `tab:ca` ("no vanishing combination in LB(w), 5 classes of steps,
≤ 7⁶ combinations each"); the statement is also checked in the Lean development (Appendix `app:lean`).

Data: `G_sym_p7.json` (the certificate: the table found by a SAT solver). Verifier: `code/verify_cert3.py`, which
uses only `t3d_audit/alib3.py` (the auditor's from-the-definitions library: generator matrices, law, t-value,
certificate). The verifier rebuilds a witness sequence (places = the cube roots of unity 1, 2, 4 in F_7, θ = 1) and
writes it to the file given as last argument; `J3_p7_graph_reference.txt` is the reference copy of that witness, and
`J3_p7_graph_rebuilt.txt` (+ `.Q.json`) the output of the last run.

## Re-run (from the archive root)

    python3 p7_graph_certificate/code/verify_cert3.py p7_graph_certificate/G_sym_p7.json 0.1428 300 6 15 6 20 p7_graph_certificate/J3_p7_graph_rebuilt.txt
    cmp p7_graph_certificate/J3_p7_graph_rebuilt.txt p7_graph_certificate/J3_p7_graph_reference.txt

Expected: `ALL CHECKS PASSED` (law = partial sums for K ≤ 6, t = 0 for m ≤ 15, certificate LB_K = 0.1429 ≥ τ); `cmp`
prints nothing (rebuilt witness byte-identical to the reference).

Not archived: the other two programs of Table `tab:ca` for this item (research programs); the Lean proof is part of the
Lean development.

Requirements: Python 3.

Last run 2026-10-29: PASS, 0.9 s (one core).
