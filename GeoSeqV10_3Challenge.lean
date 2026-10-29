/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/

module
public import GeoSeq.Statements.V10_3

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V10_3)

The statements `GeoSeq/Statements/V10_3.lean`: prime-power bases (stage V10-3): explicit models of `F_q = F_p[x]/(f)` with the power-basis code; `prop:primepower` (soundness of the one-digit certificate for every finite field and every digit code, proved once; the 13 rows of `tab:primepower` by kernel evaluation); `thm:coverage` with the prime-power rows; `sec:fail` over `F_q` with any digit code having a carry pair (`lem:carrypair`, `thm:nonqu`, `eq:carrydigit` for every natural identification, `cor:unscrambled`, `cor:faure`, `cor:nied` for prime powers). Compared theorems: `comparatorGeoSeqV10_3.json`
(the formalization notes of the research repository (stage V10-3)).
-/
