/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V10_4

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V10_4)

The statements `GeoSeq/Statements/V10_4.lean`: `thm:block`(c) for every `s >= 3` (stage V10-4): `def:block`(a) from reachability over any field (existence, uniqueness, orders of vanishing), the transfer of the nets' design `U*_s` under `x -> 1/(x+1)` (from the formal `thm:A` reachability of `Z3Net/`), `a*_s >= s - 1`, the bound `1 - (a*_s+1)/p` for every prime `p >= 5 a*_s + 4`, the column of the place `0` (all ones) and the equality given `alpha_0 = a*_s`; the free diagonal for every `s` (sign-class form); the improved `s = 6` design (`U*_6` off the diagonal, diagonal `-(3,12,13,14,13,13)`): `1 - 15/p` for every prime `p >= 125` given the checker evaluation (compared separately, `comparatorGeoSeqV10_4ca<k>.json`). Compared theorems: `comparatorGeoSeqV10_4.json`
(the formalization notes of the research repository (stage V10-4)).
-/
