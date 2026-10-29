/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V10_1

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V10_1)

The statements `GeoSeq/Statements/V10_1.lean`: side clauses (stage V10-1): the `limsup` clauses of `cor:layer`(a) and `cor:density` (covering by admissible ranges), `prop:joint`(ii) for a general local multiplier, equality in `thm:block`(c) for `s = 4, 5` (the binding axis step, every prime), `rem:randomize` (a) digital shifts, (b) index scrambles, (c) reorderings keeping a level family, `rem:residuefull` (inclusion bound), the offset-map phrasing of `cor:N1`; the sign-class bound and the block designs with the smaller free diagonal (`s = 4`: `1 - 4/p`, `p >= 11`; `s = 5`: `1 - 8/p`, `p >= 67`, and `p >= 23` given the kernel evaluations). Compared theorems: `comparatorGeoSeqV10_1.json`
(the formalization notes of the research repository (stage V10-1)).
-/
