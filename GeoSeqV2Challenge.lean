/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V2

@[expose] public section

/-!
# Challenge (geoseq paper V3, stage V2)

The V2 statements (`GeoSeq/Statements/V2.lean`): `lem:lex` and `rem:lexexact` (ordered windows), `lem:lexcover`,
`lem:ws` (general `k`), `lem:cauchy`, the local roots of the Faure frame, the arithmetic and the crosses of
`def:MR`, `thm:MR`, and the example `ex:MR101` (non-vacuity with `LB = 28/101`).
Compared theorems: `comparatorGeoSeqV2.json` (the formalization notes of the research repository).
-/
