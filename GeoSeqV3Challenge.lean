/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V3

@[expose] public section

/-!
# Challenge (geoseq paper V3, stage V3)

The V3 statements (`GeoSeq/Statements/V3.lean`): `lem:MRbound`, `thm:MRall` (a)–(c) for every `s ≥ 3`, the
rational certificates and the tables `tab:P1` (`s = 3, …, 7`) and `tab:LFY`, the last column of `tab:P1`
(`s = 3, 4, 5`, range checker), `prop:lexcap`, `prop:lexmin`, `prop:tournament`, and a non-vacuity example.
Compared theorems: `comparatorGeoSeqV3.json` (the formalization notes of the research repository).
-/
