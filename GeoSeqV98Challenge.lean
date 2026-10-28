/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V98

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V98)

The statements `GeoSeq/Statements/V98.lean`: counting exact digit relations (`sec:count`): `def:exactrel`, `lem:reltype` (polynomial of a relation, degree bound, injectivity, converse, dimension), `thm:count` (refined and depth form), `cor:layer` (a) range form, (b), (c), `cor:N1` (relation form, by the count), `cor:density` (range form), `prop:onerel` ((i) dimension for every scramble; (i) polynomial, (ii), (iii) for self-similar scrambles in residue form), `prop:blockrel` (for every scramble), `lem:rigid`, `cor:residuerows`, `cor:nodesign`. Compared theorems: `comparatorGeoSeqV98.json`
(the formalization notes of the research repository).
-/
