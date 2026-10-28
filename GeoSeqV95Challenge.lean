/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V95

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V95)

The statements `GeoSeq/Statements/V95.lean`: corollaries of `thm:nonqu` over prime fields: generator-matrix sequences as linear coordinates, scrambles (`cor:unscrambled`), reorderings and the Gray code (`rem:randomize`(b)), Sobol' sequences (`eq:sobrec`, `lem:sobol`, `cor:sobol` with explicit pairs), Niederreiter sequences (`lem:nied`, `cor:nied`) and `rem:faurerate`. Compared theorems: `comparatorGeoSeqV95.json`
(the formalization notes of the research repository).
-/
