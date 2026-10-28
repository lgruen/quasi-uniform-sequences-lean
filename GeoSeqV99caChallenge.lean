/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V99ca

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V99ca)

The statements `GeoSeq/Statements/V99ca.lean`: `thm:block`(c) for `s = 5` from the kernel evaluations of the one-digit relaxation at the primes `19 ≤ p ≤ 83` (hypothesis `Blk5CA`; the evaluations are compared in `comparatorGeoSeqV99ca5a..d.json`): `sep(P_{25K}) ≥ 1 - 17/p` for every prime `p ≥ 19`. Compared theorems: `comparatorGeoSeqV99ca.json`
(the formalization notes of the research repository).
-/
