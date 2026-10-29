/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V10_5

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V10_5)

The statements `GeoSeq/Statements/V10_5.lean`: Hammersley lifts (stage V10-5, `sec:hammersley`): `prop:liftslab`(i) (the lift of a digital `(0,s)`-sequence is a `(0,m,s+1)`-net, box form and digital form with the reversal matrix first), (ii) (a slab is a digitally shifted prefix; in-slab bounds for the staggered residue, residue and block-periodic sequences via the shifted certificates); `prop:liftcarry` (the Frobenius identity, the orders of vanishing, the carry pair, the general bound in sharp and in the paper's form, the closed forms at `m = s p^r` with the sharper constant `sqrt(s+p^2)` and the paper's constants, not well separated for places `{0} u mu_(s-1)`, `mu_s`, `{0,1}`). Compared theorems: `comparatorGeoSeqV10_5.json`
(the formalization notes of the research repository (stage V10-5)).
-/
