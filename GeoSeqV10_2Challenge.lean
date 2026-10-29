/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.V10_2

@[expose] public section

/-!
# Challenge (geoseq paper V4, stage V10_2)

The statements `GeoSeq/Statements/V10_2.lean`: the change of variable in a residue (`lem:reschange`, every commutative ring, via the char-free core `[t^m] nu^m = [t^(m-1)] nu^(m-1) (d/dt nu)`), `lem:resform`(b) (self-similar scrambles as written in `def:selfsim` <=> local multipliers, `g <-> phi` mutually inverse, local roots exist and are unique), and bridges: `prop:onerel`, `cor:residuerows`, `lem:residue-t0`, `def:residuestar`, `lem:corrS`, `prop:joint` (i), (ii) for `def:selfsim` as written. Compared theorems: `comparatorGeoSeqV10_2.json`
(the formalization notes of the research repository (stage V10-2)).
-/
