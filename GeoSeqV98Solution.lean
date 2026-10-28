/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Rel
public import GeoSeq.V98Count
public import GeoSeq.V98Rigid
public import GeoSeq.V98Cor
public import GeoSeq.V98SS
public import GeoSeq.V98Dim

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V98)
-/

#print axioms GeoSeq.dvd_of_locRes
#print axioms GeoSeq.wadic_unique
#print axioms GeoSeq.frDigit_vecPoly
#print axioms GeoSeq.place_eq
#print axioms GeoSeq.place_eq_locRes
#print axioms GeoSeq.relForm_eq_res
#print axioms GeoSeq.relPoly_degree_lt
#print axioms GeoSeq.relPoly_eq_zero_iff
#print axioms GeoSeq.relPoly_eval
#print axioms GeoSeq.relPoly_eval_ne_iff
#print axioms GeoSeq.relSpace_of_degree
#print axioms GeoSeq.relPoly_add
#print axioms GeoSeq.relPoly_smul
#print axioms GeoSeq.reltype_poly_surj
#print axioms GeoSeq.reltype_dim
#print axioms GeoSeq.count_key
#print axioms GeoSeq.count_refined
#print axioms GeoSeq.count
#print axioms GeoSeq.rigid
#print axioms GeoSeq.rows_skel
#print axioms GeoSeq.residuerows
#print axioms GeoSeq.residuerows_prop
#print axioms GeoSeq.nodesign
#print axioms GeoSeq.nodesign_no_design
#print axioms GeoSeq.count_ge
#print axioms GeoSeq.layer_a
#print axioms GeoSeq.layer_b
#print axioms GeoSeq.layer_c
#print axioms GeoSeq.N1_count
#print axioms GeoSeq.density
#print axioms GeoSeq.onerel_dim
#print axioms GeoSeq.blockrel
#print axioms GeoSeq.ssL_digit
#print axioms GeoSeq.ssL_scramble
#print axioms GeoSeq.onerel_poly
#print axioms GeoSeq.ssL_const
#print axioms GeoSeq.onerel_skel
#print axioms GeoSeq.residuerows_ss
#print axioms GeoSeq.onerel_stag
#print axioms GeoSeq.onerel_stag_gen
#print axioms GeoSeq.onerel_no_both
