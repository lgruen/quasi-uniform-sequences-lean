/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V94Seq
public import GeoSeq.V94Thm
public import GeoSeq.V94Dyadic
public import GeoSeq.V94WF

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V94)
-/

#print axioms GeoSeq.resStar_apply
#print axioms GeoSeq.resStar_apply_ne
#print axioms GeoSeq.resStar_apply_self
#print axioms GeoSeq.resStar_digit
#print axioms GeoSeq.resStarL_diag_ne
#print axioms GeoSeq.resStarL_diag_self
#print axioms GeoSeq.resStar_t0
#print axioms GeoSeq.resStar_rel
#print axioms GeoSeq.resStar_rel_shift
#print axioms GeoSeq.resStar_rel_seq
#print axioms GeoSeq.resStar_carry
#print axioms GeoSeq.cert_row
#print axioms GeoSeq.residuestar_sep
#print axioms GeoSeq.residuestar_allN
#print axioms GeoSeq.residuestar_mesh
#print axioms GeoSeq.residuestar_qu
#print axioms GeoSeq.signed_pow_two_ne_zero
#print axioms GeoSeq.abs_signed_pow_two_lt
#print axioms GeoSeq.cabsZ_ge_of_mul
#print axioms GeoSeq.exists_small_step
#print axioms GeoSeq.cabsZ_dyadic
#print axioms GeoSeq.betaStar_le_dyadic
#print axioms GeoSeq.betaStar_dyadic
#print axioms GeoSeq.betaStar_pos_imp
#print axioms GeoSeq.stdOrder_inj
#print axioms GeoSeq.stdOrder_lt
#print axioms GeoSeq.dyadic_qu
#print axioms GeoSeq.resStar_faure_ss
#print axioms GeoSeq.resStar_congr
#print axioms GeoSeq.brick_ss
#print axioms GeoSeq.brickWall_eq_WFgen
#print axioms GeoSeq.brickWall_C0
#print axioms GeoSeq.brickWall_C1
#print axioms GeoSeq.brickWall_WF
