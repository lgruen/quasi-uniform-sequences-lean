/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_5Slab
public import GeoSeq.V10_5Carry
public import GeoSeq.V10_5SlabInst

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V10_5)
-/

#print axioms GeoSeq.nat_div_eq_iff
#print axioms GeoSeq.lift_first_box
#print axioms GeoSeq.liftNet0_of_seq0
#print axioms GeoSeq.revMat_mulVec
#print axioms GeoSeq.coordE_revMat
#print axioms GeoSeq.coordE_truncGen
#print axioms GeoSeq.liftNet0_iff
#print axioms GeoSeq.liftslab_i
#print axioms GeoSeq.slab_mem
#print axioms GeoSeq.liftslab_ii
#print axioms GeoSeq.torDist2_cons_ge
#print axioms GeoSeq.slab_sep
#print axioms GeoSeq.liftD_identity
#print axioms GeoSeq.liftD_dvd
#print axioms GeoSeq.idxPolyP_of_digits
#print axioms GeoSeq.idxPolyP_carryJ
#print axioms GeoSeq.idxPolyP_carryI
#print axioms GeoSeq.idxPolyP_carry_diff
#print axioms GeoSeq.genY_scrGen
#print axioms GeoSeq.genY_scrGen_vanish
#print axioms GeoSeq.torCoord_sq_le
#print axioms GeoSeq.torDist2_sq
#print axioms GeoSeq.liftDelta_le_pair
#print axioms GeoSeq.liftPtSh_zero
#print axioms GeoSeq.liftcarry_pair
#print axioms GeoSeq.liftcarry_sharp
#print axioms GeoSeq.liftcarry
#print axioms GeoSeq.ord_term
#print axioms GeoSeq.sum_ord_le
#print axioms GeoSeq.liftcarry_closed0
#print axioms GeoSeq.liftcarry_closedMu
#print axioms GeoSeq.norm_of_mul
#print axioms GeoSeq.liftcarry_closed0_norm
#print axioms GeoSeq.liftcarry_closedMu_norm
#print axioms GeoSeq.liftcarry_gamma0
#print axioms GeoSeq.liftcarry_gammaMu
#print axioms GeoSeq.exists_r_small
#print axioms GeoSeq.lift_not_wellsep
#print axioms GeoSeq.lift01_not_wellsep
#print axioms GeoSeq.lift_resSeq01_not_wellsep
#print axioms GeoSeq.lift_resStar01_not_wellsep
#print axioms GeoSeq.cert_prime_shift
#print axioms GeoSeq.cert_one_shift
#print axioms GeoSeq.cert_row_shift
#print axioms GeoSeq.lift_scale
#print axioms GeoSeq.residuestar_sep_shift
#print axioms GeoSeq.block_sep_shift
#print axioms GeoSeq.slab_residuestar
#print axioms GeoSeq.slab_residue
#print axioms GeoSeq.slab_residue_ljit
#print axioms GeoSeq.slab_block
