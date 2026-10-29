/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Dens
public import GeoSeq.V10_1Joint
public import GeoSeq.V10_1Blk
public import GeoSeq.V10_1Rand
public import GeoSeq.V10_1Shift
public import GeoSeq.V10_1Misc
public import GeoSeq.V10_1Sign
public import GeoSeq.V10_1Diag4
public import GeoSeq.V10_1Diag5

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V10_1)
-/

#print axioms GeoSeq.dens_ranges_bound
#print axioms GeoSeq.dens_ranges_eps
#print axioms GeoSeq.dens_ranges_limsup
#print axioms GeoSeq.layer_a_density
#print axioms GeoSeq.density_limsup
#print axioms GeoSeq.density_dens
#print axioms GeoSeq.density_skel_range
#print axioms GeoSeq.locRes_one_eval
#print axioms GeoSeq.dvd_of_locRes_low
#print axioms GeoSeq.joint_transfer_gen
#print axioms GeoSeq.cong_of_corrTrunc
#print axioms GeoSeq.joint_ii
#print axioms GeoSeq.gap_zero_small
#print axioms GeoSeq.axis_term
#print axioms GeoSeq.blk4_LB_eq
#print axioms GeoSeq.blk5_LB_attained
#print axioms GeoSeq.blk5_LB_eq_proof
#print axioms GeoSeq.blk5_LB_eq_of
#print axioms GeoSeq.close_lev
#print axioms GeoSeq.not_qu_comp_lev
#print axioms GeoSeq.hasGap_full
#print axioms GeoSeq.not_qu_comp_full
#print axioms GeoSeq.uMul_surj
#print axioms GeoSeq.genY_idxScr
#print axioms GeoSeq.polyIdx_idxPolyP
#print axioms GeoSeq.seqPoint_idxScr
#print axioms GeoSeq.idxScr_prefix
#print axioms GeoSeq.idxScr_not_qu
#print axioms GeoSeq.real_carry_le
#print axioms GeoSeq.badicDigit_sum
#print axioms GeoSeq.radInv_prefix
#print axioms GeoSeq.shift_pair
#print axioms GeoSeq.nonquD_props
#print axioms GeoSeq.shift_nonqu
#print axioms GeoSeq.residue_full
#print axioms GeoSeq.N1_offset
#print axioms GeoSeq.caSig_abs_le
#print axioms GeoSeq.ca_signclass
#print axioms GeoSeq.gap_nonback_le
#print axioms GeoSeq.sc_LB
#print axioms GeoSeq.blk4d_signclass
#print axioms GeoSeq.blk4d_LB
#print axioms GeoSeq.blk4d_LB_eq
#print axioms GeoSeq.blk4d_hrel
#print axioms GeoSeq.blk4d_block
#print axioms GeoSeq.blk5d_signclass
#print axioms GeoSeq.blk5d_LB_proof
#print axioms GeoSeq.blk5d_LB_chk
#print axioms GeoSeq.blk5d_LB_attained
#print axioms GeoSeq.blk5d_LB_of
#print axioms GeoSeq.blk5d_LB_eq_of
#print axioms GeoSeq.blk5d_hrel
#print axioms GeoSeq.blk5d_block_gen
#print axioms GeoSeq.blk5d_block_of
#print axioms GeoSeq.blk5d_block_proof
