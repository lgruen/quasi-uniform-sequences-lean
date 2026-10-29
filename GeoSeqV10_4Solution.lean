/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4Num
public import GeoSeq.V10_4Trans
public import GeoSeq.V10_4Main
public import GeoSeq.V10_4S6

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V10_4)
-/

#print axioms GeoSeq.triF_zero_above
#print axioms GeoSeq.triF_coeff
#print axioms GeoSeq.triF_unique
#print axioms GeoSeq.triF_expand
#print axioms GeoSeq.poly_zero_of_nodes
#print axioms GeoSeq.designNum_exists
#print axioms GeoSeq.designNum_unique
#print axioms GeoSeq.designNum_order
#print axioms GeoSeq.designNd_spec
#print axioms GeoSeq.ustarA_injective
#print axioms GeoSeq.ustarV_ne
#print axioms GeoSeq.wN_transfer
#print axioms GeoSeq.yN_transfer
#print axioms GeoSeq.reach_of_netsForm
#print axioms GeoSeq.ustar_reachable
#print axioms GeoSeq.ustar_hrel
#print axioms GeoSeq.ustar_hNd
#print axioms GeoSeq.ustar_Nd_unique
#print axioms GeoSeq.aStar_ge
#print axioms GeoSeq.ustar_LB_proof
#print axioms GeoSeq.blkS_block
#print axioms GeoSeq.ustar_col0
#print axioms GeoSeq.blkS_axis
#print axioms GeoSeq.blkS_LB_eq_of
#print axioms GeoSeq.ustarDiag_hrel
#print axioms GeoSeq.blkSd_block
#print axioms GeoSeq.blkSd_block_sc
#print axioms GeoSeq.reach_block
#print axioms GeoSeq.blk6d_chk_of
#print axioms GeoSeq.blk6d_signclass_of
#print axioms GeoSeq.blk6G_deg
#print axioms GeoSeq.blk6d_netsForm
#print axioms GeoSeq.blk6d_reach
#print axioms GeoSeq.blk6d_LB_of_chk
#print axioms GeoSeq.axis_term_depth
#print axioms GeoSeq.blk6d_LB_eq_of_chk
#print axioms GeoSeq.blk6d_block_of_chk
