/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Res
public import GeoSeq.V96Sep
public import GeoSeq.V96Gap
public import GeoSeq.V96Inst
public import GeoSeq.V96Two
public import GeoSeq.V96Gauss

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V96)
-/

#print axioms GeoSeq.locRes_cancel_unit
#print axioms GeoSeq.locRes_cancel_pow
#print axioms GeoSeq.lagrange_one
#print axioms GeoSeq.pf_res
#print axioms GeoSeq.blockGen_vecPoly
#print axioms GeoSeq.blockNum_order
#print axioms GeoSeq.blockGen_t0
#print axioms GeoSeq.blockDig_own
#print axioms GeoSeq.blockDig_zero
#print axioms GeoSeq.blockGen_rel
#print axioms GeoSeq.blockGen_rel_seq
#print axioms GeoSeq.blockGen_skel
#print axioms GeoSeq.blockGen_implied
#print axioms GeoSeq.blockGen_carry
#print axioms GeoSeq.block_sep
#print axioms GeoSeq.skel_cells
#print axioms GeoSeq.skel_sep
#print axioms GeoSeq.skel_sepAtPrefix
#print axioms GeoSeq.gap_back
#print axioms GeoSeq.gap_fwd
#print axioms GeoSeq.cert_back1
#print axioms GeoSeq.cert_back3
#print axioms GeoSeq.blk2_good
#print axioms GeoSeq.blk2_block
#print axioms GeoSeq.blk3_good
#print axioms GeoSeq.blk3_block
#print axioms GeoSeq.blocktwo
#print axioms GeoSeq.implied_sep
#print axioms GeoSeq.hasGap_s2N
#print axioms GeoSeq.gauss_hrel_gen
#print axioms GeoSeq.gauss_LB
#print axioms GeoSeq.gauss_lattice
#print axioms GeoSeq.gauss_implied_gen
#print axioms GeoSeq.gauss
