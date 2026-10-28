/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V99Gen
public import GeoSeq.V99Blk4
public import GeoSeq.V99Blk5
public import GeoSeq.V99Cov

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V99)
-/

#print axioms GeoSeq.hrel_of_eval
#print axioms GeoSeq.hNd_of_ndPoly
#print axioms GeoSeq.dom_LB
#print axioms GeoSeq.caCheck_sound
#print axioms GeoSeq.blk4_hrel
#print axioms GeoSeq.blk4_hNd
#print axioms GeoSeq.blk4_LB_proof
#print axioms GeoSeq.blk4_LB_chk
#print axioms GeoSeq.blk4_LB_ca
#print axioms GeoSeq.blk4_LB_ca109
#print axioms GeoSeq.blk4_block
#print axioms GeoSeq.blk5_hrel
#print axioms GeoSeq.blk5_hNd
#print axioms GeoSeq.blk5_LB_proof
#print axioms GeoSeq.blk5_LB_chk
#print axioms GeoSeq.prefix_of_level
#print axioms GeoSeq.hasGap_sN
#print axioms GeoSeq.covered_of_level
#print axioms GeoSeq.covered_full
#print axioms GeoSeq.covered_sq
#print axioms GeoSeq.cov_dyadic
#print axioms GeoSeq.cov_residue
