/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V97Corr
public import GeoSeq.V97Sep
public import GeoSeq.V97Shift
public import GeoSeq.V97Joint

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V97)
-/

#print axioms GeoSeq.ssResGen_t0
#print axioms GeoSeq.ssRes_corr
#print axioms GeoSeq.ssRes_corr_seq
#print axioms GeoSeq.ssRes_modify
#print axioms GeoSeq.corrTrunc_modify
#print axioms GeoSeq.ljitB_ge
#print axioms GeoSeq.corrected
#print axioms GeoSeq.corrected_sepAtPrefix
#print axioms GeoSeq.shift_skel_rel
#print axioms GeoSeq.shift_skel_sep
#print axioms GeoSeq.shift_residue
#print axioms GeoSeq.joint_col
#print axioms GeoSeq.joint_step
#print axioms GeoSeq.joint_transfer
#print axioms GeoSeq.joint_window
#print axioms GeoSeq.joint_minkowski
#print axioms GeoSeq.joint_iii
