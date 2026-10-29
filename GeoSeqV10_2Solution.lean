/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_2Res
public import GeoSeq.V10_2Form
public import GeoSeq.V10_2SS
public import GeoSeq.V10_2Corr

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V10_2)
-/

#print axioms GeoSeq.coeff_pow_derivative
#print axioms GeoSeq.res_basis
#print axioms GeoSeq.reschange
#print axioms GeoSeq.locU_subst
#print axioms GeoSeq.ssMul_digit
#print axioms GeoSeq.ssMul_locMul
#print axioms GeoSeq.locMul_ssMul
#print axioms GeoSeq.constantCoeff_locMul
#print axioms GeoSeq.constantCoeff_ssMul
#print axioms GeoSeq.locRoots_exists
#print axioms GeoSeq.locRoots_unique
#print axioms GeoSeq.scrGen_eq_frDigit
#print axioms GeoSeq.frDigit_congr
#print axioms GeoSeq.ssL_eq_ssGen
#print axioms GeoSeq.ssGen_eq_ssL
#print axioms GeoSeq.selfsim_frDigit
#print axioms GeoSeq.selfsim_scrGen
#print axioms GeoSeq.selfsim_locMul_unit
#print axioms GeoSeq.resform_b
#print axioms GeoSeq.ssL_selfsim
#print axioms GeoSeq.resSeq_selfsim
#print axioms GeoSeq.resStar_selfsim
#print axioms GeoSeq.relSpace_congr
#print axioms GeoSeq.selfsim_relSpace
#print axioms GeoSeq.onerel_poly_selfsim
#print axioms GeoSeq.onerel_skel_selfsim
#print axioms GeoSeq.residuerows_selfsim
#print axioms GeoSeq.onerel_stag_selfsim
#print axioms GeoSeq.ssResGen_truncN
#print axioms GeoSeq.corrRel_congr
#print axioms GeoSeq.carry_congr
#print axioms GeoSeq.corrTrunc_of_PS
#print axioms GeoSeq.corrV_eq
#print axioms GeoSeq.corrCoef_zero
#print axioms GeoSeq.corrTruncPS_corrCoef
#print axioms GeoSeq.corr_free
#print axioms GeoSeq.corr_inj
#print axioms GeoSeq.selfsim_corr_of
#print axioms GeoSeq.selfsim_corrS
#print axioms GeoSeq.selfsim_joint_step
#print axioms GeoSeq.selfsim_joint_ii
