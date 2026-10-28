/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Gen
public import GeoSeq.V95Sobol
public import GeoSeq.V95SobolPair
public import GeoSeq.V95Nied
public import GeoSeq.V95Rate

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V95)
-/

#print axioms GeoSeq.genY_lin
#print axioms GeoSeq.pas_sum
#print axioms GeoSeq.scrY_lin
#print axioms GeoSeq.scrY_isBAdic
#print axioms GeoSeq.smul_isRadInv
#print axioms GeoSeq.taylor_isBAdic
#print axioms GeoSeq.badicDigit_scaled
#print axioms GeoSeq.scaledFrame_isRadInv
#print axioms GeoSeq.seqPoint_eq_linPt
#print axioms GeoSeq.not_qu_of_close
#print axioms GeoSeq.close_comp
#print axioms GeoSeq.not_qu_comp
#print axioms GeoSeq.gray_injective
#print axioms GeoSeq.gray_surj
#print axioms GeoSeq.unscrambled
#print axioms GeoSeq.unscrambled_frame
#print axioms GeoSeq.sobolDir_lt
#print axioms GeoSeq.scol_rec
#print axioms GeoSeq.scol_rec_t
#print axioms GeoSeq.sobY_mul_b
#print axioms GeoSeq.sobY_low
#print axioms GeoSeq.sobol_pi_unitri
#print axioms GeoSeq.sobol_radInv
#print axioms GeoSeq.vdc_radInv
#print axioms GeoSeq.sobol_not_qu
#print axioms GeoSeq.sobol_proj
#print axioms GeoSeq.sobol_primitive
#print axioms GeoSeq.polyIdx_add_two
#print axioms GeoSeq.sobol_pair
#print axioms GeoSeq.niedY_lin
#print axioms GeoSeq.nied_isBAdic
#print axioms GeoSeq.nied_top
#print axioms GeoSeq.nied_digit
#print axioms GeoSeq.niedPi_onto
#print axioms GeoSeq.nied_radInv
#print axioms GeoSeq.classical_cong
#print axioms GeoSeq.classical_ind
#print axioms GeoSeq.monic_irred_coprime
#print axioms GeoSeq.niedGen_not_qu
#print axioms GeoSeq.nied_not_qu
#print axioms GeoSeq.faureD_taylor
#print axioms GeoSeq.faureD_dvd_c1
#print axioms GeoSeq.faureD_dvd
#print axioms GeoSeq.faureD_natDegree
#print axioms GeoSeq.faurerate
#print axioms GeoSeq.faurerate_sep
