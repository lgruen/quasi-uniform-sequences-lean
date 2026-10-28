/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S11Res
public import GeoSeq.S11Series
public import GeoSeq.EBasis
public import GeoSeq.LIa
public import GeoSeq.LIconv
public import GeoSeq.ConvChar2

@[expose] public section

/-!
# Solution (geoseq paper, stage S11): Appendix C machinery
-/

#print axioms GeoSeq.residue2
#print axioms GeoSeq.tRoot_add_sq
#print axioms GeoSeq.gamF_zero
#print axioms GeoSeq.gamF_one
#print axioms GeoSeq.gamF_odd
#print axioms GeoSeq.gamF_subst_wD
#print axioms GeoSeq.coeff_change
#print axioms GeoSeq.gam_expand
#print axioms GeoSeq.ebas_B_exists
#print axioms GeoSeq.ebas_T_exists
#print axioms GeoSeq.ebas_indep
#print axioms GeoSeq.B_diag_ne
#print axioms GeoSeq.residue_thm
#print axioms GeoSeq.residue_faure
#print axioms GeoSeq.residue_decomp
#print axioms GeoSeq.ebasis
#print axioms GeoSeq.ebas_eq_w
#print axioms GeoSeq.ebas_eq_x
#print axioms GeoSeq.LI_a
#print axioms GeoSeq.LI_a_B
#print axioms GeoSeq.scrGen_eq_ssGen_iff
#print axioms GeoSeq.LIconv
#print axioms GeoSeq.N2a_LI
#print axioms GeoSeq.convchar2
#print axioms GeoSeq.convchar2_exists
