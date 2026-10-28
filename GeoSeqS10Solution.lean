/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.N1
public import GeoSeq.Rational
public import GeoSeq.N2
public import GeoSeq.FrameLaw
public import GeoSeq.FrameLI
public import GeoSeq.Rank2
public import GeoSeq.Composite
public import GeoSeq.CompositeB
public import GeoSeq.Dual
public import GeoSeq.DualThm
public import GeoSeq.DualBC
public import GeoSeq.LemH

@[expose] public section

/-!
# Solution (geoseq paper, stage S10): structural results
-/

#print axioms GeoSeq.box_existsUnique
#print axioms GeoSeq.N1_general
#print axioms GeoSeq.N1
#print axioms GeoSeq.isRat_partial
#print axioms GeoSeq.evPeriodic_isRat
#print axioms GeoSeq.no_rat_root
#print axioms GeoSeq.N2a
#print axioms GeoSeq.N2a_periodic
#print axioms GeoSeq.N2b
#print axioms GeoSeq.N2b_periodic
#print axioms GeoSeq.frame_factor
#print axioms GeoSeq.frame_factor_F
#print axioms GeoSeq.freeSer_const
#print axioms GeoSeq.coeff_dir
#print axioms GeoSeq.LI_c
#print axioms GeoSeq.depthdir
#print axioms GeoSeq.freeSer_free
#print axioms GeoSeq.freeSer_row
#print axioms GeoSeq.LI_d
#print axioms GeoSeq.cover
#print axioms GeoSeq.law_coef_exists
#print axioms GeoSeq.rank2
#print axioms GeoSeq.rank2_indep
#print axioms GeoSeq.composite_a
#print axioms GeoSeq.composite_a4
#print axioms GeoSeq.composite_c
#print axioms GeoSeq.composite_s4
#print axioms GeoSeq.composite_b
#print axioms GeoSeq.isSeq0_of_kernel
#print axioms GeoSeq.dual_kernel
#print axioms GeoSeq.dual_fail
#print axioms GeoSeq.dual_a
#print axioms GeoSeq.dual_p3
#print axioms GeoSeq.dual_b_example
#print axioms GeoSeq.dual_b
#print axioms GeoSeq.dual_c
#print axioms GeoSeq.lemH_core
#print axioms GeoSeq.lemH
