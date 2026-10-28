/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2Ex

@[expose] public section

/-!
# Solution (geoseq paper V3, stage V2)
-/

#print axioms GeoSeq.lex_bound
#print axioms GeoSeq.lex_cost
#print axioms GeoSeq.lex_exact_row
#print axioms GeoSeq.lex_exact
#print axioms GeoSeq.lex_eq
#print axioms GeoSeq.lex_eq_cost
#print axioms GeoSeq.lexcover_iff
#print axioms GeoSeq.lexcover_zero
#print axioms GeoSeq.lexcover_lattice
#print axioms GeoSeq.ws_pos
#print axioms GeoSeq.ws_cover
#print axioms GeoSeq.cauchy_mul
#print axioms GeoSeq.cauchy_super
#print axioms GeoSeq.cauchy_prod
#print axioms GeoSeq.exists_localRoot
#print axioms GeoSeq.faureW_monic
#print axioms GeoSeq.faureW_natDegree
#print axioms GeoSeq.faure_roots_exist
#print axioms GeoSeq.mrMu_mul
#print axioms GeoSeq.mrG_dvd
#print axioms GeoSeq.mrG_pos
#print axioms GeoSeq.mrMuBar_mul
#print axioms GeoSeq.faure_placeDer
#print axioms GeoSeq.MR_kap
#print axioms GeoSeq.MR_LB
#print axioms GeoSeq.MR_cond_i
#print axioms GeoSeq.MR_cond_ii
#print axioms GeoSeq.MR
#print axioms GeoSeq.MR_every
#print axioms GeoSeq.MR101
