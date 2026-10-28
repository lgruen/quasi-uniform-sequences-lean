/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V93Poly
public import GeoSeq.V93Carry
public import GeoSeq.V93Thm
public import GeoSeq.V93Halton

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V9-3)
-/

#print axioms GeoSeq.badicDigit_add
#print axioms GeoSeq.badicDigit_base
#print axioms GeoSeq.badicDigit_succ
#print axioms GeoSeq.badicDigit_high
#print axioms GeoSeq.badicDigit_pow_mul
#print axioms GeoSeq.badicDigit_run
#print axioms GeoSeq.badicDigit_congr
#print axioms GeoSeq.runS_mul
#print axioms GeoSeq.runS_ne_zero
#print axioms GeoSeq.idxPolyP_polyIdx
#print axioms GeoSeq.polyIdx_lt
#print axioms GeoSeq.polyIdx_injective
#print axioms GeoSeq.real_prefix
#print axioms GeoSeq.real_carry
#print axioms GeoSeq.IsRadInv.isBAdic
#print axioms GeoSeq.carrydigit_prime
#print axioms GeoSeq.carrypair
#print axioms GeoSeq.carrypair_sep
#print axioms GeoSeq.exists_pow_sub_one_dvd
#print axioms GeoSeq.nonqu_exists
#print axioms GeoSeq.nonqu_excess
#print axioms GeoSeq.nonqu_pair
#print axioms GeoSeq.nonqu_sep
#print axioms GeoSeq.linPt_mem
#print axioms GeoSeq.covRadIdx_ge
#print axioms GeoSeq.covRadIdx_ge_pow
#print axioms GeoSeq.nonqu
#print axioms GeoSeq.haltonY_lin
#print axioms GeoSeq.haltonY_radInv
#print axioms GeoSeq.haltonPt_eq_linPt
#print axioms GeoSeq.halton_not_quasiUniform
#print axioms GeoSeq.halton_pair
#print axioms GeoSeq.taylor_coeff_eq_badicDigit
#print axioms GeoSeq.frame_eq_haltonPt
#print axioms GeoSeq.faure_not_quasiUniform
#print axioms GeoSeq.faureSeq_not_quasiUniform
