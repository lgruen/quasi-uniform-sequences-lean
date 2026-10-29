/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/

module
public import GeoSeq.V10_3Beta
public import GeoSeq.V10_3Fail
public import GeoSeq.V10_3Rows
public import GeoSeq.V10_3Cov

@[expose] public section

/-!
# Solution (geoseq paper V4, stage V10_3)
-/

#print axioms GeoSeq.mem_vecsOf
#print axioms GeoSeq.mem_vecsOfL
#print axioms GeoSeq.smul3_eq
#print axioms GeoSeq.ppCheck_spec
#print axioms GeoSeq.gapNum_one_ge
#print axioms GeoSeq.carryChange_const
#print axioms GeoSeq.pp_sep
#print axioms GeoSeq.primepower_of_check
#print axioms GeoSeq.coeff_idxPolyD
#print axioms GeoSeq.natDegree_idxPolyD
#print axioms GeoSeq.polyIdxD_digit
#print axioms GeoSeq.idxPolyD_polyIdxD
#print axioms GeoSeq.polyIdxD_lt
#print axioms GeoSeq.polyIdxD_injective
#print axioms GeoSeq.linPtD_polyIdxD
#print axioms GeoSeq.linPtD_mem
#print axioms GeoSeq.enc_eq_zero_iff
#print axioms GeoSeq.carrypairD
#print axioms GeoSeq.nonqu_existsD
#print axioms GeoSeq.nonqu_pairD
#print axioms GeoSeq.nonqu_code
#print axioms GeoSeq.geom_aux
#print axioms GeoSeq.val_neg_one_eq
#print axioms GeoSeq.carryPair_nat
#print axioms GeoSeq.PF.code_isNat
#print axioms GeoSeq.carryPair_pb
#print axioms GeoSeq.genY_idxD
#print axioms GeoSeq.seqPoint_eq_linPtD
#print axioms GeoSeq.unscrambledD
#print axioms GeoSeq.unscrambled_frameD
#print axioms GeoSeq.faure_code
#print axioms GeoSeq.niedGen_not_quD
#print axioms GeoSeq.nied_not_quD
#print axioms GeoSeq.pp_delta_s2_q8
#print axioms GeoSeq.primepower_s2_q8
#print axioms GeoSeq.pp_delta_s2_q9
#print axioms GeoSeq.primepower_s2_q9
#print axioms GeoSeq.pp_delta_s2_q16
#print axioms GeoSeq.primepower_s2_q16
#print axioms GeoSeq.pp_delta_s2_q25
#print axioms GeoSeq.primepower_s2_q25
#print axioms GeoSeq.pp_delta_s2_q27
#print axioms GeoSeq.primepower_s2_q27
#print axioms GeoSeq.pp_delta_s2_q49
#print axioms GeoSeq.primepower_s2_q49
#print axioms GeoSeq.pp_delta_s3_q25
#print axioms GeoSeq.primepower_s3_q25
#print axioms GeoSeq.pp_delta_s3_q32
#print axioms GeoSeq.primepower_s3_q32
#print axioms GeoSeq.pp_delta_s3_q49
#print axioms GeoSeq.primepower_s3_q49
#print axioms GeoSeq.pp_delta_s3_q64
#print axioms GeoSeq.primepower_s3_q64
#print axioms GeoSeq.pp_delta_s3_q81
#print axioms GeoSeq.primepower_s3_q81
#print axioms GeoSeq.pp_delta_s3_q121
#print axioms GeoSeq.primepower_s3_q121
#print axioms GeoSeq.pp_delta_s3_q125
#print axioms GeoSeq.primepower_s3_q125
#print axioms GeoSeq.covered_of_concl
#print axioms GeoSeq.PF.dec_fin_injective
#print axioms GeoSeq.coverage_pp_rows
#print axioms GeoSeq.coverage_pp_of_parts
