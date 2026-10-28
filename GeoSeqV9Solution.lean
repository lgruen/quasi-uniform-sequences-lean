/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Res
public import GeoSeq.V9Seq
public import GeoSeq.V9Prefix
public import GeoSeq.V9Thm
public import GeoSeq.V9Kor
public import GeoSeq.V9QU

@[expose] public section

/-!
# Solution (geoseq paper V4, stages V9-1, V9-2)
-/

#print axioms GeoSeq.res_thm
#print axioms GeoSeq.res_thm_of_deg
#print axioms GeoSeq.res_thm_zero
#print axioms GeoSeq.locRes_one
#print axioms GeoSeq.taylor_coeff_vecPoly
#print axioms GeoSeq.scrGen_res
#print axioms GeoSeq.polarNum_eval
#print axioms GeoSeq.scrGen_res_polar
#print axioms GeoSeq.resSeq_apply
#print axioms GeoSeq.resSeq_digit
#print axioms GeoSeq.resL_diag
#print axioms GeoSeq.resSeq_t0
#print axioms GeoSeq.resSeq_skel
#print axioms GeoSeq.resSeq_skel_zero
#print axioms GeoSeq.resSeq_skel_top
#print axioms GeoSeq.resSeq_skel_shift
#print axioms GeoSeq.resSeq_skel_seq
#print axioms GeoSeq.prefix_sep_gap
#print axioms GeoSeq.prefix_mesh_gap
#print axioms GeoSeq.hasGap_sN1
#print axioms GeoSeq.prefix_sep_sN1
#print axioms GeoSeq.prefix_mesh_sN1
#print axioms GeoSeq.residue_cells
#print axioms GeoSeq.residue_sep
#print axioms GeoSeq.residue_sep_ljit
#print axioms GeoSeq.residue_sepAtPrefix
#print axioms GeoSeq.le_ljit
#print axioms GeoSeq.ljit_le
#print axioms GeoSeq.korRho_pow_le
#print axioms GeoSeq.lt_korRho_succ_pow
#print axioms GeoSeq.korRho_pow_lt
#print axioms GeoSeq.korRho_two_le_iff
#print axioms GeoSeq.korRho_three_le_iff
#print axioms GeoSeq.korobov_ne_zero
#print axioms GeoSeq.korobov_lat
#print axioms GeoSeq.korobov_jit
#print axioms GeoSeq.korobov_ljit
#print axioms GeoSeq.korobov_sep
#print axioms GeoSeq.korobov_sepAtPrefix
#print axioms GeoSeq.korobov_forms
#print axioms GeoSeq.residue_allN
#print axioms GeoSeq.residue_mesh
#print axioms GeoSeq.small_vec
#print axioms GeoSeq.jit_exists_iff
#print axioms GeoSeq.faurePlace_injective
#print axioms GeoSeq.resSeq_faure_apply
#print axioms GeoSeq.residue_korobov
#print axioms GeoSeq.torDistR_eq
#print axioms GeoSeq.torDist2_le_euclDist
#print axioms GeoSeq.seqPoint_mem
#print axioms GeoSeq.covRadIdx_le
#print axioms GeoSeq.sepDistIdx_ge
#print axioms GeoSeq.qu_of_sepAllN
#print axioms GeoSeq.residue_qu
#print axioms GeoSeq.residue_korobov_explicit
