/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S4Data
public import GeoSeq.K4Gap

@[expose] public section

/-!
# GeoSeq stage S8: the finite checks of the certificate of `thm:S4` (kernel `decide`)

The permuted change columns of the sources `1, 2, 3` (`s4_Zperm`), the completeness of the buckets
(`s4_bk3`, `s4_pb_*`), and the certificate checks `s4part`, `s4three`, `s4full` (used in
`GeoSeq/S4Cert.lean`).
-/

namespace GeoSeq

set_option Elab.async false

set_option maxRecDepth 100000 in
theorem s4_Zperm : ∀ c' : Fin 4, (S4Z c').length = 120 ∧ ∀ t : Fin 120, ∀ c : Fin 4,
    ((S4Z c').getD t []).getD c 0 = ((S4Z 0).getD t []).getD ((c : ℕ) ^^^ (c' : ℕ)) 0 ∧
    ((S4Z c').getD t []).getD c 0 < 1024 := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_bk3_0 : ∀ t : Fin 120, (S4Z 2).getD t [] ∈
    s4bk3 0 (((S4Z 2).getD t []).getD 0 0 / 32) (((S4Z 2).getD t []).getD 1 0 / 32) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_bk3_1 : ∀ t : Fin 120, (S4Z 3).getD t [] ∈
    s4bk3 1 (((S4Z 3).getD t []).getD 0 0 / 32) (((S4Z 3).getD t []).getD 1 0 / 32) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_bk3_2 : ∀ t : Fin 120, (S4Z 3).getD t [] ∈
    s4bk3 2 (((S4Z 3).getD t []).getD 0 0 / 32) (((S4Z 3).getD t []).getD 2 0 / 32) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_bk3_3 : ∀ t : Fin 120, (S4Z 3).getD t [] ∈
    s4bk3 3 (((S4Z 3).getD t []).getD 1 0 / 32) (((S4Z 3).getD t []).getD 2 0 / 32) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_pb_0 : ∀ t2 : Fin 120, 0 ≤ t2.val → t2.val < 30 → ∀ t3 : Fin 120,
    (List.range 4).map (fun c => ((S4Z 2).getD t2 []).getD c 0 ^^^ ((S4Z 3).getD t3 []).getD c 0) ∈
      (S4PB.getD ((((S4Z 2).getD t2 []).getD 0 0 ^^^ ((S4Z 3).getD t3 []).getD 0 0) / 32) []).getD
        ((((S4Z 2).getD t2 []).getD 1 0 ^^^ ((S4Z 3).getD t3 []).getD 1 0) / 32) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_pb_1 : ∀ t2 : Fin 120, 30 ≤ t2.val → t2.val < 60 → ∀ t3 : Fin 120,
    (List.range 4).map (fun c => ((S4Z 2).getD t2 []).getD c 0 ^^^ ((S4Z 3).getD t3 []).getD c 0) ∈
      (S4PB.getD ((((S4Z 2).getD t2 []).getD 0 0 ^^^ ((S4Z 3).getD t3 []).getD 0 0) / 32) []).getD
        ((((S4Z 2).getD t2 []).getD 1 0 ^^^ ((S4Z 3).getD t3 []).getD 1 0) / 32) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_pb_2 : ∀ t2 : Fin 120, 60 ≤ t2.val → t2.val < 90 → ∀ t3 : Fin 120,
    (List.range 4).map (fun c => ((S4Z 2).getD t2 []).getD c 0 ^^^ ((S4Z 3).getD t3 []).getD c 0) ∈
      (S4PB.getD ((((S4Z 2).getD t2 []).getD 0 0 ^^^ ((S4Z 3).getD t3 []).getD 0 0) / 32) []).getD
        ((((S4Z 2).getD t2 []).getD 1 0 ^^^ ((S4Z 3).getD t3 []).getD 1 0) / 32) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_pb_3 : ∀ t2 : Fin 120, 90 ≤ t2.val → t2.val < 120 → ∀ t3 : Fin 120,
    (List.range 4).map (fun c => ((S4Z 2).getD t2 []).getD c 0 ^^^ ((S4Z 3).getD t3 []).getD c 0) ∈
      (S4PB.getD ((((S4Z 2).getD t2 []).getD 0 0 ^^^ ((S4Z 3).getD t3 []).getD 0 0) / 32) []).getD
        ((((S4Z 2).getD t2 []).getD 1 0 ^^^ ((S4Z 3).getD t3 []).getD 1 0) / 32) [] := by decide +kernel

theorem s4_pb : ∀ t2 t3 : Fin 120,
    (List.range 4).map (fun c => ((S4Z 2).getD t2 []).getD c 0 ^^^ ((S4Z 3).getD t3 []).getD c 0) ∈
      (S4PB.getD ((((S4Z 2).getD t2 []).getD 0 0 ^^^ ((S4Z 3).getD t3 []).getD 0 0) / 32) []).getD
        ((((S4Z 2).getD t2 []).getD 1 0 ^^^ ((S4Z 3).getD t3 []).getD 1 0) / 32) [] := by
  intro t2
  have h : (0 ≤ t2.val ∧ t2.val < 30) ∨ (30 ≤ t2.val ∧ t2.val < 60) ∨ (60 ≤ t2.val ∧ t2.val < 90) ∨
      (90 ≤ t2.val ∧ t2.val < 120) := by omega
  rcases h with h | h | h | h
  · exact s4_pb_0 t2 (by omega) (by omega)
  · exact s4_pb_1 t2 (by omega) (by omega)
  · exact s4_pb_2 t2 (by omega) (by omega)
  · exact s4_pb_3 t2 (by omega) (by omega)

set_option maxRecDepth 100000 in
theorem s4_part0001 : s4part false false false true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part0010 : s4part false false true false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part0011 : s4part false false true true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part0100 : s4part false true false false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part0101 : s4part false true false true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part0110 : s4part false true true false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part1000 : s4part true false false false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part1001 : s4part true false false true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part1010 : s4part true false true false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_part1100 : s4part true true false false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_three0 : s4three 0 0 1 2 (fun c => decide (c ≠ 3)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_three1 : s4three 1 0 1 3 (fun c => decide (c ≠ 2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_three2 : s4three 2 0 2 3 (fun c => decide (c ≠ 1)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_three3 : s4three 3 1 2 3 (fun c => decide (c ≠ 0)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_full : s4full = true := by decide +kernel

end GeoSeq
