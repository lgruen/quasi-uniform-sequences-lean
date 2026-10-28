/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S3Auto
public import GeoSeq.S3Data

@[expose] public section

/-!
# GeoSeq stage S8: the automaton certificate of `thm:S3`, source coordinate `1` (kernel `decide`)

Initial vector, closure of the state lists under the three Cartier steps, readouts, witnesses and
distinctness of the `85` columns (data in `GeoSeq/S3Data.lean`; used in `GeoSeq/S3Cert.lean`). The
checks are split into chunks of states so that each kernel check stays small.
-/

namespace GeoSeq

set_option maxRecDepth 100000 in
theorem s3_init1 : (S3Bv 1).getD 0 [] = initVS 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeB1 : ∀ s : Fin 4, (((S3tB 1).getD s []).getD 0 0 < 4 ∧
    stepVS 0 ((S3Bv 1).getD s []) = (S3Bv 1).getD (((S3tB 1).getD s []).getD 0 0) []) ∧
    ∀ r : Fin 3, r ≠ 0 → ((S3tB 1).getD s []).getD r 0 < 225 ∧
      stepVS r ((S3Bv 1).getD s []) = (S3Av 1).getD (((S3tB 1).getD s []).getD r 0) [] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_0 : ∀ s : Fin 225, 0 ≤ s.val → s.val < 25 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_1 : ∀ s : Fin 225, 25 ≤ s.val → s.val < 50 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_2 : ∀ s : Fin 225, 50 ≤ s.val → s.val < 75 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_3 : ∀ s : Fin 225, 75 ≤ s.val → s.val < 100 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_4 : ∀ s : Fin 225, 100 ≤ s.val → s.val < 125 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_5 : ∀ s : Fin 225, 125 ≤ s.val → s.val < 150 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_6 : ∀ s : Fin 225, 150 ≤ s.val → s.val < 175 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_7 : ∀ s : Fin 225, 175 ≤ s.val → s.val < 200 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_closeA1_8 : ∀ s : Fin 225, 200 ≤ s.val → s.val < 225 → ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧ stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by decide +kernel

theorem s3_closeA1 : ∀ s : Fin 225, ∀ r : Fin 3, ((S3tA 1).getD s []).getD r 0 < 225 ∧
    stepVS r ((S3Av 1).getD s []) = (S3Av 1).getD (((S3tA 1).getD s []).getD r 0) [] := by
  intro s
  have h : (0 ≤ s.val ∧ s.val < 25) ∨ (25 ≤ s.val ∧ s.val < 50) ∨ (50 ≤ s.val ∧ s.val < 75) ∨ (75 ≤ s.val ∧ s.val < 100) ∨ (100 ≤ s.val ∧ s.val < 125) ∨ (125 ≤ s.val ∧ s.val < 150) ∨ (150 ≤ s.val ∧ s.val < 175) ∨ (175 ≤ s.val ∧ s.val < 200) ∨ (200 ≤ s.val ∧ s.val < 225) := by omega
  rcases h with h | h | h | h | h | h | h | h | h
  · exact s3_closeA1_0 s (by omega) (by omega)
  · exact s3_closeA1_1 s (by omega) (by omega)
  · exact s3_closeA1_2 s (by omega) (by omega)
  · exact s3_closeA1_3 s (by omega) (by omega)
  · exact s3_closeA1_4 s (by omega) (by omega)
  · exact s3_closeA1_5 s (by omega) (by omega)
  · exact s3_closeA1_6 s (by omega) (by omega)
  · exact s3_closeA1_7 s (by omega) (by omega)
  · exact s3_closeA1_8 s (by omega) (by omega)

set_option maxRecDepth 100000 in
theorem s3_read1_0 : ∀ s : Fin 225, 0 ≤ s.val → s.val < 45 → (S3out 1).getD s 0 < 85 ∧ ((S3Av 1).getD s []).map acoefS = ((S3tup 1).getD ((S3out 1).getD s 0) []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_read1_1 : ∀ s : Fin 225, 45 ≤ s.val → s.val < 90 → (S3out 1).getD s 0 < 85 ∧ ((S3Av 1).getD s []).map acoefS = ((S3tup 1).getD ((S3out 1).getD s 0) []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_read1_2 : ∀ s : Fin 225, 90 ≤ s.val → s.val < 135 → (S3out 1).getD s 0 < 85 ∧ ((S3Av 1).getD s []).map acoefS = ((S3tup 1).getD ((S3out 1).getD s 0) []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_read1_3 : ∀ s : Fin 225, 135 ≤ s.val → s.val < 180 → (S3out 1).getD s 0 < 85 ∧ ((S3Av 1).getD s []).map acoefS = ((S3tup 1).getD ((S3out 1).getD s 0) []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_read1_4 : ∀ s : Fin 225, 180 ≤ s.val → s.val < 225 → (S3out 1).getD s 0 < 85 ∧ ((S3Av 1).getD s []).map acoefS = ((S3tup 1).getD ((S3out 1).getD s 0) []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

theorem s3_read1 : ∀ s : Fin 225, (S3out 1).getD s 0 < 85 ∧
    ((S3Av 1).getD s []).map acoefS =
      ((S3tup 1).getD ((S3out 1).getD s 0) []).map (fun n : ℕ => (n : ZMod 3)) := by
  intro s
  have h : (0 ≤ s.val ∧ s.val < 45) ∨ (45 ≤ s.val ∧ s.val < 90) ∨ (90 ≤ s.val ∧ s.val < 135) ∨ (135 ≤ s.val ∧ s.val < 180) ∨ (180 ≤ s.val ∧ s.val < 225) := by omega
  rcases h with h | h | h | h | h
  · exact s3_read1_0 s (by omega) (by omega)
  · exact s3_read1_1 s (by omega) (by omega)
  · exact s3_read1_2 s (by omega) (by omega)
  · exact s3_read1_3 s (by omega) (by omega)
  · exact s3_read1_4 s (by omega) (by omega)

set_option maxRecDepth 100000 in
theorem s3_wit1_0 : ∀ t : Fin 85, 0 ≤ t.val → t.val < 17 → (∀ d ∈ (S3wit 1).getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 ((S3wit 1).getD t []) ∧ (readVS ((S3wit 1).getD t []) (initVS 1)).map acoefS = ((S3tup 1).getD t []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_wit1_1 : ∀ t : Fin 85, 17 ≤ t.val → t.val < 34 → (∀ d ∈ (S3wit 1).getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 ((S3wit 1).getD t []) ∧ (readVS ((S3wit 1).getD t []) (initVS 1)).map acoefS = ((S3tup 1).getD t []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_wit1_2 : ∀ t : Fin 85, 34 ≤ t.val → t.val < 51 → (∀ d ∈ (S3wit 1).getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 ((S3wit 1).getD t []) ∧ (readVS ((S3wit 1).getD t []) (initVS 1)).map acoefS = ((S3tup 1).getD t []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_wit1_3 : ∀ t : Fin 85, 51 ≤ t.val → t.val < 68 → (∀ d ∈ (S3wit 1).getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 ((S3wit 1).getD t []) ∧ (readVS ((S3wit 1).getD t []) (initVS 1)).map acoefS = ((S3tup 1).getD t []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_wit1_4 : ∀ t : Fin 85, 68 ≤ t.val → t.val < 85 → (∀ d ∈ (S3wit 1).getD t [], d < 3) ∧ 1 ≤ Nat.ofDigits 3 ((S3wit 1).getD t []) ∧ (readVS ((S3wit 1).getD t []) (initVS 1)).map acoefS = ((S3tup 1).getD t []).map (fun n : ℕ => (n : ZMod 3)) := by decide +kernel

theorem s3_wit1 : ∀ t : Fin 85, (∀ d ∈ (S3wit 1).getD t [], d < 3) ∧
    1 ≤ Nat.ofDigits 3 ((S3wit 1).getD t []) ∧
    (readVS ((S3wit 1).getD t []) (initVS 1)).map acoefS =
      ((S3tup 1).getD t []).map (fun n : ℕ => (n : ZMod 3)) := by
  intro t
  have h : (0 ≤ t.val ∧ t.val < 17) ∨ (17 ≤ t.val ∧ t.val < 34) ∨ (34 ≤ t.val ∧ t.val < 51) ∨ (51 ≤ t.val ∧ t.val < 68) ∨ (68 ≤ t.val ∧ t.val < 85) := by omega
  rcases h with h | h | h | h | h
  · exact s3_wit1_0 t (by omega) (by omega)
  · exact s3_wit1_1 t (by omega) (by omega)
  · exact s3_wit1_2 t (by omega) (by omega)
  · exact s3_wit1_3 t (by omega) (by omega)
  · exact s3_wit1_4 t (by omega) (by omega)

set_option maxRecDepth 100000 in
theorem s3_distinct1_0 : ∀ t : Fin 85, 0 ≤ t.val → t.val < 17 → ∀ t' : Fin 85, t ≠ t' → ∃ k : Fin 24, S3tupv 1 t k ≠ S3tupv 1 t' k := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_distinct1_1 : ∀ t : Fin 85, 17 ≤ t.val → t.val < 34 → ∀ t' : Fin 85, t ≠ t' → ∃ k : Fin 24, S3tupv 1 t k ≠ S3tupv 1 t' k := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_distinct1_2 : ∀ t : Fin 85, 34 ≤ t.val → t.val < 51 → ∀ t' : Fin 85, t ≠ t' → ∃ k : Fin 24, S3tupv 1 t k ≠ S3tupv 1 t' k := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_distinct1_3 : ∀ t : Fin 85, 51 ≤ t.val → t.val < 68 → ∀ t' : Fin 85, t ≠ t' → ∃ k : Fin 24, S3tupv 1 t k ≠ S3tupv 1 t' k := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_distinct1_4 : ∀ t : Fin 85, 68 ≤ t.val → t.val < 85 → ∀ t' : Fin 85, t ≠ t' → ∃ k : Fin 24, S3tupv 1 t k ≠ S3tupv 1 t' k := by decide +kernel

theorem s3_distinct1 : ∀ t t' : Fin 85, t ≠ t' → ∃ k : Fin 24, S3tupv 1 t k ≠ S3tupv 1 t' k := by
  intro t
  have h : (0 ≤ t.val ∧ t.val < 17) ∨ (17 ≤ t.val ∧ t.val < 34) ∨ (34 ≤ t.val ∧ t.val < 51) ∨ (51 ≤ t.val ∧ t.val < 68) ∨ (68 ≤ t.val ∧ t.val < 85) := by omega
  rcases h with h | h | h | h | h
  · exact s3_distinct1_0 t (by omega) (by omega)
  · exact s3_distinct1_1 t (by omega) (by omega)
  · exact s3_distinct1_2 t (by omega) (by omega)
  · exact s3_distinct1_3 t (by omega) (by omega)
  · exact s3_distinct1_4 t (by omega) (by omega)

end GeoSeq
