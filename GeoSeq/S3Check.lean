/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S3Data
public import GeoSeq.S3Gap

@[expose] public section

/-!
# GeoSeq stage S8: the finite checks of the certificate of `thm:S3` (kernel `decide`)

The signed words of the columns (`s3_rows`), the buckets (`s3_bk`), the two-digit tables, and the
certificate checks `s3part`/`s3full` for every step code (used in `GeoSeq/S3Cert.lean`).
-/

namespace GeoSeq

open Finset

/-! ## Words of the columns, tables, buckets (kernel checks) -/

set_option maxRecDepth 100000 in
theorem s3_rows : ∀ c' : Fin 3, ∀ f : Fin 2, (S3SW.getD (2 * c' + f) []).length = 85 ∧
    ∀ t : Fin 85, ∀ c : Fin 3,
      ((S3SW.getD (2 * c' + f) []).getD t []).getD c 0 =
        encVec (zcode 3) (fun i : Fin 8 => emod3 (f + 1) * S3tupv c' t (3 * i + c)) ∧
      ((S3SW.getD (2 * c' + f) []).getD t []).getD c 0 < 6561 ∧
      ((S3SW.getD (2 * c' + f) []).getD t []).getD (3 + c) 0 =
        ((S3SW.getD (2 * c' + f) []).getD t []).getD c 0 / 729 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s3_bk : ∀ f : Fin 2, ∀ t : Fin 85, (S3SW.getD (4 + f) []).getD t [] ∈
    s3bucket (f + 1) (((S3SW.getD (4 + f) []).getD t []).getD 3 0)
      (((S3SW.getD (4 + f) []).getD t []).getD 4 0) (((S3SW.getD (4 + f) []).getD t []).getD 5 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem add9_eq : ∀ x y : Fin 9, add9 x y = add3W 2 x y := by decide +kernel

set_option maxRecDepth 100000 in
theorem key9_eq : ∀ f : Fin 2, ∀ k : Fin 9, key9 (f + 1) k = add3W 2 (s3kt (f + 1)) (neg3W 2 k) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part001 : s3part 0 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part002 : s3part 0 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part010 : s3part 0 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part011 : s3part 0 1 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part012 : s3part 0 1 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part020 : s3part 0 2 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part021 : s3part 0 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part022 : s3part 0 2 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part100 : s3part 1 0 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part101 : s3part 1 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part102 : s3part 1 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part110 : s3part 1 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full111 : s3full 1 1 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full112 : s3full 1 1 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part120 : s3part 1 2 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full121 : s3full 1 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full122 : s3full 1 2 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part200 : s3part 2 0 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part201 : s3part 2 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part202 : s3part 2 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part210 : s3part 2 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full211 : s3full 2 1 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full212 : s3full 2 1 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_part220 : s3part 2 2 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full221 : s3full 2 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s3_full222 : s3full 2 2 2 = true := by decide +kernel

lemma s3_check (f0 f1 f2 : ℕ) (h0 : f0 < 3) (h1 : f1 < 3) (h2 : f2 < 3) (hne : f0 ≠ 0 ∨ f1 ≠ 0 ∨ f2 ≠ 0) :
    (f0 ≠ 0 → f1 ≠ 0 → f2 ≠ 0 → s3full f0 f1 f2 = true) ∧
    (f0 = 0 ∨ f1 = 0 ∨ f2 = 0 → s3part f0 f1 f2 = true) := by
  interval_cases f0 <;> interval_cases f1 <;> interval_cases f2
  · exact absurd hne (by omega)
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part001⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part002⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part010⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part011⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part012⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part020⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part021⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part022⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part100⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part101⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part102⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part110⟩
  · exact ⟨fun _ _ _ => s3_full111, fun hz => by omega⟩
  · exact ⟨fun _ _ _ => s3_full112, fun hz => by omega⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part120⟩
  · exact ⟨fun _ _ _ => s3_full121, fun hz => by omega⟩
  · exact ⟨fun _ _ _ => s3_full122, fun hz => by omega⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part200⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part201⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part202⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part210⟩
  · exact ⟨fun _ _ _ => s3_full211, fun hz => by omega⟩
  · exact ⟨fun _ _ _ => s3_full212, fun hz => by omega⟩
  · exact ⟨fun ha hb hc => by omega, fun _ => s3_part220⟩
  · exact ⟨fun _ _ _ => s3_full221, fun hz => by omega⟩
  · exact ⟨fun _ _ _ => s3_full222, fun hz => by omega⟩

end GeoSeq
