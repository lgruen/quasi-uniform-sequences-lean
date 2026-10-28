/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S4Auto
public import GeoSeq.S4Data
public import GeoSeq.K4Gap

@[expose] public section

/-!
# GeoSeq stage S8: the automaton certificate of `thm:S4`, source coordinate `0`, part `B`

Initial vector, closure of the state lists under the four Cartier steps, readouts, witnesses, distinctness
of the `80` pair columns, `D_i(0) = 0`, and the words of the `120` change columns (data in
`GeoSeq/S4Data.lean`; used in `GeoSeq/S4Cert.lean`; the other sources follow by `S4_rot`). Split into chunks,
elaborated sequentially (`Elab.async false`), so that each kernel check stays small.
-/

namespace GeoSeq

set_option Elab.async false

theorem s4_closeA_5 : ∀ s : Fin 170, 100 ≤ s.val → s.val < 120 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_6 : ∀ s : Fin 170, 120 ≤ s.val → s.val < 140 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_7 : ∀ s : Fin 170, 140 ≤ s.val → s.val < 160 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_8 : ∀ s : Fin 170, 160 ≤ s.val → s.val < 170 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_init : S4Bv.getD 0 [] = initVU 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_closeB0 : ∀ s : Fin 4, (S4tB.getD s []).getD 0 0 < 4 ∧
    stepVU 0 (S4Bv.getD s []) = S4Bv.getD ((S4tB.getD s []).getD 0 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem s4_closeBr : ∀ s : Fin 4, ∀ r : Fin 4, r ≠ 0 → (S4tB.getD s []).getD r 0 < 170 ∧
    stepVU r (S4Bv.getD s []) = S4Av.getD ((S4tB.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeB : ∀ s : Fin 4, ((S4tB.getD s []).getD 0 0 < 4 ∧
    stepVU 0 (S4Bv.getD s []) = S4Bv.getD ((S4tB.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 4, r ≠ 0 → (S4tB.getD s []).getD r 0 < 170 ∧
      stepVU r (S4Bv.getD s []) = S4Av.getD ((S4tB.getD s []).getD r 0) [] :=
  fun s => ⟨s4_closeB0 s, s4_closeBr s⟩

theorem s4_zero : ∀ i : Fin 5, ∀ c : Fin 4, acoefU (initSU i c 0 0) = 0 := by decide +kernel

end GeoSeq
