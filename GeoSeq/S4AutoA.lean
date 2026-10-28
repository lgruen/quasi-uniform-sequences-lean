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
# GeoSeq stage S8: the automaton certificate of `thm:S4`, source coordinate `0`, part `A`

Initial vector, closure of the state lists under the four Cartier steps, readouts, witnesses, distinctness
of the `80` pair columns, `D_i(0) = 0`, and the words of the `120` change columns (data in
`GeoSeq/S4Data.lean`; used in `GeoSeq/S4Cert.lean`; the other sources follow by `S4_rot`). Split into chunks,
elaborated sequentially (`Elab.async false`), so that each kernel check stays small.
-/

namespace GeoSeq

set_option Elab.async false

theorem s4_closeA_0 : ∀ s : Fin 170, 0 ≤ s.val → s.val < 20 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_1 : ∀ s : Fin 170, 20 ≤ s.val → s.val < 40 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_2 : ∀ s : Fin 170, 40 ≤ s.val → s.val < 60 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_3 : ∀ s : Fin 170, 60 ≤ s.val → s.val < 80 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

theorem s4_closeA_4 : ∀ s : Fin 170, 80 ≤ s.val → s.val < 100 → ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by decide +kernel

end GeoSeq
