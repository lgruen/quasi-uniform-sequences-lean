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
# GeoSeq stage S8: the automaton certificate of `thm:S4`, source coordinate `0`, part `C`

Initial vector, closure of the state lists under the four Cartier steps, readouts, witnesses, distinctness
of the `80` pair columns, `D_i(0) = 0`, and the words of the `120` change columns (data in
`GeoSeq/S4Data.lean`; used in `GeoSeq/S4Cert.lean`; the other sources follow by `S4_rot`). Split into chunks,
elaborated sequentially (`Elab.async false`), so that each kernel check stays small.
-/

namespace GeoSeq

set_option Elab.async false

theorem s4_read_0 : ∀ s : Fin 170, 0 ≤ s.val → s.val < 34 → S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by decide +kernel

theorem s4_read_1 : ∀ s : Fin 170, 34 ≤ s.val → s.val < 68 → S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by decide +kernel

theorem s4_read_2 : ∀ s : Fin 170, 68 ≤ s.val → s.val < 102 → S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by decide +kernel

theorem s4_read_3 : ∀ s : Fin 170, 102 ≤ s.val → s.val < 136 → S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by decide +kernel

theorem s4_read_4 : ∀ s : Fin 170, 136 ≤ s.val → s.val < 170 → S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by decide +kernel

theorem s4_wit_0 : ∀ t : Fin 80, 0 ≤ t.val → t.val < 20 → (∀ d ∈ S4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (S4wit.getD t []) ∧ (readVU (S4wit.getD t []) (initVU 0)).map acoefU = (S4tup.getD t []).map n2f := by decide +kernel

theorem s4_wit_1 : ∀ t : Fin 80, 20 ≤ t.val → t.val < 40 → (∀ d ∈ S4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (S4wit.getD t []) ∧ (readVU (S4wit.getD t []) (initVU 0)).map acoefU = (S4tup.getD t []).map n2f := by decide +kernel

theorem s4_wit_2 : ∀ t : Fin 80, 40 ≤ t.val → t.val < 60 → (∀ d ∈ S4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (S4wit.getD t []) ∧ (readVU (S4wit.getD t []) (initVU 0)).map acoefU = (S4tup.getD t []).map n2f := by decide +kernel

theorem s4_wit_3 : ∀ t : Fin 80, 60 ≤ t.val → t.val < 80 → (∀ d ∈ S4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (S4wit.getD t []) ∧ (readVU (S4wit.getD t []) (initVU 0)).map acoefU = (S4tup.getD t []).map n2f := by decide +kernel

end GeoSeq
