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
# GeoSeq stage S8: the automaton certificate of `thm:S4`, source coordinate `0`, part `D`

Initial vector, closure of the state lists under the four Cartier steps, readouts, witnesses, distinctness
of the `80` pair columns, `D_i(0) = 0`, and the words of the `120` change columns (data in
`GeoSeq/S4Data.lean`; used in `GeoSeq/S4Cert.lean`; the other sources follow by `S4_rot`). Split into chunks,
elaborated sequentially (`Elab.async false`), so that each kernel check stays small.
-/

namespace GeoSeq

set_option Elab.async false

theorem s4_distinct_0 : ∀ t : Fin 80, 0 ≤ t.val → t.val < 20 → ∀ t' : Fin 80, t ≠ t' → ∃ k : Fin 40, S4tupv t k ≠ S4tupv t' k := by decide +kernel

theorem s4_distinct_1 : ∀ t : Fin 80, 20 ≤ t.val → t.val < 40 → ∀ t' : Fin 80, t ≠ t' → ∃ k : Fin 40, S4tupv t k ≠ S4tupv t' k := by decide +kernel

theorem s4_distinct_2 : ∀ t : Fin 80, 40 ≤ t.val → t.val < 60 → ∀ t' : Fin 80, t ≠ t' → ∃ k : Fin 40, S4tupv t k ≠ S4tupv t' k := by decide +kernel

theorem s4_distinct_3 : ∀ t : Fin 80, 60 ≤ t.val → t.val < 80 → ∀ t' : Fin 80, t ≠ t' → ∃ k : Fin 40, S4tupv t k ≠ S4tupv t' k := by decide +kernel

theorem s4_chg : ∀ t : Fin 80, ∀ ty : Fin 2, ∀ c : Fin 4, (S4chg.getD t []).getD ty 0 < 120 ∧
    encVec f4code (fun i : Fin 5 => chgU t ty i c) = ((S4Z 0).getD ((S4chg.getD t []).getD ty 0) []).getD c 0 := by
  decide +kernel

end GeoSeq
