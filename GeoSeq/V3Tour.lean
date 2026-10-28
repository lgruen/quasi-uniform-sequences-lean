/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib

@[expose] public section

/-!
# GeoSeq stage V3: minimal patterns of restricted crosses (`prop:tournament`)

A pattern of restricted crosses is a relation `R c c'` ("`W_{c←c'}` is restricted") on the coordinates `Fin s`
(only pairs `c ≠ c'` matter). The hypothesis of `prop:tournament` — every step `e` has a moving coordinate `c`
with `W_{c←c'}` restricted for every other `c' ∈ supp e` — reads: every nonempty set `E` of coordinates
(`E = supp e`; the supports of the steps `e ∈ {-1,0,1}^s \ 0` are exactly the nonempty sets) has an element `c`
with `R c c'` for all `c' ∈ E \ {c}`.
* `tournament`: then some order `v` of the coordinates has `R (v i) (v j)` for all `i < j`;
* `tournament_card`: hence at least `s(s-1)/2` crosses are restricted;
* `tournament_min`: the patterns with this property and exactly `s(s-1)/2` restricted crosses are exactly the
  ordered patterns (`R c c' ⟺ v⁻¹ c < v⁻¹ c'` for `c ≠ c'`).
-/

namespace GeoSeq

open Finset

section Tournament

variable {α : Type*} [DecidableEq α] (R : α → α → Prop)

lemma exists_pairwise_list (hR : ∀ E : Finset α, E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') :
    ∀ E : Finset α, ∃ l : List α, l.Nodup ∧ l.toFinset = E ∧ l.Pairwise R := by
  intro E
  induction E using Finset.strongInduction with
  | H E ih =>
    rcases E.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, rfl, List.Pairwise.nil⟩
    · obtain ⟨c, hc, hcR⟩ := hR E hne
      obtain ⟨l, hnd, hset, hpw⟩ := ih (E.erase c) (erase_ssubset hc)
      refine ⟨c :: l, List.nodup_cons.mpr ⟨fun h => ?_, hnd⟩, ?_, List.pairwise_cons.mpr ⟨fun a ha => ?_, hpw⟩⟩
      · have : c ∈ l.toFinset := List.mem_toFinset.mpr h
        rw [hset] at this; simp at this
      · rw [List.toFinset_cons, hset, insert_erase hc]
      · have : a ∈ l.toFinset := List.mem_toFinset.mpr ha
        rw [hset] at this
        exact hcR a (mem_of_mem_erase this) (ne_of_mem_erase this)

end Tournament

variable {s : ℕ}

/-- **`prop:tournament`**, first part: if every nonempty set `E` of coordinates has an element `c` with
`R c c'` for all other `c' ∈ E`, then in some order `v` of the coordinates every upper cross is restricted:
`R (v i) (v j)` for all `i < j`. -/
theorem tournament (R : Fin s → Fin s → Prop)
    (hR : ∀ E : Finset (Fin s), E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') :
    ∃ v : Fin s ≃ Fin s, ∀ i j : Fin s, i < j → R (v i) (v j) := by
  obtain ⟨l, hnd, hset, hpw⟩ := exists_pairwise_list R hR univ
  have hlen : l.length = s := by
    have := List.toFinset_card_of_nodup hnd
    rw [hset, card_univ, Fintype.card_fin] at this
    exact this.symm
  let f : Fin s → Fin s := fun i => l.get (Fin.cast hlen.symm i)
  have hinj : Function.Injective f := fun i j hij => by
    have := (hnd.get_inj_iff).mp hij
    exact Fin.cast_injective _ this
  have hbij : Function.Bijective f := (Finite.injective_iff_bijective).mp hinj
  refine ⟨Equiv.ofBijective f hbij, fun i j hij => ?_⟩
  exact List.pairwise_iff_get.mp hpw _ _ (by rw [Fin.lt_def, Fin.coe_cast, Fin.coe_cast]; exact Fin.lt_def.mp hij)

lemma card_lt_pairs (s : ℕ) : (univ.filter (fun x : Fin s × Fin s => x.1 < x.2)).card = s * (s - 1) / 2 := by
  rw [card_filter, ← univ_product_univ, sum_product_right]
  have : ∀ j : Fin s, (∑ i : Fin s, if i < j then 1 else 0) = (j : ℕ) := fun j => by
    rw [← card_filter]
    have : univ.filter (fun i : Fin s => i < j) = Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) s, sum_range_id]

lemma image_lt_pairs (R : Fin s → Fin s → Prop) [DecidableRel R] (v : Fin s ≃ Fin s)
    (hv : ∀ i j : Fin s, i < j → R (v i) (v j)) :
    (univ.filter (fun x : Fin s × Fin s => x.1 < x.2)).image (fun x => (v x.1, v x.2)) ⊆
      univ.filter (fun x : Fin s × Fin s => x.1 ≠ x.2 ∧ R x.1 x.2) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
  have hlt := (mem_filter.mp hx).2
  exact mem_filter.mpr ⟨mem_univ _, fun h => (ne_of_lt hlt) (v.injective h), hv _ _ hlt⟩

lemma card_image_lt_pairs (v : Fin s ≃ Fin s) :
    ((univ.filter (fun x : Fin s × Fin s => x.1 < x.2)).image (fun x => (v x.1, v x.2))).card =
      s * (s - 1) / 2 := by
  rw [card_image_of_injective _ (fun x y h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (v.injective h.1) (v.injective h.2)), card_lt_pairs]

/-- **`prop:tournament`**: at least `s(s-1)/2` crosses are restricted. -/
theorem tournament_card (R : Fin s → Fin s → Prop) [DecidableRel R]
    (hR : ∀ E : Finset (Fin s), E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') :
    s * (s - 1) / 2 ≤ (univ.filter (fun x : Fin s × Fin s => x.1 ≠ x.2 ∧ R x.1 x.2)).card := by
  obtain ⟨v, hv⟩ := tournament R hR
  rw [← card_image_lt_pairs v]
  exact card_le_card (image_lt_pairs R v hv)

/-- **`prop:tournament`**, last sentence: the patterns with the property and exactly `s(s-1)/2` restricted
crosses are exactly the ordered patterns: `R c c' ⟺ v⁻¹ c < v⁻¹ c'` (`c ≠ c'`) for an order `v`. -/
theorem tournament_min (R : Fin s → Fin s → Prop) [DecidableRel R] :
    ((∀ E : Finset (Fin s), E.Nonempty → ∃ c ∈ E, ∀ c' ∈ E, c' ≠ c → R c c') ∧
        (univ.filter (fun x : Fin s × Fin s => x.1 ≠ x.2 ∧ R x.1 x.2)).card = s * (s - 1) / 2) ↔
      ∃ v : Fin s ≃ Fin s, ∀ c c' : Fin s, c ≠ c' → (R c c' ↔ v.symm c < v.symm c') := by
  constructor
  · rintro ⟨hR, hcard⟩
    obtain ⟨v, hv⟩ := tournament R hR
    have heq := eq_of_subset_of_card_le (image_lt_pairs R v hv) (by rw [hcard, card_image_lt_pairs v])
    refine ⟨v, fun c c' hcc => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have hm : (c, c') ∈ univ.filter (fun x : Fin s × Fin s => x.1 ≠ x.2 ∧ R x.1 x.2) :=
        mem_filter.mpr ⟨mem_univ _, hcc, h⟩
      rw [← heq] at hm
      obtain ⟨x, hx, hxe⟩ := mem_image.mp hm
      simp only [Prod.mk.injEq] at hxe
      rw [← hxe.1, ← hxe.2, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact (mem_filter.mp hx).2
    · have := hv _ _ h
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  · rintro ⟨v, hv⟩
    have hv' : ∀ i j : Fin s, i < j → R (v i) (v j) := fun i j hij =>
      (hv (v i) (v j) (fun h => (ne_of_lt hij) (v.injective h))).mpr (by simpa using hij)
    refine ⟨fun E hE => ?_, ?_⟩
    · obtain ⟨c, hc, hmin⟩ := exists_min_image E (fun c => v.symm c) hE
      refine ⟨c, hc, fun c' hc' hne => (hv c c' hne.symm).mpr ?_⟩
      exact lt_of_le_of_ne (hmin c' hc') (fun h => hne (v.symm.injective h).symm)
    · have hsub := image_lt_pairs R v hv'
      refine le_antisymm ?_ (by rw [← card_image_lt_pairs v]; exact card_le_card hsub)
      rw [← card_image_lt_pairs v]
      refine card_le_card fun x hx => ?_
      obtain ⟨-, hne, hRx⟩ := mem_filter.mp hx
      refine mem_image.mpr ⟨(v.symm x.1, v.symm x.2), mem_filter.mpr ⟨mem_univ _, (hv _ _ hne).mp hRx⟩, ?_⟩
      simp

end GeoSeq
