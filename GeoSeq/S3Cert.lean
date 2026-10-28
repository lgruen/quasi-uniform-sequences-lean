/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S3Law
public import GeoSeq.S3Data
public import GeoSeq.S3Gap
public import GeoSeq.S3Cert0
public import GeoSeq.S3Cert1
public import GeoSeq.S3Cert2
public import GeoSeq.S3Check

@[expose] public section

/-!
# GeoSeq stage S8: the exact response sets and the certificate of `thm:S3`

* The automaton certificate (`prop:automaton` for `thm:S3`, one automaton per source coordinate `c'`):
  initial vector, closure under the three Cartier steps, readouts, witnesses (kernel `decide`).
  `S3_resp`: for every `l ≥ 1` the column `(D_i(l)[c][c'])_{i<8, c<3}` is one of the `85` listed
  columns of source `c'`; `S3_resp_card`: exactly these occur.
* The certificate minimum `134917 = min ∑_c (3^8 f_8(e_c, σ_c))²` (`S3_cert_lb`), by kernel checks on
  base-3 words with a filter on the two leading digits (`s3part`, `s3full`, buckets `S3BK`): a moving
  coordinate whose two leading digits are not `(1,1)` (for `e_c = 1`) resp. `(2,2)` (for `e_c = -1`) has
  a bound `≥ 729 > √134917` (`s3_far`).
* `thm:S3`: `S3_sep_one` (`K = 1`, direct check of the `27` points of `P_3`), `S3_sep` (every
  `K ≥ 1`), `S3_allN`, `S3_mesh`.
-/

namespace GeoSeq

open Finset PowerSeries


/-! ## The response sets -/

lemma getD_map_z3 (L : List ℕ) (k : ℕ) : (L.map (fun n : ℕ => (n : ZMod 3))).getD k 0 = (L.getD k 0 : ZMod 3) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases L[k]? <;> simp

lemma valsS_initVS (c' : Fin 3) (l i : ℕ) (hi : i < 8) (c : Fin 3) :
    (valsS (initVS c') l).getD (3 * i + c) 0 = lawD (fun _ => S3g) S3z S3G i l c c' := by
  have hk : 3 * i + (c : ℕ) < 24 := by omega
  simp only [valsS, initVS, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some, Function.comp_apply]
  have e1 : (3 * i + (c : ℕ)) / 3 = i := by omega
  have e2 : (⟨(3 * i + (c : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = c := by
    ext; simp only [Fin.val_mk]; omega
  rw [e1, e2]
  exact S3_init i hi c c' l

lemma s3_cert (c' : Fin 3) : (S3Bv c').getD 0 [] = initVS c' ∧
    (∀ s : Fin 225, ∀ r : Fin 3, ((S3tA c').getD s []).getD r 0 < 225 ∧
      stepVS r ((S3Av c').getD s []) = (S3Av c').getD (((S3tA c').getD s []).getD r 0) []) ∧
    (∀ s : Fin 4, (((S3tB c').getD s []).getD 0 0 < 4 ∧
      stepVS 0 ((S3Bv c').getD s []) = (S3Bv c').getD (((S3tB c').getD s []).getD 0 0) []) ∧
      ∀ r : Fin 3, r ≠ 0 → ((S3tB c').getD s []).getD r 0 < 225 ∧
        stepVS r ((S3Bv c').getD s []) = (S3Av c').getD (((S3tB c').getD s []).getD r 0) []) ∧
    (∀ s : Fin 225, (S3out c').getD s 0 < 85 ∧
      ((S3Av c').getD s []).map acoefS = ((S3tup c').getD ((S3out c').getD s 0) []).map (fun n : ℕ => (n : ZMod 3))) := by
  fin_cases c'
  · exact ⟨s3_init0, s3_closeA0, s3_closeB0, s3_read0⟩
  · exact ⟨s3_init1, s3_closeA1, s3_closeB1, s3_read1⟩
  · exact ⟨s3_init2, s3_closeA2, s3_closeB2, s3_read2⟩

/-- **`prop:automaton` for `thm:S3`** (`j = 8`): for every carry length `l ≥ 1` and source coordinate
`c'`, the column `(D_i(l)[c][c'])_{i<8, c<3}` is one of the `85` listed columns of source `c'`. -/
theorem S3_resp (c' : Fin 3) (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < 85, ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => S3g) S3z S3G i l c c' = S3tupv c' t (3 * i + c) := by
  obtain ⟨hinit, hA, hB, hread⟩ := s3_cert c'
  obtain ⟨s', hs', h⟩ := reach_BS (S3Av c') (S3Bv c') (S3tA c') (S3tB c') 225 4 hA hB l 0 hl (by norm_num)
  rw [hinit] at h
  obtain ⟨h1, h2⟩ := hread ⟨s', hs'⟩
  refine ⟨_, h1, fun i hi c => ?_⟩
  have a := valsS_initVS c' l i hi c
  rw [h, valsS_zero, h2, getD_map_z3] at a
  exact a.symm

/-- **`prop:automaton` for `thm:S3`, exactness**: every listed column occurs for some `l ≥ 1`. -/
theorem S3_resp_occurs (c' : Fin 3) (t : ℕ) (ht : t < 85) :
    ∃ l, 1 ≤ l ∧ ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => S3g) S3z S3G i l c c' = S3tupv c' t (3 * i + c) := by
  have key : ∃ ds : List ℕ, (∀ d ∈ ds, d < 3) ∧ 1 ≤ Nat.ofDigits 3 ds ∧
      (readVS ds (initVS c')).map acoefS = ((S3tup c').getD t []).map (fun n : ℕ => (n : ZMod 3)) := by
    fin_cases c'
    · exact ⟨_, s3_wit0 ⟨t, ht⟩⟩
    · exact ⟨_, s3_wit1 ⟨t, ht⟩⟩
    · exact ⟨_, s3_wit2 ⟨t, ht⟩⟩
  obtain ⟨ds, hds, h1, h2⟩ := key
  refine ⟨Nat.ofDigits 3 ds, h1, fun i hi c => ?_⟩
  have a := valsS_initVS c' (Nat.ofDigits 3 ds) i hi c
  rw [valsS_read ds hds, valsS_zero, h2, getD_map_z3] at a
  exact a.symm

/-- **`prop:automaton` for `thm:S3`, the count** (`j = 8`): for every source coordinate `c'`, the columns
over all carry lengths `l ≥ 1` form a set of exactly `85` elements. -/
theorem S3_resp_card (c' : Fin 3) :
    Set.ncard {D : Fin 8 → Fin 3 → ZMod 3 |
      ∃ l, 1 ≤ l ∧ ∀ i : Fin 8, ∀ c : Fin 3, D i c = lawD (fun _ => S3g) S3z S3G i l c c'} = 85 := by
  let f : Fin 85 → (Fin 8 → Fin 3 → ZMod 3) := fun t i c => S3tupv c' t (3 * i + c)
  have hset : {D : Fin 8 → Fin 3 → ZMod 3 |
      ∃ l, 1 ≤ l ∧ ∀ i : Fin 8, ∀ c : Fin 3, D i c = lawD (fun _ => S3g) S3z S3G i l c c'} = Set.range f := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨l, hl, hD⟩
      obtain ⟨t, ht, h⟩ := S3_resp c' l hl
      exact ⟨⟨t, ht⟩, funext fun i => funext fun c => by rw [hD, h i i.isLt c]⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨l, hl, h⟩ := S3_resp_occurs c' t ht
      exact ⟨l, hl, fun i c => (h i i.isLt c).symm⟩
  have hinj : Function.Injective f := by
    intro t t' htt
    by_contra hne
    have hd : ∃ k : Fin 24, S3tupv c' t k ≠ S3tupv c' t' k := by
      fin_cases c'
      · exact s3_distinct0 t t' hne
      · exact s3_distinct1 t t' hne
      · exact s3_distinct2 t t' hne
    obtain ⟨k, hk⟩ := hd
    apply hk
    have hk3 : (k : ℕ) = 3 * ((k : ℕ) / 3) + (k : ℕ) % 3 := by omega
    have := congrFun (congrFun htt ⟨(k : ℕ) / 3, by omega⟩) ⟨(k : ℕ) % 3, by omega⟩
    simp only [f, Fin.val_mk] at this
    rw [hk3]; exact this
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## Soundness of the filtered checks -/

/-- A moving coordinate whose two leading digits do not have the small pattern has a bound `≥ 729`. -/
lemma s3_far (f w : ℕ) (hf : f = 1 ∨ f = 2) (hw : w < 6561) (hk : w / 729 ≠ s3kt f) : 729 ≤ s3b f w := by
  rcases hf with rfl | rfl
  · have hn := neg3W_div 2 6 w
    have hlt := neg3W_lt 8 w
    norm_num at hn hlt
    have hwk : w / 729 < 9 := by omega
    have key : neg3W 2 (w / 729) ≠ 8 := neg3W_key ⟨w / 729, hwk⟩ (by simpa [s3kt] using hk)
    rw [← hn] at key
    simp only [s3b, show (1 : ℕ) ≠ 0 by norm_num, ite_false, ite_true]
    omega
  · simp only [s3kt, show (2 : ℕ) ≠ 1 by norm_num, ite_false] at hk
    simp only [s3b, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, ite_false]
    omega

lemma s3_keysum (a b d : ℕ) :
    add3W 8 (add3W 8 a b) d / 729 = add3W 2 (add3W 2 (a / 729) (b / 729)) (d / 729) := by
  have h1 := add3W_div 2 6 (add3W 8 a b) d
  have h2 := add3W_div 2 6 a b
  norm_num at h1 h2
  rw [h1, h2]

lemma s3_sum_big (x y z : ℕ) (h : 729 ≤ x ∨ 729 ≤ y ∨ 729 ≤ z) : 134917 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  rcases h with h | h | h <;> nlinarith

lemma s3_div9 (w : ℕ) (hw : w < 6561) : w / 729 < 9 := by omega

/-- One coordinate of the partial check: if the filter fails, the bound is `≥ 729`. -/
lemma s3_coord (f wa wb wd : ℕ) (hf : f < 3) (ha : wa < 6561) (hb : wb < 6561) (hd : wd < 6561)
    (hfilt : s3filt f (add9 (add9 (wa / 729) (wb / 729)) (wd / 729)) = false) :
    729 ≤ s3b f (add3W 8 (add3W 8 wa wb) wd) := by
  have e1 := add9_eq ⟨wa / 729, s3_div9 _ ha⟩ ⟨wb / 729, s3_div9 _ hb⟩
  simp only [Fin.val_mk] at e1
  have h9 := add3W_lt 2 (wa / 729) (wb / 729)
  norm_num at h9
  have e2 := add9_eq ⟨add3W 2 (wa / 729) (wb / 729), h9⟩ ⟨wd / 729, s3_div9 _ hd⟩
  simp only [Fin.val_mk] at e2
  rw [e1, e2] at hfilt
  unfold s3filt at hfilt
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hfilt
  have hlt : add3W 8 (add3W 8 wa wb) wd < 6561 := by have := add3W_lt 8 (add3W 8 wa wb) wd; norm_num at this; exact this
  refine s3_far f _ (by omega) hlt ?_
  rw [s3_keysum]; exact hfilt.2

lemma getD_mem3 {α : Type*} (L : List α) (k : ℕ) (d : α) (h : k < L.length) : L.getD k d ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

lemma getD_getElem3 {α : Type*} (L : List α) (t : ℕ) (d : α) (h : t < L.length) : L.getD t d = L[t] := by
  simp [List.getD_eq_getElem?_getD, h]

lemma s3sw_mem (c' f : ℕ) (hc : c' < 3) (hf0 : f ≠ 0) (hf : f < 3) (d : List ℕ) (hd : d ∈ s3sw c' f) :
    ∃ t < 85, d = (S3SW.getD (2 * c' + f - 1) []).getD t [] := by
  unfold s3sw at hd
  rw [if_neg hf0] at hd
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hd
  obtain ⟨hlen, -⟩ := s3_rows ⟨c', hc⟩ ⟨f - 1, by omega⟩
  simp only [Fin.val_mk, show 2 * c' + (f - 1) = 2 * c' + f - 1 by omega] at hlen
  exact ⟨t, hlen ▸ ht, (getD_getElem3 _ _ _ ht).symm⟩

/-- Rows of the signed-word lists: words `< 3^8` and keys `= word / 3^6`. -/
lemma s3sw_row (c' f : ℕ) (hc : c' < 3) (hf : f < 3) (d : List ℕ) (hd : d ∈ s3sw c' f) (c : ℕ)
    (hc3 : c < 3) : d.getD c 0 < 6561 ∧ d.getD (3 + c) 0 = d.getD c 0 / 729 := by
  by_cases h0 : f = 0
  · unfold s3sw at hd
    rw [if_pos h0, List.mem_singleton] at hd
    subst hd
    interval_cases c <;> decide
  · obtain ⟨t, ht, rfl⟩ := s3sw_mem c' f hc h0 hf d hd
    obtain ⟨-, hrow⟩ := s3_rows ⟨c', hc⟩ ⟨f - 1, by omega⟩
    simp only [Fin.val_mk, show 2 * c' + (f - 1) = 2 * c' + f - 1 by omega] at hrow
    obtain ⟨-, h2, h3⟩ := hrow ⟨t, ht⟩ ⟨c, hc3⟩
    exact ⟨h2, h3⟩

lemma s3part_spec (f0 f1 f2 : ℕ) (h0 : f0 < 3) (h1 : f1 < 3) (h2 : f2 < 3)
    (h : s3part f0 f1 f2 = true) (a b d : List ℕ) (ha : a ∈ s3sw 0 f0) (hb : b ∈ s3sw 1 f1)
    (hd : d ∈ s3sw 2 f2) :
    134917 ≤ s3b f0 (add3W 8 (add3W 8 (a.getD 0 0) (b.getD 0 0)) (d.getD 0 0)) ^ 2 +
      s3b f1 (add3W 8 (add3W 8 (a.getD 1 0) (b.getD 1 0)) (d.getD 1 0)) ^ 2 +
      s3b f2 (add3W 8 (add3W 8 (a.getD 2 0) (b.getD 2 0)) (d.getD 2 0)) ^ 2 := by
  unfold s3part at h
  rw [List.all_eq_true] at h
  have h' := h a ha
  rw [List.all_eq_true] at h'
  have h'' := h' b hb
  rw [List.all_eq_true] at h''
  have hx := h'' d hd
  have ra := fun c hc => s3sw_row 0 f0 (by norm_num) h0 a ha c hc
  have rb := fun c hc => s3sw_row 1 f1 (by norm_num) h1 b hb c hc
  have rd := fun c hc => s3sw_row 2 f2 (by norm_num) h2 d hd c hc
  rw [(ra 0 (by norm_num)).2, (rb 0 (by norm_num)).2, (rd 0 (by norm_num)).2,
    (ra 1 (by norm_num)).2, (rb 1 (by norm_num)).2, (rd 1 (by norm_num)).2,
    (ra 2 (by norm_num)).2, (rb 2 (by norm_num)).2, (rd 2 (by norm_num)).2] at hx
  split_ifs at hx with hc
  · unfold s3ok at hx; exact of_decide_eq_true hx
  · simp only [Bool.and_eq_true, not_and_or, Bool.not_eq_true] at hc
    apply s3_sum_big
    rcases hc with (hc | hc) | hc
    · left; exact s3_coord f0 _ _ _ h0 (ra 0 (by norm_num)).1 (rb 0 (by norm_num)).1 (rd 0 (by norm_num)).1 hc
    · right; left
      exact s3_coord f1 _ _ _ h1 (ra 1 (by norm_num)).1 (rb 1 (by norm_num)).1 (rd 1 (by norm_num)).1 hc
    · right; right
      exact s3_coord f2 _ _ _ h2 (ra 2 (by norm_num)).1 (rb 2 (by norm_num)).1 (rd 2 (by norm_num)).1 hc

/-- One coordinate of the bucket check: a column of the third source with a different key gives a
bound `≥ 729`. -/
lemma s3_coord_full (f wa wb wd : ℕ) (hf : f = 1 ∨ f = 2) (ha : wa < 6561) (hb : wb < 6561)
    (hd : wd < 6561) (hk : wd / 729 ≠ key9 f (add9 (wa / 729) (wb / 729))) :
    729 ≤ s3b f (add3W 8 (add3W 8 wa wb) wd) := by
  have e1 := add9_eq ⟨wa / 729, s3_div9 _ ha⟩ ⟨wb / 729, s3_div9 _ hb⟩
  simp only [Fin.val_mk] at e1
  have h9 := add3W_lt 2 (wa / 729) (wb / 729)
  norm_num at h9
  have e2 := key9_eq ⟨f - 1, by omega⟩ ⟨add3W 2 (wa / 729) (wb / 729), h9⟩
  simp only [Fin.val_mk, show f - 1 + 1 = f by omega] at e2
  rw [e1, e2] at hk
  have hlt : add3W 8 (add3W 8 wa wb) wd < 6561 := by have := add3W_lt 8 (add3W 8 wa wb) wd; norm_num at this; exact this
  refine s3_far f _ hf hlt ?_
  rw [s3_keysum]
  intro heq
  have hkt : s3kt f < 9 := by unfold s3kt; split_ifs <;> norm_num
  have := add3W_solve ⟨add3W 2 (wa / 729) (wb / 729), h9⟩ ⟨wd / 729, s3_div9 _ hd⟩ ⟨s3kt f, hkt⟩ heq
  exact hk this

lemma s3full_spec (f0 f1 f2 : ℕ) (h0 : f0 = 1 ∨ f0 = 2) (h1 : f1 = 1 ∨ f1 = 2) (h2 : f2 = 1 ∨ f2 = 2)
    (h : s3full f0 f1 f2 = true) (a b d : List ℕ) (ha : a ∈ s3sw 0 f0) (hb : b ∈ s3sw 1 f1)
    (hd : d ∈ s3sw 2 f2) :
    134917 ≤ s3b f0 (add3W 8 (add3W 8 (a.getD 0 0) (b.getD 0 0)) (d.getD 0 0)) ^ 2 +
      s3b f1 (add3W 8 (add3W 8 (a.getD 1 0) (b.getD 1 0)) (d.getD 1 0)) ^ 2 +
      s3b f2 (add3W 8 (add3W 8 (a.getD 2 0) (b.getD 2 0)) (d.getD 2 0)) ^ 2 := by
  have ra := fun c hc => s3sw_row 0 f0 (by norm_num) (by omega) a ha c hc
  have rb := fun c hc => s3sw_row 1 f1 (by norm_num) (by omega) b hb c hc
  have rd := fun c hc => s3sw_row 2 f2 (by norm_num) (by omega) d hd c hc
  unfold s3full at h
  rw [List.all_eq_true] at h
  have h' := h a ha
  rw [List.all_eq_true] at h'
  have h'' := h' b hb
  rw [List.all_eq_true] at h''
  by_cases hk : d.getD 3 0 = key9 f0 (add9 (a.getD 3 0) (b.getD 3 0)) ∧
      d.getD 4 0 = key9 f1 (add9 (a.getD 4 0) (b.getD 4 0)) ∧
      d.getD 5 0 = key9 f2 (add9 (a.getD 5 0) (b.getD 5 0))
  · -- `d` lies in the bucket that was checked
    have hmem : d ∈ s3bucket f2 (key9 f0 (add9 (a.getD 3 0) (b.getD 3 0)))
        (key9 f1 (add9 (a.getD 4 0) (b.getD 4 0))) (key9 f2 (add9 (a.getD 5 0) (b.getD 5 0))) := by
      rw [← hk.1, ← hk.2.1, ← hk.2.2]
      obtain ⟨t, ht, rfl⟩ := s3sw_mem 2 f2 (by norm_num) (by omega) (by omega) d hd
      have := s3_bk ⟨f2 - 1, by omega⟩ ⟨t, ht⟩
      simp only [Fin.val_mk, show f2 - 1 + 1 = f2 by omega, show 4 + (f2 - 1) = 2 * 2 + f2 - 1 by omega] at this
      exact this
    have hx := h'' d hmem
    unfold s3ok at hx; exact of_decide_eq_true hx
  · rw [(ra 0 (by norm_num)).2, (rb 0 (by norm_num)).2, (rd 0 (by norm_num)).2,
      (ra 1 (by norm_num)).2, (rb 1 (by norm_num)).2, (rd 1 (by norm_num)).2,
      (ra 2 (by norm_num)).2, (rb 2 (by norm_num)).2, (rd 2 (by norm_num)).2] at hk
    simp only [not_and_or] at hk
    apply s3_sum_big
    rcases hk with hk | hk | hk
    · left; exact s3_coord_full f0 _ _ _ h0 (ra 0 (by norm_num)).1 (rb 0 (by norm_num)).1 (rd 0 (by norm_num)).1 hk
    · right; left
      exact s3_coord_full f1 _ _ _ h1 (ra 1 (by norm_num)).1 (rb 1 (by norm_num)).1 (rd 1 (by norm_num)).1 hk
    · right; right
      exact s3_coord_full f2 _ _ _ h2 (ra 2 (by norm_num)).1 (rb 2 (by norm_num)).1 (rd 2 (by norm_num)).1 hk

lemma s3_spec (f0 f1 f2 : ℕ) (h0 : f0 < 3) (h1 : f1 < 3) (h2 : f2 < 3) (hne : f0 ≠ 0 ∨ f1 ≠ 0 ∨ f2 ≠ 0)
    (a b d : List ℕ) (ha : a ∈ s3sw 0 f0) (hb : b ∈ s3sw 1 f1) (hd : d ∈ s3sw 2 f2) :
    134917 ≤ s3b f0 (add3W 8 (add3W 8 (a.getD 0 0) (b.getD 0 0)) (d.getD 0 0)) ^ 2 +
      s3b f1 (add3W 8 (add3W 8 (a.getD 1 0) (b.getD 1 0)) (d.getD 1 0)) ^ 2 +
      s3b f2 (add3W 8 (add3W 8 (a.getD 2 0) (b.getD 2 0)) (d.getD 2 0)) ^ 2 := by
  obtain ⟨hf, hp⟩ := s3_check f0 f1 f2 h0 h1 h2 hne
  by_cases hz : f0 = 0 ∨ f1 = 0 ∨ f2 = 0
  · exact s3part_spec f0 f1 f2 h0 h1 h2 (hp hz) a b d ha hb hd
  · simp only [not_or] at hz
    exact s3full_spec f0 f1 f2 (by omega) (by omega) (by omega) (hf hz.1 hz.2.1 hz.2.2) a b d ha hb hd

/-! ## The certificate minimum -/

lemma s3b_le (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (σ : Fin 8 → ZMod 3) :
    s3b (fcode e) (encVec (zcode 3) σ) ≤ gapNum (zcode 3) 8 e σ := by
  unfold s3b fcode
  rcases (show e = -1 ∨ e = 0 ∨ e = 1 by omega) with rfl | rfl | rfl
  · have := gapNum3_neg 8 σ
    simp only [show (-1 : ℤ) ≠ 0 by norm_num, show (-1 : ℤ) ≠ 1 by norm_num, ite_false,
      show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num]
    norm_num at this; omega
  · have := gapNum3_zero 8 σ
    rw [top3_eqW] at this
    simpa using this
  · have := gapNum3_pos 8 σ
    rw [encVec_two3] at this
    simp only [show (1 : ℤ) ≠ 0 by norm_num, ite_true, ite_false, show (1 : ℕ) ≠ 0 by norm_num]
    norm_num at this; omega

lemma enc_term3 (c' : Fin 3) (f t : ℕ) (hf : f < 3) (ht : t < 85) (c : Fin 3) :
    encVec (zcode 3) (fun i : Fin 8 => emod3 f * S3tupv c' t (3 * i + c)) =
      ((if f = 0 then [0, 0, 0, 0, 0, 0] else (S3SW.getD (2 * c' + f - 1) []).getD t []) : List ℕ).getD c 0 := by
  by_cases h0 : f = 0
  · subst h0
    simp only [ite_true, emod3, zero_mul]
    rw [encVec_zero3]
    fin_cases c <;> rfl
  · rw [if_neg h0]
    obtain ⟨-, hrow⟩ := s3_rows c' ⟨f - 1, by omega⟩
    obtain ⟨h1, -, -⟩ := hrow ⟨t, ht⟩ c
    simp only [Fin.val_mk, show f - 1 + 1 = f by omega, show 2 * (c' : ℕ) + (f - 1) = 2 * c' + f - 1 by omega] at h1
    exact h1.symm

/-- The lower-bound half of the certificate of `thm:S3`: for every step and all carry lengths
`l_c ≥ 1`, `∑_c (3^8 f_8(e_c, σ_c))² ≥ 134917`. -/
theorem S3_cert_lb (e : Fin 3 → ℤ) (l : Fin 3 → ℕ) (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1)
    (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    134917 ≤ ∑ c, gapNum (zcode 3) 8 (e c) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l c) ^ 2 := by
  choose t ht hresp using fun c' => S3_resp c' (l c') (hl c')
  set f : Fin 3 → ℕ := fun c' => fcode (e c') with hfdef
  have hf3 : ∀ c', f c' < 3 := fun c' => fcode_lt _
  set row : Fin 3 → List ℕ := fun c' =>
    if f c' = 0 then [0, 0, 0, 0, 0, 0] else (S3SW.getD (2 * c' + f c' - 1) []).getD (t c') [] with hrow
  have hmem : ∀ c' : Fin 3, row c' ∈ s3sw c' (f c') := by
    intro c'
    simp only [hrow, s3sw]
    split_ifs with h0
    · exact List.mem_singleton_self _
    · obtain ⟨hlen, -⟩ := s3_rows c' ⟨f c' - 1, by have := hf3 c'; omega⟩
      simp only [Fin.val_mk, show 2 * (c' : ℕ) + (f c' - 1) = 2 * c' + f c' - 1 by omega] at hlen
      exact getD_mem3 _ _ _ (by rw [hlen]; exact ht c')
  have hw : ∀ c : Fin 3, encVec (zcode 3) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l c) =
      add3W 8 (add3W 8 ((row 0).getD c 0) ((row 1).getD c 0)) ((row 2).getD c 0) := by
    intro c
    have hs : certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l c =
        ((fun i : Fin 8 => emod3 (f 0) * S3tupv 0 (t 0) (3 * i + c)) +
          (fun i : Fin 8 => emod3 (f 1) * S3tupv 1 (t 1) (3 * i + c))) +
          (fun i : Fin 8 => emod3 (f 2) * S3tupv 2 (t 2) (3 * i + c)) := by
      funext i
      simp only [certSigmaP, Fin.sum_univ_three, Pi.add_apply]
      rw [hresp 0 i i.isLt c, hresp 1 i i.isLt c, hresp 2 i i.isLt c, emod3_cast _ (he 0),
        emod3_cast _ (he 1), emod3_cast _ (he 2)]
    rw [hs, encVec_add3, encVec_add3, enc_term3 0 _ _ (hf3 0) (ht 0), enc_term3 1 _ _ (hf3 1) (ht 1),
      enc_term3 2 _ _ (hf3 2) (ht 2)]
  have hb : ∀ c, s3b (f c) (encVec (zcode 3) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l c)) ≤
      gapNum (zcode 3) 8 (e c) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l c) :=
    fun c => s3b_le _ (he c) _
  have hne' : f 0 ≠ 0 ∨ f 1 ≠ 0 ∨ f 2 ≠ 0 := by
    obtain ⟨c, hc⟩ := hne
    have hz : ∀ c', f c' = 0 → e c' = 0 := by
      intro c' h0; simp only [hfdef, fcode] at h0; split_ifs at h0 with h' <;> first | exact h' | omega
    fin_cases c
    · left; exact fun h => hc (hz 0 h)
    · right; left; exact fun h => hc (hz 1 h)
    · right; right; exact fun h => hc (hz 2 h)
  have hk := s3_spec (f 0) (f 1) (f 2) (hf3 0) (hf3 1) (hf3 2) hne' (row 0) (row 1) (row 2)
    (hmem 0) (hmem 1) (hmem 2)
  have e0 := hw 0
  have e1 := hw 1
  have e2 := hw 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  rw [← e0, ← e1, ← e2] at hk
  rw [Fin.sum_univ_three]
  exact hk.trans (Nat.add_le_add (Nat.add_le_add (Nat.pow_le_pow_left (hb 0) 2)
    (Nat.pow_le_pow_left (hb 1) 2)) (Nat.pow_le_pow_left (hb 2) 2))

/-! ## The level `K = 1` (`3^K < 4`): a direct check of the `27` points of `P_3` -/

/-- The first six coefficients of `g` (from the closed form `S3_M`, `b = 0`). -/
def s3gL : List (ZMod 3) := tmul 6 (tsemLS 6 (S3Mn 0 0)) (List.replicate 6 1)

/-- The first six coefficients of `z_c = c + U`. -/
def s3zL (c : Fin 3) : List (ZMod 3) := tadd 6 (tconst 6 ((c : ℕ) : ZMod 3)) (UL3 6)

lemma s3g_rep : TRep 6 s3gL S3g := by
  have hm := mk1_mul3'
  have e : S3g = tsemS (S3Mn 0 0) * PowerSeries.mk 1 := by
    have h := S3_M 0 0
    simp only [frameM, Fin.val_zero, pow_zero, mul_one] at h
    rw [← h]
    linear_combination S3g * hm.symm
  have h1 : TRep 6 (List.replicate 6 (1 : ZMod 3)) (PowerSeries.mk 1) := fun n hn => by
    simp only [lget, coeff_mk, List.getD_eq_getElem?_getD, List.getElem?_replicate, hn, ite_true,
      Option.getD_some]; rfl
  intro n hn
  rw [e, s3gL, tmul_rep (tsemLS_rep 6 _) h1 n hn]

lemma s3z_rep (c : Fin 3) : TRep 6 (s3zL c) (S3z c) := tadd_rep (tconst_rep 6 _) (UL3_rep 6)

/-- The first six digits of the points `y(v)`, `v < 27`, as an integer (`cellIdx … 6`). -/
def s3cell6 (v : ℕ) (c : Fin 3) : ℕ :=
  ∑ n : Fin 6, (∑ k ∈ range (v + 1),
    cget (tcols 6 27 s3gL (s3zL c)) k n * idxDigit (zcode 3) v k).val * 3 ^ (6 - 1 - (n : ℕ))

lemma cell6S (v : ℕ) (hv : v < 27) (c : Fin 3) : cellIdx (zcode 3) S3gen v c 6 = s3cell6 v c := by
  unfold cellIdx s3cell6
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [z3enc]
  congr 2
  unfold seqDigit
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 27 := by have := Finset.mem_range.mp hk; omega
  rw [show S3gen c n k = _ from ssGen_entry (fun _ => S3g) S3z c s3g_rep (s3z_rep c) n k n.isLt hk']

set_option maxRecDepth 100000 in
/-- Every two of the `27` points of `P_3` are at least `42` six-digit cells apart in one coordinate
(on the circle of `729` cells). -/
theorem s3_cell6_far : ∀ v w : Fin 27, v ≠ w → ∃ c : Fin 3,
    42 ≤ ((s3cell6 v c : ℤ) - s3cell6 w c).natAbs ∧
      ((s3cell6 v c : ℤ) - s3cell6 w c).natAbs + 42 ≤ 729 := by
  decide +kernel

/-- **`thm:S3`, level `K = 1`**: `c(P_3) ≥ √134917/6561` (every pair of the `27` points has a coordinate
with toroidal gap `≥ 41/729`, so `c(P_3) ≥ 123/729 = 0.168`). -/
theorem S3_sep_one : SepAtLevel 3 3 1 (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561) := by
  intro v w hv hw hvw
  have hv27 : v < 27 := by simpa using hv
  have hw27 : w < 27 := by simpa using hw
  obtain ⟨c, hc1, hc2⟩ := s3_cell6_far ⟨v, hv27⟩ ⟨w, hw27⟩ (fun h => hvw (congrArg Fin.val h))
  have cv := coord_cell (by norm_num : 2 ≤ 3) (zcode 3) S3gen v c 6
  have cw := coord_cell (by norm_num : 2 ≤ 3) (zcode 3) S3gen w c 6
  rw [cell6S v hv27] at cv
  rw [cell6S w hw27] at cw
  simp only [Fin.val_mk] at hc1 hc2
  zify at hc1 hc2
  have hd1 : (42 : ℝ) ≤ |(s3cell6 v c : ℝ) - s3cell6 w c| := by exact_mod_cast hc1
  have hd2 : |(s3cell6 v c : ℝ) - s3cell6 w c| + 42 ≤ (3 : ℝ) ^ 6 := by
    norm_num; exact_mod_cast hc2
  have ht := tor_cells (Q := (3 : ℝ) ^ 6) (by positivity) (by exact_mod_cast cv.1)
    (by exact_mod_cast cv.2) (by exact_mod_cast cw.1) (by exact_mod_cast cw.2) hd1 hd2
  have hT : Z3NetDGS.torCoord (seqPoint (zcode 3) S3gen v c) (seqPoint (zcode 3) S3gen w c) ≤
      Z3NetDGS.torDist2 (seqPoint (zcode 3) S3gen v) (seqPoint (zcode 3) S3gen w) := by
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => Z3NetDGS.torCoord (seqPoint (zcode 3) S3gen v j)
      (seqPoint (zcode 3) S3gen w j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ c)
  have hs : Real.sqrt 134917 ≤ 368 := by
    rw [show (368 : ℝ) = Real.sqrt (368 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  push_cast
  norm_num at ht
  nlinarith

/-! ## `thm:S3` -/

lemma S3_LB_le_one : Real.sqrt 134917 / 6561 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  rw [show (6561 : ℝ) = Real.sqrt (6561 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma S3_LB_pos : 0 < Real.sqrt 134917 / 6561 := by positivity

/-- **`thm:S3`** (separation): `c(P_{3K}) ≥ √134917/3^8 = 0.0559839…` for every `K ≥ 1`. -/
theorem S3_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 3 3 K (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561) := by
  rcases Nat.lt_or_ge K 2 with h | h
  · obtain rfl : K = 1 := by omega
    exact S3_sep_one
  have hK4 : 4 ≤ 3 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
  have hc := cert_prime S3gen K 8 hK4 (S3_net (3 * K) 0) (lawD (fun _ => S3g) S3z S3G)
    (fun i _ l h1 h2 c c' => S3_law K i l h1 h2 c c') (Real.sqrt 134917 / 6561) ?_
  · rwa [min_eq_right S3_LB_le_one] at hc
  rintro e l ⟨he, hne, hl⟩
  have hb := S3_cert_lb e l he hne (fun c => (hl c).1)
  rewrite [Fin.sum_univ_three] at hb
  unfold certTerm
  rewrite [Fin.sum_univ_three]
  generalize gapNum (zcode 3) 8 (e 0) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l 0) = A at hb ⊢
  generalize gapNum (zcode 3) 8 (e 1) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l 1) = B at hb ⊢
  generalize gapNum (zcode 3) 8 (e 2) (certSigmaP (lawD (fun _ => S3g) S3z S3G) 8 e l 2) = D at hb ⊢
  apply Real.le_sqrt_of_sq_le
  have hb' : (134917 : ℝ) ≤ (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + (D : ℝ) ^ 2 := by exact_mod_cast hb
  rw [div_pow, Real.sq_sqrt (by norm_num), div_pow, div_pow, div_pow, ← add_div, ← add_div]
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

/-- **`thm:S3`** (all `N`): `δ(P_{[N]}) ≥ 0.0186 · N^{-1/3}` for every `N ≥ 2`. -/
theorem S3_allN : SepAllN 3 (seqPoint (zcode 3) S3gen) (186 / 10000) := by
  have h := prefix_sep 3 3 (by norm_num) (by norm_num) (seqPoint (zcode 3) S3gen) _ S3_LB_pos.le
    (fun K hK => S3_sep K hK)
  refine sepAllN_mono _ ?_ h
  have hs : (3673 / 10 : ℝ) ≤ Real.sqrt 134917 := Real.le_sqrt_of_sq_le (by norm_num)
  push_cast
  rw [div_div, le_div_iff₀ (by norm_num)]
  nlinarith

/-- **`thm:S3`** (mesh ratio): `h(P_{[N]}) ≤ 93 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem S3_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode 3) S3gen)) ≤
      93 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 3) S3gen))) := by
  have h := prefix_mesh (zcode 3) S3gen (by norm_num) (by norm_num) S3_net _ S3_LB_pos
    (fun K hK => S3_sep K hK) N hN
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h3 : Real.sqrt 3 ≤ 173206 / 100000 := by
      rw [show (173206 / 100000 : ℝ) = Real.sqrt ((173206 / 100000) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs : (3673 / 10 : ℝ) ≤ Real.sqrt 134917 := Real.le_sqrt_of_sq_le (by norm_num)
    push_cast
    rw [div_le_iff₀ S3_LB_pos]
    nlinarith
  · have : 0 ≤ Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode 3) S3gen)) :=
      Real.iInf_nonneg fun _ => div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    linarith

/-- **`lem:frames`(a) for `H = 𝔽_3`** (`S3_frames` with `IsP3` unfolded): `U = -∑_{k≥0} x^{3^k}` satisfies
`U³ - U = x`, `U(0) = 0`, the Mahler equation `U(x) = U(x³) - x`, and `[x^n] U = -1` exactly at the powers
of `3` (`0` otherwise). -/
theorem S3_frames_char : U3 ^ 3 - U3 = X ∧ constantCoeff U3 = 0 ∧ U3 = expand 3 three_ne_zero U3 - X ∧
    (∀ k, coeff (3 ^ k) U3 = -1) ∧ ∀ n, (¬ ∃ k, 3 ^ k = n) → coeff n U3 = 0 :=
  S3_frames

end GeoSeq
