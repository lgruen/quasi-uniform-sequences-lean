/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S4Law
public import GeoSeq.S4AutoA
public import GeoSeq.S4AutoB
public import GeoSeq.S4AutoC
public import GeoSeq.S4AutoD
public import GeoSeq.S4Check
public import GeoSeq.K4Cert

@[expose] public section

/-!
# GeoSeq stage S8: the exact response sets and the certificate of `thm:S4`

* The automaton certificate (`prop:automaton` for `thm:S4`, source coordinate `0`; the other sources by
  the translation symmetry `S4_rot`). `S4_resp`: for every `l ≥ 1` the pair column
  `(D_i(l)[c][0], D_i(l-1)[c][0])` is one of the `80` listed ones; `S4_resp_card`: exactly these occur.
* The change columns of `eq:carrychange` (`S4_change`): `120` binary words per moving coordinate.
* The certificate minimum `952 = min ∑_c (4^5 f_5(e_c, σ_c))²` (`S4_cert_lb`): kernel checks with
  buckets on the five leading bits (a moving coordinate whose five leading bits are not all `1` has a
  bound `≥ 32 > √952`, `s4_far`), and `thm:S4`: `S4_sep` (every `K ≥ 1`), `S4_allN`, `S4_mesh`.
-/

namespace GeoSeq

open Finset PowerSeries

lemma getD_getElem4 {α : Type*} (L : List α) (t : ℕ) (d : α) (h : t < L.length) : L.getD t d = L[t] := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## The automaton certificate (source coordinate `0`) -/

theorem s4_closeA : ∀ s : Fin 170, ∀ r : Fin 4, (S4tA.getD s []).getD r 0 < 170 ∧ stepVU r (S4Av.getD s []) = S4Av.getD ((S4tA.getD s []).getD r 0) [] := by
  intro s
  have h : (0 ≤ s.val ∧ s.val < 20) ∨ (20 ≤ s.val ∧ s.val < 40) ∨ (40 ≤ s.val ∧ s.val < 60) ∨ (60 ≤ s.val ∧ s.val < 80) ∨ (80 ≤ s.val ∧ s.val < 100) ∨ (100 ≤ s.val ∧ s.val < 120) ∨ (120 ≤ s.val ∧ s.val < 140) ∨ (140 ≤ s.val ∧ s.val < 160) ∨ (160 ≤ s.val ∧ s.val < 170) := by omega
  rcases h with h | h | h | h | h | h | h | h | h
  · exact s4_closeA_0 s (by omega) (by omega)
  · exact s4_closeA_1 s (by omega) (by omega)
  · exact s4_closeA_2 s (by omega) (by omega)
  · exact s4_closeA_3 s (by omega) (by omega)
  · exact s4_closeA_4 s (by omega) (by omega)
  · exact s4_closeA_5 s (by omega) (by omega)
  · exact s4_closeA_6 s (by omega) (by omega)
  · exact s4_closeA_7 s (by omega) (by omega)
  · exact s4_closeA_8 s (by omega) (by omega)

theorem s4_read : ∀ s : Fin 170, S4out.getD s 0 < 80 ∧ (S4Av.getD s []).map acoefU = (S4tup.getD (S4out.getD s 0) []).map n2f := by
  intro s
  have h : (0 ≤ s.val ∧ s.val < 34) ∨ (34 ≤ s.val ∧ s.val < 68) ∨ (68 ≤ s.val ∧ s.val < 102) ∨ (102 ≤ s.val ∧ s.val < 136) ∨ (136 ≤ s.val ∧ s.val < 170) := by omega
  rcases h with h | h | h | h | h
  · exact s4_read_0 s (by omega) (by omega)
  · exact s4_read_1 s (by omega) (by omega)
  · exact s4_read_2 s (by omega) (by omega)
  · exact s4_read_3 s (by omega) (by omega)
  · exact s4_read_4 s (by omega) (by omega)

theorem s4_wit : ∀ t : Fin 80, (∀ d ∈ S4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (S4wit.getD t []) ∧ (readVU (S4wit.getD t []) (initVU 0)).map acoefU = (S4tup.getD t []).map n2f := by
  intro t
  have h : (0 ≤ t.val ∧ t.val < 20) ∨ (20 ≤ t.val ∧ t.val < 40) ∨ (40 ≤ t.val ∧ t.val < 60) ∨ (60 ≤ t.val ∧ t.val < 80) := by omega
  rcases h with h | h | h | h
  · exact s4_wit_0 t (by omega) (by omega)
  · exact s4_wit_1 t (by omega) (by omega)
  · exact s4_wit_2 t (by omega) (by omega)
  · exact s4_wit_3 t (by omega) (by omega)

theorem s4_distinct : ∀ t : Fin 80, ∀ t' : Fin 80, t ≠ t' → ∃ k : Fin 40, S4tupv t k ≠ S4tupv t' k := by
  intro t
  have h : (0 ≤ t.val ∧ t.val < 20) ∨ (20 ≤ t.val ∧ t.val < 40) ∨ (40 ≤ t.val ∧ t.val < 60) ∨ (60 ≤ t.val ∧ t.val < 80) := by omega
  rcases h with h | h | h | h
  · exact s4_distinct_0 t (by omega) (by omega)
  · exact s4_distinct_1 t (by omega) (by omega)
  · exact s4_distinct_2 t (by omega) (by omega)
  · exact s4_distinct_3 t (by omega) (by omega)


/-! ## The response pairs -/

lemma S4_lawD_zero (i : ℕ) (hi : i < 5) (c : Fin 4) : lawD (fun _ => S4g) S4z S4G i 0 c 0 = 0 := by
  rw [← S4_init i hi c 0 0, zero_add, ← acoefU_eq]
  exact s4_zero ⟨i, hi⟩ c

lemma S4Dr_prev (i : ℕ) (hi : i < 5) (c : Fin 4) (l : ℕ) (hl : 1 ≤ l) :
    coeff (l + 5) (esemU (initSU i c 0 1)) = S4Dr i (l - 1) c 0 := by
  rw [S4_init1 i hi c 0 l hl, S4Dr]
  by_cases h : l - 1 = 0
  · rw [if_pos h, h, S4_lawD_zero i hi c]
  · rw [if_neg h]

lemma valsU_initVU (l i : ℕ) (hl : 1 ≤ l) (hi : i < 5) (c : Fin 4) :
    (valsU (initVU 0) l).getD (4 * i + c) 0 = lawD (fun _ => S4g) S4z S4G i l c 0 ∧
    (valsU (initVU 0) l).getD (20 + 4 * i + c) 0 = S4Dr i (l - 1) c 0 := by
  have hk : 4 * i + (c : ℕ) < 40 := by omega
  have hk' : 20 + 4 * i + (c : ℕ) < 40 := by omega
  simp only [valsU, initVU, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
  simp only [Option.map_some, Option.getD_some, Function.comp_apply]
  have e1 : (4 * i + (c : ℕ)) % 20 / 4 = i := by omega
  have e2 : (20 + 4 * i + (c : ℕ)) % 20 / 4 = i := by omega
  have e3 : (⟨(4 * i + (c : ℕ)) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = c := by
    ext; simp only [Fin.val_mk]; omega
  have e4 : (⟨(20 + 4 * i + (c : ℕ)) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = c := by
    ext; simp only [Fin.val_mk]; omega
  have e5 : (4 * i + (c : ℕ)) / 20 = 0 := by omega
  have e6 : (20 + 4 * i + (c : ℕ)) / 20 = 1 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  exact ⟨S4_init i hi c 0 l, S4Dr_prev i hi c l hl⟩

/-- **`prop:automaton` for `thm:S4`** (`j = 5`, source `0`): for every carry length `l ≥ 1` the pair
column `(D_i(l)[c][0], D_i(l-1)[c][0])_{i<5, c<4}` is one of the `80` listed tuples. -/
theorem S4_resp (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < 80, ∀ i < 5, ∀ c : Fin 4, lawD (fun _ => S4g) S4z S4G i l c 0 = S4tupv t (4 * i + c) ∧
      S4Dr i (l - 1) c 0 = S4tupv t (20 + 4 * i + c) := by
  obtain ⟨s', hs', h⟩ := reach_BU S4Av S4Bv S4tA S4tB 170 4 s4_closeA s4_closeB l 0 hl (by norm_num)
  rw [s4_init] at h
  obtain ⟨h1, h2⟩ := s4_read ⟨s', hs'⟩
  refine ⟨_, h1, fun i hi c => ?_⟩
  obtain ⟨a, b⟩ := valsU_initVU l i hl hi c
  rw [h, valsU_zero, h2, getD_map_n2f] at a b
  exact ⟨a.symm, b.symm⟩

/-- **`prop:automaton` for `thm:S4`, exactness**: every listed pair column occurs for some `l ≥ 1`. -/
theorem S4_resp_occurs (t : ℕ) (ht : t < 80) :
    ∃ l, 1 ≤ l ∧ ∀ i < 5, ∀ c : Fin 4, lawD (fun _ => S4g) S4z S4G i l c 0 = S4tupv t (4 * i + c) ∧
      S4Dr i (l - 1) c 0 = S4tupv t (20 + 4 * i + c) := by
  obtain ⟨hds, h1, h2⟩ := s4_wit ⟨t, ht⟩
  refine ⟨Nat.ofDigits 4 (S4wit.getD t []), h1, fun i hi c => ?_⟩
  obtain ⟨a, b⟩ := valsU_initVU _ i h1 hi c
  rw [valsU_read _ hds, valsU_zero, h2, getD_map_n2f] at a b
  exact ⟨a.symm, b.symm⟩

/-- **`prop:automaton` for `thm:S4`, the count** (`j = 5`): the pair columns
`(D_i(l)[c][0], D_i(l-1)[c][0])_{i<5, c<4}` over all `l ≥ 1` form a set of exactly `80` elements. -/
theorem S4_resp_card :
    Set.ncard {D : Fin 5 → Fin 4 → F4 × F4 | ∃ l, 1 ≤ l ∧ ∀ i : Fin 5, ∀ c : Fin 4,
      D i c = (lawD (fun _ => S4g) S4z S4G i l c 0, S4Dr i (l - 1) c 0)} = 80 := by
  let f : Fin 80 → (Fin 5 → Fin 4 → F4 × F4) := fun t i c =>
    (S4tupv t (4 * i + c), S4tupv t (20 + 4 * i + c))
  have hset : {D : Fin 5 → Fin 4 → F4 × F4 | ∃ l, 1 ≤ l ∧ ∀ i : Fin 5, ∀ c : Fin 4,
      D i c = (lawD (fun _ => S4g) S4z S4G i l c 0, S4Dr i (l - 1) c 0)} = Set.range f := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨l, hl, hD⟩
      obtain ⟨t, ht, h⟩ := S4_resp l hl
      refine ⟨⟨t, ht⟩, funext fun i => funext fun c => ?_⟩
      rw [hD i c, (h i i.isLt c).1, (h i i.isLt c).2]
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨l, hl, h⟩ := S4_resp_occurs t ht
      exact ⟨l, hl, fun i c => by rw [(h i i.isLt c).1, (h i i.isLt c).2]⟩
  have hinj : Function.Injective f := by
    intro t t' htt
    by_contra hne
    obtain ⟨k, hk⟩ := s4_distinct t t' hne
    apply hk
    by_cases hk1 : (k : ℕ) < 20
    · have e := congrArg Prod.fst (congrFun (congrFun htt ⟨(k : ℕ) / 4, by omega⟩) ⟨(k : ℕ) % 4, by omega⟩)
      simp only [f, Fin.val_mk] at e
      rw [show (k : ℕ) = 4 * ((k : ℕ) / 4) + (k : ℕ) % 4 by omega]; exact e
    · have e := congrArg Prod.snd
        (congrFun (congrFun htt ⟨((k : ℕ) - 20) / 4, by omega⟩) ⟨((k : ℕ) - 20) % 4, by omega⟩)
      simp only [f, Fin.val_mk] at e
      rw [show (k : ℕ) = 20 + 4 * (((k : ℕ) - 20) / 4) + ((k : ℕ) - 20) % 4 by omega]; exact e
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## The change columns (`eq:carrychange`) -/

lemma S4Dr_rot (i l : ℕ) (c c' : Fin 4) : S4Dr i l c c' = S4Dr i l (fxor c c') 0 := by
  unfold S4Dr
  split_ifs
  · rfl
  · exact S4_rot i l c c'

lemma S4Dr_pos (i l : ℕ) (hl : l ≠ 0) (c c' : Fin 4) :
    S4Dr i l c c' = lawD (fun _ => S4g) S4z S4G i l c c' := by
  rw [S4Dr, if_neg hl]

/-- **The change columns of `thm:S4`** (`eq:carrychange`, `Δ(ȳ) = ω²`, `Δ(y) ∈ {1, ω²}`): for every carry
length `l ≥ 1` and stop digit `y`, the change of the geometric digit `K + i` of coordinate `c` caused by a
step of coordinate `c'` is entry `(i, c ⊕ c')` of one of the listed change columns of source `0`. -/
theorem S4_change (l : ℕ) (hl : 1 ≤ l) (y : F4) : ∃ t < 80, ∃ ty < 2, ∀ i < 5, ∀ c c' : Fin 4,
    carryChange f4code S4Dr i l y c c' = chgU t ty i (fxor c c') := by
  obtain ⟨t, ht, h⟩ := S4_resp l hl
  have hl0 : l ≠ 0 := by omega
  rcases digInc_cases4 y with hy | hy
  · refine ⟨t, ht, 1, by norm_num, fun i hi c c' => ?_⟩
    obtain ⟨h1, h2⟩ := h i hi (fxor c c')
    unfold carryChange chgU
    rw [digInc_top4, hy, S4Dr_rot i (l - 1), S4Dr_rot i l, S4Dr_pos i l hl0, h1, h2, if_neg one_ne_zero]
    exact f4_chg1 _ _
  · refine ⟨t, ht, 0, by norm_num, fun i hi c c' => ?_⟩
    obtain ⟨h1, h2⟩ := h i hi (fxor c c')
    unfold carryChange chgU
    rw [digInc_top4, hy, S4Dr_rot i (l - 1), S4Dr_rot i l, S4Dr_pos i l hl0, h1, h2, if_pos rfl]
    exact f4_chg2 _ _

/-! ## Soundness of the bucket checks -/

lemma xor_key (a b : ℕ) : (a ^^^ b) / 32 = a / 32 ^^^ b / 32 := by
  have h := Nat.xor_div_two_pow (a := a) (b := b) (n := 5)
  norm_num at h
  exact h

lemma xor_solve (x y : ℕ) (h : x ^^^ y = 31) : y = 31 ^^^ x := by
  rw [← h, Nat.xor_comm x y, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- A moving coordinate whose five leading bits are not all `1` has a bound `≥ 32`. -/
lemma s4_far (w : ℕ) (hw : w < 1024) (hk : w / 32 ≠ 31) : 32 ≤ s4b true w := by
  unfold s4b; simp only [ite_true]; omega

lemma s4_sum_big (x y z u : ℕ) (h : 32 ≤ x ∨ 32 ≤ y ∨ 32 ≤ z ∨ 32 ≤ u) :
    952 ≤ x ^ 2 + y ^ 2 + z ^ 2 + u ^ 2 := by
  rcases h with h | h | h | h <;> nlinarith

lemma xor3_lt (a b d : ℕ) (ha : a < 1024) (hb : b < 1024) (hd : d < 1024) : a ^^^ b ^^^ d < 1024 :=
  Nat.xor_lt_two_pow (n := 10) (Nat.xor_lt_two_pow (n := 10) ha hb) hd

/-- One coordinate of the bucket checks: if the third key does not complete `31`, the bound is `≥ 32`. -/
lemma s4_coordfar (wa wb wd : ℕ) (ha : wa < 1024) (hb : wb < 1024) (hd : wd < 1024)
    (hk : wd / 32 ≠ 31 ^^^ (wa / 32 ^^^ wb / 32)) : 32 ≤ s4b true (wa ^^^ wb ^^^ wd) := by
  refine s4_far _ (xor3_lt _ _ _ ha hb hd) ?_
  rw [xor_key, xor_key]
  intro h
  exact hk (xor_solve _ _ h)

lemma s4Z_mem (c' : ℕ) (hc : c' < 4) (d : List ℕ) (hd : d ∈ S4Z c') :
    ∃ t < 120, d = (S4Z c').getD t [] := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hd
  obtain ⟨hlen, -⟩ := s4_Zperm ⟨c', hc⟩
  exact ⟨t, hlen ▸ ht, (getD_getElem4 _ _ _ ht).symm⟩

lemma s4Z_lt (c' : ℕ) (hc : c' < 4) (d : List ℕ) (hd : d ∈ S4Z c') (c : ℕ) (hc4 : c < 4) :
    d.getD c 0 < 1024 := by
  obtain ⟨t, ht, rfl⟩ := s4Z_mem c' hc d hd
  exact ((s4_Zperm ⟨c', hc⟩).2 ⟨t, ht⟩ ⟨c, hc4⟩).2

lemma s4part_spec (m0 m1 m2 m3 : Bool) (h : s4part m0 m1 m2 m3 = true) (a b c d : List ℕ)
    (ha : a ∈ s4opt m0 0) (hb : b ∈ s4opt m1 1) (hc : c ∈ s4opt m2 2) (hd : d ∈ s4opt m3 3) :
    952 ≤ s4b m0 (a.getD 0 0 ^^^ b.getD 0 0 ^^^ c.getD 0 0 ^^^ d.getD 0 0) ^ 2 +
      s4b m1 (a.getD 1 0 ^^^ b.getD 1 0 ^^^ c.getD 1 0 ^^^ d.getD 1 0) ^ 2 +
      s4b m2 (a.getD 2 0 ^^^ b.getD 2 0 ^^^ c.getD 2 0 ^^^ d.getD 2 0) ^ 2 +
      s4b m3 (a.getD 3 0 ^^^ b.getD 3 0 ^^^ c.getD 3 0 ^^^ d.getD 3 0) ^ 2 := by
  unfold s4part at h
  rw [List.all_eq_true] at h
  have h1 := h a ha; rw [List.all_eq_true] at h1
  have h2 := h1 b hb; rw [List.all_eq_true] at h2
  have h3 := h2 c hc; rw [List.all_eq_true] at h3
  have h4 := h3 d hd
  unfold s4ok at h4
  exact of_decide_eq_true h4

lemma getD_range_map (f : ℕ → ℕ) (c : ℕ) (hc : c < 4) : ((List.range 4).map f).getD c 0 = f c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]; rfl

lemma s4three_spec0 (a b d : List ℕ) (ha : a ∈ S4Z 0) (hb : b ∈ S4Z 1) (hd : d ∈ S4Z 2) :
    952 ≤ s4b (decide ((0 : ℕ) ≠ 3)) (a.getD 0 0 ^^^ b.getD 0 0 ^^^ d.getD 0 0) ^ 2 +
      s4b (decide ((1 : ℕ) ≠ 3)) (a.getD 1 0 ^^^ b.getD 1 0 ^^^ d.getD 1 0) ^ 2 +
      s4b (decide ((2 : ℕ) ≠ 3)) (a.getD 2 0 ^^^ b.getD 2 0 ^^^ d.getD 2 0) ^ 2 +
      s4b (decide ((3 : ℕ) ≠ 3)) (a.getD 3 0 ^^^ b.getD 3 0 ^^^ d.getD 3 0) ^ 2 := by
  have h := s4_three0
  unfold s4three at h
  rw [List.all_eq_true] at h
  have h1 := h a ha; rw [List.all_eq_true] at h1
  have h2 := h1 b hb; rw [List.all_eq_true] at h2
  have la := fun c hc => s4Z_lt 0 (by norm_num) a ha c hc
  have lb := fun c hc => s4Z_lt 1 (by norm_num) b hb c hc
  have ld := fun c hc => s4Z_lt 2 (by norm_num) d hd c hc
  have hbk : d ∈ s4bk3 0 (d.getD 0 0 / 32) (d.getD 1 0 / 32) := by
    obtain ⟨t, ht, rfl⟩ := s4Z_mem 2 (by norm_num) d hd
    exact s4_bk3_0 ⟨t, ht⟩
  by_cases hk : d.getD 0 0 / 32 = 31 ^^^ (a.getD 0 0 / 32 ^^^ b.getD 0 0 / 32) ∧
      d.getD 1 0 / 32 = 31 ^^^ (a.getD 1 0 / 32 ^^^ b.getD 1 0 / 32)
  · rw [hk.1, hk.2] at hbk
    have hx := h2 d hbk
    split_ifs at hx with hk3
    · unfold s4ok at hx; exact of_decide_eq_true hx
    · apply s4_sum_big
      have := s4_coordfar _ _ _ (la 2 (by norm_num)) (lb 2 (by norm_num)) (ld 2 (by norm_num)) hk3
      simp only [show ((2 : ℕ) ≠ 3) = True by norm_num, decide_true]
      right; right; left
      exact this
  · apply s4_sum_big
    rcases not_and_or.mp hk with hk1 | hk2
    · have := s4_coordfar _ _ _ (la 0 (by norm_num)) (lb 0 (by norm_num)) (ld 0 (by norm_num)) hk1
      simp only [show ((0 : ℕ) ≠ 3) = True by norm_num, decide_true]
      left
      exact this
    · have := s4_coordfar _ _ _ (la 1 (by norm_num)) (lb 1 (by norm_num)) (ld 1 (by norm_num)) hk2
      simp only [show ((1 : ℕ) ≠ 3) = True by norm_num, decide_true]
      right; left
      exact this

lemma s4three_spec1 (a b d : List ℕ) (ha : a ∈ S4Z 0) (hb : b ∈ S4Z 1) (hd : d ∈ S4Z 3) :
    952 ≤ s4b (decide ((0 : ℕ) ≠ 2)) (a.getD 0 0 ^^^ b.getD 0 0 ^^^ d.getD 0 0) ^ 2 +
      s4b (decide ((1 : ℕ) ≠ 2)) (a.getD 1 0 ^^^ b.getD 1 0 ^^^ d.getD 1 0) ^ 2 +
      s4b (decide ((2 : ℕ) ≠ 2)) (a.getD 2 0 ^^^ b.getD 2 0 ^^^ d.getD 2 0) ^ 2 +
      s4b (decide ((3 : ℕ) ≠ 2)) (a.getD 3 0 ^^^ b.getD 3 0 ^^^ d.getD 3 0) ^ 2 := by
  have h := s4_three1
  unfold s4three at h
  rw [List.all_eq_true] at h
  have h1 := h a ha; rw [List.all_eq_true] at h1
  have h2 := h1 b hb; rw [List.all_eq_true] at h2
  have la := fun c hc => s4Z_lt 0 (by norm_num) a ha c hc
  have lb := fun c hc => s4Z_lt 1 (by norm_num) b hb c hc
  have ld := fun c hc => s4Z_lt 3 (by norm_num) d hd c hc
  have hbk : d ∈ s4bk3 1 (d.getD 0 0 / 32) (d.getD 1 0 / 32) := by
    obtain ⟨t, ht, rfl⟩ := s4Z_mem 3 (by norm_num) d hd
    exact s4_bk3_1 ⟨t, ht⟩
  by_cases hk : d.getD 0 0 / 32 = 31 ^^^ (a.getD 0 0 / 32 ^^^ b.getD 0 0 / 32) ∧
      d.getD 1 0 / 32 = 31 ^^^ (a.getD 1 0 / 32 ^^^ b.getD 1 0 / 32)
  · rw [hk.1, hk.2] at hbk
    have hx := h2 d hbk
    split_ifs at hx with hk3
    · unfold s4ok at hx; exact of_decide_eq_true hx
    · apply s4_sum_big
      have := s4_coordfar _ _ _ (la 3 (by norm_num)) (lb 3 (by norm_num)) (ld 3 (by norm_num)) hk3
      simp only [show ((3 : ℕ) ≠ 2) = True by norm_num, decide_true]
      right; right; right
      exact this
  · apply s4_sum_big
    rcases not_and_or.mp hk with hk1 | hk2
    · have := s4_coordfar _ _ _ (la 0 (by norm_num)) (lb 0 (by norm_num)) (ld 0 (by norm_num)) hk1
      simp only [show ((0 : ℕ) ≠ 2) = True by norm_num, decide_true]
      left
      exact this
    · have := s4_coordfar _ _ _ (la 1 (by norm_num)) (lb 1 (by norm_num)) (ld 1 (by norm_num)) hk2
      simp only [show ((1 : ℕ) ≠ 2) = True by norm_num, decide_true]
      right; left
      exact this

lemma s4three_spec2 (a b d : List ℕ) (ha : a ∈ S4Z 0) (hb : b ∈ S4Z 2) (hd : d ∈ S4Z 3) :
    952 ≤ s4b (decide ((0 : ℕ) ≠ 1)) (a.getD 0 0 ^^^ b.getD 0 0 ^^^ d.getD 0 0) ^ 2 +
      s4b (decide ((1 : ℕ) ≠ 1)) (a.getD 1 0 ^^^ b.getD 1 0 ^^^ d.getD 1 0) ^ 2 +
      s4b (decide ((2 : ℕ) ≠ 1)) (a.getD 2 0 ^^^ b.getD 2 0 ^^^ d.getD 2 0) ^ 2 +
      s4b (decide ((3 : ℕ) ≠ 1)) (a.getD 3 0 ^^^ b.getD 3 0 ^^^ d.getD 3 0) ^ 2 := by
  have h := s4_three2
  unfold s4three at h
  rw [List.all_eq_true] at h
  have h1 := h a ha; rw [List.all_eq_true] at h1
  have h2 := h1 b hb; rw [List.all_eq_true] at h2
  have la := fun c hc => s4Z_lt 0 (by norm_num) a ha c hc
  have lb := fun c hc => s4Z_lt 2 (by norm_num) b hb c hc
  have ld := fun c hc => s4Z_lt 3 (by norm_num) d hd c hc
  have hbk : d ∈ s4bk3 2 (d.getD 0 0 / 32) (d.getD 2 0 / 32) := by
    obtain ⟨t, ht, rfl⟩ := s4Z_mem 3 (by norm_num) d hd
    exact s4_bk3_2 ⟨t, ht⟩
  by_cases hk : d.getD 0 0 / 32 = 31 ^^^ (a.getD 0 0 / 32 ^^^ b.getD 0 0 / 32) ∧
      d.getD 2 0 / 32 = 31 ^^^ (a.getD 2 0 / 32 ^^^ b.getD 2 0 / 32)
  · rw [hk.1, hk.2] at hbk
    have hx := h2 d hbk
    split_ifs at hx with hk3
    · unfold s4ok at hx; exact of_decide_eq_true hx
    · apply s4_sum_big
      have := s4_coordfar _ _ _ (la 3 (by norm_num)) (lb 3 (by norm_num)) (ld 3 (by norm_num)) hk3
      simp only [show ((3 : ℕ) ≠ 1) = True by norm_num, decide_true]
      right; right; right
      exact this
  · apply s4_sum_big
    rcases not_and_or.mp hk with hk1 | hk2
    · have := s4_coordfar _ _ _ (la 0 (by norm_num)) (lb 0 (by norm_num)) (ld 0 (by norm_num)) hk1
      simp only [show ((0 : ℕ) ≠ 1) = True by norm_num, decide_true]
      left
      exact this
    · have := s4_coordfar _ _ _ (la 2 (by norm_num)) (lb 2 (by norm_num)) (ld 2 (by norm_num)) hk2
      simp only [show ((2 : ℕ) ≠ 1) = True by norm_num, decide_true]
      right; right; left
      exact this

lemma s4three_spec3 (a b d : List ℕ) (ha : a ∈ S4Z 1) (hb : b ∈ S4Z 2) (hd : d ∈ S4Z 3) :
    952 ≤ s4b (decide ((0 : ℕ) ≠ 0)) (a.getD 0 0 ^^^ b.getD 0 0 ^^^ d.getD 0 0) ^ 2 +
      s4b (decide ((1 : ℕ) ≠ 0)) (a.getD 1 0 ^^^ b.getD 1 0 ^^^ d.getD 1 0) ^ 2 +
      s4b (decide ((2 : ℕ) ≠ 0)) (a.getD 2 0 ^^^ b.getD 2 0 ^^^ d.getD 2 0) ^ 2 +
      s4b (decide ((3 : ℕ) ≠ 0)) (a.getD 3 0 ^^^ b.getD 3 0 ^^^ d.getD 3 0) ^ 2 := by
  have h := s4_three3
  unfold s4three at h
  rw [List.all_eq_true] at h
  have h1 := h a ha; rw [List.all_eq_true] at h1
  have h2 := h1 b hb; rw [List.all_eq_true] at h2
  have la := fun c hc => s4Z_lt 1 (by norm_num) a ha c hc
  have lb := fun c hc => s4Z_lt 2 (by norm_num) b hb c hc
  have ld := fun c hc => s4Z_lt 3 (by norm_num) d hd c hc
  have hbk : d ∈ s4bk3 3 (d.getD 1 0 / 32) (d.getD 2 0 / 32) := by
    obtain ⟨t, ht, rfl⟩ := s4Z_mem 3 (by norm_num) d hd
    exact s4_bk3_3 ⟨t, ht⟩
  by_cases hk : d.getD 1 0 / 32 = 31 ^^^ (a.getD 1 0 / 32 ^^^ b.getD 1 0 / 32) ∧
      d.getD 2 0 / 32 = 31 ^^^ (a.getD 2 0 / 32 ^^^ b.getD 2 0 / 32)
  · rw [hk.1, hk.2] at hbk
    have hx := h2 d hbk
    split_ifs at hx with hk3
    · unfold s4ok at hx; exact of_decide_eq_true hx
    · apply s4_sum_big
      have := s4_coordfar _ _ _ (la 3 (by norm_num)) (lb 3 (by norm_num)) (ld 3 (by norm_num)) hk3
      simp only [show ((3 : ℕ) ≠ 0) = True by norm_num, decide_true]
      right; right; right
      exact this
  · apply s4_sum_big
    rcases not_and_or.mp hk with hk1 | hk2
    · have := s4_coordfar _ _ _ (la 1 (by norm_num)) (lb 1 (by norm_num)) (ld 1 (by norm_num)) hk1
      simp only [show ((1 : ℕ) ≠ 0) = True by norm_num, decide_true]
      right; left
      exact this
    · have := s4_coordfar _ _ _ (la 2 (by norm_num)) (lb 2 (by norm_num)) (ld 2 (by norm_num)) hk2
      simp only [show ((2 : ℕ) ≠ 0) = True by norm_num, decide_true]
      right; right; left
      exact this

lemma s4full_spec (a b d2 d3 : List ℕ) (ha : a ∈ S4Z 0) (hb : b ∈ S4Z 1) (hd2 : d2 ∈ S4Z 2)
    (hd3 : d3 ∈ S4Z 3) :
    952 ≤ s4b true (a.getD 0 0 ^^^ b.getD 0 0 ^^^ (d2.getD 0 0 ^^^ d3.getD 0 0)) ^ 2 +
      s4b true (a.getD 1 0 ^^^ b.getD 1 0 ^^^ (d2.getD 1 0 ^^^ d3.getD 1 0)) ^ 2 +
      s4b true (a.getD 2 0 ^^^ b.getD 2 0 ^^^ (d2.getD 2 0 ^^^ d3.getD 2 0)) ^ 2 +
      s4b true (a.getD 3 0 ^^^ b.getD 3 0 ^^^ (d2.getD 3 0 ^^^ d3.getD 3 0)) ^ 2 := by
  have h := s4_full
  unfold s4full at h
  rw [List.all_eq_true] at h
  have h1 := h a ha; rw [List.all_eq_true] at h1
  have h2 := h1 b hb; rw [List.all_eq_true] at h2
  have la := fun c hc => s4Z_lt 0 (by norm_num) a ha c hc
  have lb := fun c hc => s4Z_lt 1 (by norm_num) b hb c hc
  have l2 := fun c hc => s4Z_lt 2 (by norm_num) d2 hd2 c hc
  have l3 := fun c hc => s4Z_lt 3 (by norm_num) d3 hd3 c hc
  set p := (List.range 4).map (fun c => d2.getD c 0 ^^^ d3.getD c 0) with hp
  have hpc : ∀ c, c < 4 → p.getD c 0 = d2.getD c 0 ^^^ d3.getD c 0 := fun c hc => getD_range_map _ c hc
  have lp : ∀ c, c < 4 → p.getD c 0 < 1024 := fun c hc => by
    rw [hpc c hc]; exact Nat.xor_lt_two_pow (n := 10) (l2 c hc) (l3 c hc)
  have hbk : p ∈ (S4PB.getD (p.getD 0 0 / 32) []).getD (p.getD 1 0 / 32) [] := by
    obtain ⟨t2, ht2, rfl⟩ := s4Z_mem 2 (by norm_num) d2 hd2
    obtain ⟨t3, ht3, rfl⟩ := s4Z_mem 3 (by norm_num) d3 hd3
    rw [hpc 0 (by norm_num), hpc 1 (by norm_num)]
    exact s4_pb ⟨t2, ht2⟩ ⟨t3, ht3⟩
  rw [← hpc 0 (by norm_num), ← hpc 1 (by norm_num), ← hpc 2 (by norm_num), ← hpc 3 (by norm_num)]
  by_cases hk : p.getD 0 0 / 32 = 31 ^^^ (a.getD 0 0 / 32 ^^^ b.getD 0 0 / 32) ∧
      p.getD 1 0 / 32 = 31 ^^^ (a.getD 1 0 / 32 ^^^ b.getD 1 0 / 32)
  · rw [hk.1, hk.2] at hbk
    have hx := h2 p hbk
    split_ifs at hx with hk3
    · unfold s4ok at hx; exact of_decide_eq_true hx
    · apply s4_sum_big
      rcases not_and_or.mp hk3 with h3 | h3
      · right; right; left
        exact s4_coordfar _ _ _ (la 2 (by norm_num)) (lb 2 (by norm_num)) (lp 2 (by norm_num)) h3
      · right; right; right
        exact s4_coordfar _ _ _ (la 3 (by norm_num)) (lb 3 (by norm_num)) (lp 3 (by norm_num)) h3
  · apply s4_sum_big
    rcases not_and_or.mp hk with h3 | h3
    · left; exact s4_coordfar _ _ _ (la 0 (by norm_num)) (lb 0 (by norm_num)) (lp 0 (by norm_num)) h3
    · right; left; exact s4_coordfar _ _ _ (la 1 (by norm_num)) (lb 1 (by norm_num)) (lp 1 (by norm_num)) h3

/-! ## The certificate minimum -/

lemma enc_ite5 (p : Prop) [Decidable p] (f : Fin 5 → F4) :
    encVec f4code (if p then 0 else f) = if p then 0 else encVec f4code f := by
  split_ifs
  · exact encVec_zero4
  · rfl

lemma s4b_le (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (σ : Fin 5 → F4) :
    s4b (decide (e ≠ 0)) (encVec f4code σ) ≤ gapNum f4code 5 e σ := by
  unfold s4b
  by_cases h0 : e = 0
  · subst h0
    simpa using gapNum4_zero 5 σ
  · have hpm : e = 1 ∨ e = -1 := by omega
    have := gapNum4_pm 5 e hpm σ
    simp only [ne_eq, h0, not_false_eq_true, decide_true, ite_true]
    have h4 : (4 : ℕ) ^ 5 = 1024 := by norm_num
    rw [h4] at this
    omega

lemma getD_zero4 (k : ℕ) : ([0, 0, 0, 0] : List ℕ).getD k 0 = 0 := by
  rcases k with _ | _ | _ | _ | k <;> rfl

/-- The lower-bound half of the certificate of `thm:S4`: for every step, all carry lengths `l_c ≥ 1` and
all stop digits `y`, `∑_c (4^5 f_5(e_c, σ_c))² ≥ 952`. -/
theorem S4_cert_lb (e : Fin 4 → ℤ) (l : Fin 4 → ℕ) (y : Fin 4 → F4)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    952 ≤ ∑ c, gapNum f4code 5 (e c) (certSigma f4code S4Dr 5 e l y c) ^ 2 := by
  choose t ht ty hty hch using fun c' => S4_change (l c') (hl c') (y c')
  set z : Fin 4 → ℕ := fun c' => (S4chg.getD (t c') []).getD (ty c') 0 with hzdef
  have hz : ∀ c' (k : Fin 4), z c' < 120 ∧ encVec f4code (fun i : Fin 5 => chgU (t c') (ty c') i k) =
      ((S4Z 0).getD (z c') []).getD k 0 := fun c' k => s4_chg ⟨t c', ht c'⟩ ⟨ty c', hty c'⟩ k
  set row : Fin 4 → List ℕ := fun c' => if e c' = 0 then [0, 0, 0, 0] else (S4Z c').getD (z c') [] with hrowdef
  have hrow0 : ∀ c', e c' = 0 → row c' = [0, 0, 0, 0] := fun c' h => by simp [hrowdef, h]
  have hrowm : ∀ c' : Fin 4, e c' ≠ 0 → row c' ∈ S4Z c' := by
    intro c' h
    simp only [hrowdef, h, ite_false]
    obtain ⟨hlen, -⟩ := s4_Zperm c'
    exact getD_mem' _ _ _ (by rw [hlen]; exact (hz c' 0).1)
  have hterm : ∀ c c' : Fin 4, encVec f4code (if e c' = 0 then 0 else
      (fun i : Fin 5 => chgU (t c') (ty c') i (fxor c c'))) = (row c').getD c 0 := by
    intro c c'
    rw [enc_ite5]
    by_cases h0 : e c' = 0
    · simp only [h0, ite_true, hrowdef, getD_zero4]
    · simp only [h0, ite_false, hrowdef]
      rw [(hz c' (fxor c c')).2, ((s4_Zperm c').2 ⟨z c', (hz c' 0).1⟩ c).1]
      rfl
  have hw : ∀ c : Fin 4, encVec f4code (certSigma f4code S4Dr 5 e l y c) =
      (row 0).getD c 0 ^^^ (row 1).getD c 0 ^^^ (row 2).getD c 0 ^^^ (row 3).getD c 0 := by
    intro c
    have hs : certSigma f4code S4Dr 5 e l y c =
        (if e 0 = 0 then 0 else (fun i : Fin 5 => chgU (t 0) (ty 0) i (fxor c 0))) +
        (if e 1 = 0 then 0 else (fun i : Fin 5 => chgU (t 1) (ty 1) i (fxor c 1))) +
        (if e 2 = 0 then 0 else (fun i : Fin 5 => chgU (t 2) (ty 2) i (fxor c 2))) +
        (if e 3 = 0 then 0 else (fun i : Fin 5 => chgU (t 3) (ty 3) i (fxor c 3))) := by
      funext i
      simp only [certSigma, Fin.sum_univ_four, Pi.add_apply]
      rw [hch 0 i i.isLt c 0, hch 1 i i.isLt c 1, hch 2 i i.isLt c 2, hch 3 i i.isLt c 3,
        intCast_f4 _ (he 0), intCast_f4 _ (he 1), intCast_f4 _ (he 2), intCast_f4 _ (he 3)]
      split_ifs <;> simp
    rw [hs, encVec_xor4, encVec_xor4, encVec_xor4, hterm, hterm, hterm, hterm]
  have hb : ∀ c, s4b (decide (e c ≠ 0)) (encVec f4code (certSigma f4code S4Dr 5 e l y c)) ≤
      gapNum f4code 5 (e c) (certSigma f4code S4Dr 5 e l y c) := fun c => s4b_le _ (he c) _
  have key : 952 ≤ ∑ c : Fin 4, s4b (decide (e c ≠ 0))
      ((row 0).getD c 0 ^^^ (row 1).getD c 0 ^^^ (row 2).getD c 0 ^^^ (row 3).getD c 0) ^ 2 := by
    rw [Fin.sum_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, fin4_val3]
    by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;> by_cases h2 : e 2 = 0 <;> by_cases h3 : e 3 = 0
    · obtain ⟨c, hc⟩ := hne; fin_cases c <;> simp_all
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec false false false true s4_part0001 (row 0) (row 1) (row 2) (row 3) (by rw [hrow0 0 h0]; simp [s4opt]) (by rw [hrow0 1 h1]; simp [s4opt]) (by rw [hrow0 2 h2]; simp [s4opt]) (by simpa [s4opt] using hrowm 3 h3)
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec false false true false s4_part0010 (row 0) (row 1) (row 2) (row 3) (by rw [hrow0 0 h0]; simp [s4opt]) (by rw [hrow0 1 h1]; simp [s4opt]) (by simpa [s4opt] using hrowm 2 h2) (by rw [hrow0 3 h3]; simp [s4opt])
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec false false true true s4_part0011 (row 0) (row 1) (row 2) (row 3) (by rw [hrow0 0 h0]; simp [s4opt]) (by rw [hrow0 1 h1]; simp [s4opt]) (by simpa [s4opt] using hrowm 2 h2) (by simpa [s4opt] using hrowm 3 h3)
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec false true false false s4_part0100 (row 0) (row 1) (row 2) (row 3) (by rw [hrow0 0 h0]; simp [s4opt]) (by simpa [s4opt] using hrowm 1 h1) (by rw [hrow0 2 h2]; simp [s4opt]) (by rw [hrow0 3 h3]; simp [s4opt])
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec false true false true s4_part0101 (row 0) (row 1) (row 2) (row 3) (by rw [hrow0 0 h0]; simp [s4opt]) (by simpa [s4opt] using hrowm 1 h1) (by rw [hrow0 2 h2]; simp [s4opt]) (by simpa [s4opt] using hrowm 3 h3)
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec false true true false s4_part0110 (row 0) (row 1) (row 2) (row 3) (by rw [hrow0 0 h0]; simp [s4opt]) (by simpa [s4opt] using hrowm 1 h1) (by simpa [s4opt] using hrowm 2 h2) (by rw [hrow0 3 h3]; simp [s4opt])
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      have hs := s4three_spec3 (row 1) (row 2) (row 3) (hrowm 1 h1) (hrowm 2 h2) (hrowm 3 h3)
      rw [hrow0 0 h0]
      simp only [getD_zero4, Nat.xor_zero, Nat.zero_xor] 
      norm_num at hs ⊢
      exact hs
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec true false false false s4_part1000 (row 0) (row 1) (row 2) (row 3) (by simpa [s4opt] using hrowm 0 h0) (by rw [hrow0 1 h1]; simp [s4opt]) (by rw [hrow0 2 h2]; simp [s4opt]) (by rw [hrow0 3 h3]; simp [s4opt])
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec true false false true s4_part1001 (row 0) (row 1) (row 2) (row 3) (by simpa [s4opt] using hrowm 0 h0) (by rw [hrow0 1 h1]; simp [s4opt]) (by rw [hrow0 2 h2]; simp [s4opt]) (by simpa [s4opt] using hrowm 3 h3)
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec true false true false s4_part1010 (row 0) (row 1) (row 2) (row 3) (by simpa [s4opt] using hrowm 0 h0) (by rw [hrow0 1 h1]; simp [s4opt]) (by simpa [s4opt] using hrowm 2 h2) (by rw [hrow0 3 h3]; simp [s4opt])
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      have hs := s4three_spec2 (row 0) (row 2) (row 3) (hrowm 0 h0) (hrowm 2 h2) (hrowm 3 h3)
      rw [hrow0 1 h1]
      simp only [getD_zero4, Nat.xor_zero, Nat.zero_xor] 
      norm_num at hs ⊢
      exact hs
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      exact s4part_spec true true false false s4_part1100 (row 0) (row 1) (row 2) (row 3) (by simpa [s4opt] using hrowm 0 h0) (by simpa [s4opt] using hrowm 1 h1) (by rw [hrow0 2 h2]; simp [s4opt]) (by rw [hrow0 3 h3]; simp [s4opt])
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      have hs := s4three_spec1 (row 0) (row 1) (row 3) (hrowm 0 h0) (hrowm 1 h1) (hrowm 3 h3)
      rw [hrow0 2 h2]
      simp only [getD_zero4, Nat.xor_zero, Nat.zero_xor] 
      norm_num at hs ⊢
      exact hs
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      have hs := s4three_spec0 (row 0) (row 1) (row 2) (hrowm 0 h0) (hrowm 1 h1) (hrowm 2 h2)
      rw [hrow0 3 h3]
      simp only [getD_zero4, Nat.xor_zero, Nat.zero_xor] 
      norm_num at hs ⊢
      exact hs
    · simp only [h0, h1, h2, h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_true, decide_false]
      have hs := s4full_spec (row 0) (row 1) (row 2) (row 3) (hrowm 0 h0) (hrowm 1 h1) (hrowm 2 h2) (hrowm 3 h3)
      simp only [Nat.xor_assoc] at hs ⊢
      exact hs
  rw [Fin.sum_univ_four] at key ⊢
  rw [← hw 0, ← hw 1, ← hw 2, ← hw 3] at key
  exact key.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.pow_le_pow_left (hb 0) 2)
    (Nat.pow_le_pow_left (hb 1) 2)) (Nat.pow_le_pow_left (hb 2) 2)) (Nat.pow_le_pow_left (hb 3) 2))

/-! ## `thm:S4` -/

lemma S4_LB_le_one : Real.sqrt 952 / 1024 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  rw [show (1024 : ℝ) = Real.sqrt (1024 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma S4_LB_pos : 0 < Real.sqrt 952 / 1024 := by positivity

/-- **`thm:S4`** (separation): `c(P_{4K}) ≥ √952/4^5 = 0.0301313…` for every `K ≥ 1`. -/
theorem S4_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 4 4 K (seqPoint f4code S4gen) (Real.sqrt 952 / 1024) := by
  have hK4 : 4 ≤ 4 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK)
  have hc := cert f4code S4gen K 5 hK4 (S4_net (4 * K) 0) S4Dr (fun i c c' => by simp [S4Dr])
    (fun i _ l h1 h2 c c' => by
      rw [show S4Dr i l c c' = lawD (fun _ => S4g) S4z S4G i l c c' by simp [S4Dr]; omega]
      exact S4_law K i l h1 h2 c c')
    (Real.sqrt 952 / 1024) ?_
  · rwa [min_eq_right S4_LB_le_one] at hc
  rintro e l ⟨he, hne, hl⟩ y
  have hb := S4_cert_lb e l y he hne (fun c => (hl c).1)
  rewrite [Fin.sum_univ_four] at hb
  unfold certTerm
  rewrite [Fin.sum_univ_four]
  generalize gapNum f4code 5 (e 0) (certSigma f4code S4Dr 5 e l y 0) = A at hb ⊢
  generalize gapNum f4code 5 (e 1) (certSigma f4code S4Dr 5 e l y 1) = B at hb ⊢
  generalize gapNum f4code 5 (e 2) (certSigma f4code S4Dr 5 e l y 2) = D at hb ⊢
  generalize gapNum f4code 5 (e 3) (certSigma f4code S4Dr 5 e l y 3) = E at hb ⊢
  apply Real.le_sqrt_of_sq_le
  have hb' : (952 : ℝ) ≤ (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + (D : ℝ) ^ 2 + (E : ℝ) ^ 2 := by exact_mod_cast hb
  rw [div_pow, Real.sq_sqrt (by norm_num), div_pow, div_pow, div_pow, div_pow, ← add_div, ← add_div,
    ← add_div]
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

/-- **`thm:S4`** (all `N`): `δ(P_{[N]}) ≥ 0.0075 · N^{-1/4}` for every `N ≥ 2`. -/
theorem S4_allN : SepAllN 4 (seqPoint f4code S4gen) (75 / 10000) := by
  have h := prefix_sep 4 4 (by norm_num) (by norm_num) (seqPoint f4code S4gen) _ S4_LB_pos.le
    (fun K hK => S4_sep K hK)
  refine sepAllN_mono _ ?_ h
  have hs : (3085 / 100 : ℝ) ≤ Real.sqrt 952 := Real.le_sqrt_of_sq_le (by norm_num)
  push_cast
  rw [div_div, le_div_iff₀ (by norm_num)]
  nlinarith

/-- **`thm:S4`** (mesh ratio): `h(P_{[N]}) ≤ 266 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem S4_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint f4code S4gen)) ≤
      266 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint f4code S4gen))) := by
  have h := prefix_mesh f4code S4gen (by norm_num) (by norm_num) S4_net _ S4_LB_pos
    (fun K hK => S4_sep K hK) N hN
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hs : (3085 / 100 : ℝ) ≤ Real.sqrt 952 := Real.le_sqrt_of_sq_le (by norm_num)
    push_cast
    rw [h4, div_le_iff₀ S4_LB_pos]
    nlinarith
  · have : 0 ≤ Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint f4code S4gen)) :=
      Real.iInf_nonneg fun _ => div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    linarith

/-- **`lem:frames`(a) for `H = 𝔽_4`** (`S4_frames` with `IsP4` unfolded): `U = ∑_{k≥0} x^{4^k}` satisfies
`U⁴ + U = x`, `U(0) = 0`, the Mahler equation `U(x) = U(x⁴) + x`, and `[x^n] U = 1` exactly at the powers
of `4` (`0` otherwise). -/
theorem S4_frames_char : U4 ^ 4 + U4 = X ∧ constantCoeff U4 = 0 ∧ U4 = expand 4 four_ne_zero U4 + X ∧
    (∀ k, coeff (4 ^ k) U4 = 1) ∧ ∀ n, (¬ ∃ k, 4 ^ k = n) → coeff n U4 = 0 :=
  S4_frames

end GeoSeq
