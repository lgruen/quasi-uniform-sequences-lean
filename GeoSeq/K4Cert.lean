/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.K4Law
public import GeoSeq.K4Data
public import GeoSeq.K4Gap
public import GeoSeq.B3Cert

@[expose] public section

/-!
# GeoSeq stage S8: the exact response sets and the certificate of `thm:K4`

* The automaton certificate (`prop:automaton` for `thm:K4`, source coordinate `0`; the other sources
  by `K4_rot`): initial vector, closure under the four Cartier steps, readouts, witnesses (kernel
  `decide`). `K4_resp`: for every carry length `l ≥ 1` the pair column `(D_i(l)[c][0], D_i(l-1)[c][0])`
  is one of the `37` listed tuples; `K4_resp_card`: exactly these occur.
* The change columns of `eq:carrychange` (`Δ(ȳ) = ω²`, `Δ(y) ∈ {1, ω²}`): `ω² D(l)` and
  `D(l) + ω D(l-1)`, `67` binary words per target coordinate (`K4_change`).
* The certificate minimum `54774953 = min ∑_c (4^8 f_8(e_c, σ_c))²` (`K4_cert_min`), by a kernel check
  over all moving sets and all choices of change columns with the binary closed forms of `f_8`
  (`GeoSeq/K4Gap.lean`), and `thm:K4`: `K4_sep` (every `K ≥ 1`: `4^K ≥ 4`), `K4_allN`, `K4_mesh`.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## The automaton certificate (source coordinate `0`) -/

set_option maxRecDepth 100000 in
theorem k4_init : K4Bv.getD 0 [] = initV4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem k4_closeA : ∀ s : Fin 51, ∀ r : Fin 4, (K4tA.getD s []).getD r 0 < 51 ∧
    stepV4 r (K4Av.getD s []) = K4Av.getD ((K4tA.getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem k4_closeB : ∀ s : Fin 3, ((K4tB.getD s []).getD 0 0 < 3 ∧
    stepV4 0 (K4Bv.getD s []) = K4Bv.getD ((K4tB.getD s []).getD 0 0) []) ∧
    ∀ r : Fin 4, r ≠ 0 → (K4tB.getD s []).getD r 0 < 51 ∧
      stepV4 r (K4Bv.getD s []) = K4Av.getD ((K4tB.getD s []).getD r 0) [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem k4_read : ∀ s : Fin 51, K4out.getD s 0 < 37 ∧
    (K4Av.getD s []).map acoef4 = (K4tup.getD (K4out.getD s 0) []).map n2f := by decide +kernel

set_option maxRecDepth 100000 in
theorem k4_wit : ∀ t : Fin 37, (∀ d ∈ K4wit.getD t [], d < 4) ∧ 1 ≤ Nat.ofDigits 4 (K4wit.getD t []) ∧
    (readV4 (K4wit.getD t []) initV4).map acoef4 = (K4tup.getD t []).map n2f := by decide +kernel

set_option maxRecDepth 100000 in
/-- `D_i(0) = 0` from the formula: coefficient `0` of every initial state vanishes. -/
theorem k4_zero : ∀ i : Fin 8, ∀ c : Fin 3, acoef4 (initS4 i c 0) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem k4_distinct : ∀ t t' : Fin 37, t ≠ t' → ∃ k : Fin 48, K4tupv t k ≠ K4tupv t' k := by
  decide +kernel

/-! ## The response pairs -/

lemma getD_map_n2f (L : List ℕ) (k : ℕ) : (L.map n2f).getD k 0 = n2f (L.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases L[k]? <;> rfl

lemma K4_lawD_zero (i : ℕ) (hi : i < 8) (c : Fin 3) : lawD (fun _ => K4g) K4z K4G i 0 c 0 = 0 := by
  rw [← K4_init i hi c 0, zero_add, ← acoef4_eq]
  exact k4_zero ⟨i, hi⟩ c

lemma K4Dr_prev (i : ℕ) (hi : i < 8) (c : Fin 3) (l : ℕ) (hl : 1 ≤ l) :
    coeff (l + 8) (esem4 (initS4 i c 1)) = K4Dr i (l - 1) c 0 := by
  rw [K4_init1 i hi c l hl, K4Dr]
  by_cases h : l - 1 = 0
  · rw [if_pos h, h, K4_lawD_zero i hi c]
  · rw [if_neg h]

lemma vals4_initV4 (l i : ℕ) (hl : 1 ≤ l) (hi : i < 8) (c : Fin 3) :
    (vals4 initV4 l).getD (3 * i + c) 0 = lawD (fun _ => K4g) K4z K4G i l c 0 ∧
    (vals4 initV4 l).getD (24 + 3 * i + c) 0 = K4Dr i (l - 1) c 0 := by
  have hk : 3 * i + (c : ℕ) < 48 := by omega
  have hk' : 24 + 3 * i + (c : ℕ) < 48 := by omega
  simp only [vals4, initV4, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
  simp only [Option.map_some, Option.getD_some, Function.comp_apply]
  have e1 : (3 * i + (c : ℕ)) % 24 / 3 = i := by omega
  have e2 : (24 + 3 * i + (c : ℕ)) % 24 / 3 = i := by omega
  have e3 : (⟨(3 * i + (c : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = c := by
    ext; simp only [Fin.val_mk]; omega
  have e4 : (⟨(24 + 3 * i + (c : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = c := by
    ext; simp only [Fin.val_mk]; omega
  have e5 : (3 * i + (c : ℕ)) / 24 = 0 := by omega
  have e6 : (24 + 3 * i + (c : ℕ)) / 24 = 1 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  exact ⟨K4_init i hi c l, K4Dr_prev i hi c l hl⟩

/-- **`prop:automaton` for `thm:K4`** (`j = 8`, source `0`): for every carry length `l ≥ 1` the pair
column `(D_i(l)[c][0], D_i(l-1)[c][0])_{i<8, c<3}` is one of the `37` listed tuples. -/
theorem K4_resp (l : ℕ) (hl : 1 ≤ l) :
    ∃ t < 37, ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => K4g) K4z K4G i l c 0 = K4tupv t (3 * i + c) ∧
      K4Dr i (l - 1) c 0 = K4tupv t (24 + 3 * i + c) := by
  obtain ⟨s', hs', h⟩ := reach_B4 K4Av K4Bv K4tA K4tB 51 3 (by decide +kernel) (by decide +kernel)
    k4_closeA k4_closeB l 0 hl (by norm_num)
  rw [k4_init] at h
  obtain ⟨h1, h2⟩ := k4_read ⟨s', hs'⟩
  refine ⟨_, h1, fun i hi c => ?_⟩
  obtain ⟨a, b⟩ := vals4_initV4 l i hl hi c
  rw [h, vals4_zero, h2, getD_map_n2f] at a b
  exact ⟨a.symm, b.symm⟩

/-- **`prop:automaton` for `thm:K4`, exactness**: every listed pair tuple occurs for some `l ≥ 1`. -/
theorem K4_resp_occurs (t : ℕ) (ht : t < 37) :
    ∃ l, 1 ≤ l ∧ ∀ i < 8, ∀ c : Fin 3, lawD (fun _ => K4g) K4z K4G i l c 0 = K4tupv t (3 * i + c) ∧
      K4Dr i (l - 1) c 0 = K4tupv t (24 + 3 * i + c) := by
  obtain ⟨hds, h1, h2⟩ := k4_wit ⟨t, ht⟩
  refine ⟨Nat.ofDigits 4 (K4wit.getD t []), h1, fun i hi c => ?_⟩
  obtain ⟨a, b⟩ := vals4_initV4 _ i h1 hi c
  rw [vals4_read _ hds, vals4_zero, h2, getD_map_n2f] at a b
  exact ⟨a.symm, b.symm⟩

/-- **`prop:automaton` for `thm:K4`, the count** (`j = 8`): the pair columns
`(D_i(l)[c][0], D_i(l-1)[c][0])_{i<8, c<3}` over all `l ≥ 1` form a set of exactly `37` elements. -/
theorem K4_resp_card :
    Set.ncard {D : Fin 8 → Fin 3 → F4 × F4 | ∃ l, 1 ≤ l ∧ ∀ i : Fin 8, ∀ c : Fin 3,
      D i c = (lawD (fun _ => K4g) K4z K4G i l c 0, K4Dr i (l - 1) c 0)} = 37 := by
  let f : Fin 37 → (Fin 8 → Fin 3 → F4 × F4) := fun t i c =>
    (K4tupv t (3 * i + c), K4tupv t (24 + 3 * i + c))
  have hset : {D : Fin 8 → Fin 3 → F4 × F4 | ∃ l, 1 ≤ l ∧ ∀ i : Fin 8, ∀ c : Fin 3,
      D i c = (lawD (fun _ => K4g) K4z K4G i l c 0, K4Dr i (l - 1) c 0)} = Set.range f := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨l, hl, hD⟩
      obtain ⟨t, ht, h⟩ := K4_resp l hl
      refine ⟨⟨t, ht⟩, funext fun i => funext fun c => ?_⟩
      rw [hD i c, (h i i.isLt c).1, (h i i.isLt c).2]
    · rintro ⟨⟨t, ht⟩, rfl⟩
      obtain ⟨l, hl, h⟩ := K4_resp_occurs t ht
      exact ⟨l, hl, fun i c => by rw [(h i i.isLt c).1, (h i i.isLt c).2]⟩
  have hinj : Function.Injective f := by
    intro t t' htt
    by_contra hne
    obtain ⟨k, hk⟩ := k4_distinct t t' hne
    apply hk
    by_cases hk1 : (k : ℕ) < 24
    · have e := congrArg Prod.fst (congrFun (congrFun htt ⟨(k : ℕ) / 3, by omega⟩) ⟨(k : ℕ) % 3, by omega⟩)
      simp only [f, Fin.val_mk] at e
      rw [show (k : ℕ) = 3 * ((k : ℕ) / 3) + (k : ℕ) % 3 by omega]; exact e
    · have e := congrArg Prod.snd
        (congrFun (congrFun htt ⟨((k : ℕ) - 24) / 3, by omega⟩) ⟨((k : ℕ) - 24) % 3, by omega⟩)
      simp only [f, Fin.val_mk] at e
      rw [show (k : ℕ) = 24 + 3 * (((k : ℕ) - 24) / 3) + ((k : ℕ) - 24) % 3 by omega]; exact e
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## The change columns (`eq:carrychange`) -/

lemma K4Dr_rot (i l : ℕ) (c c' : Fin 3) : K4Dr i l c c' = K4Dr i l (c - c') 0 := by
  unfold K4Dr
  split_ifs
  · rfl
  · exact K4_rot i l c c'

lemma K4Dr_pos (i l : ℕ) (hl : l ≠ 0) (c c' : Fin 3) :
    K4Dr i l c c' = lawD (fun _ => K4g) K4z K4G i l c c' := by
  rw [K4Dr, if_neg hl]

lemma getD_mem' {α : Type*} (L : List α) (k : ℕ) (d : α) (h : k < L.length) : L.getD k d ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

lemma digInc_top4 : digInc f4code (topDigit f4code) = F4.w2 := rfl

lemma digInc_cases4 (y : F4) : digInc f4code y = 1 ∨ digInc f4code y = F4.w2 := by
  cases y <;> decide

lemma f4_chg1 : ∀ A B : F4, F4.w2 * B + 1 * (A - B) = A + F4.w * B := by decide
lemma f4_chg2 : ∀ A B : F4, F4.w2 * B + F4.w2 * (A - B) = F4.w2 * A := by decide

/-- **The change columns of `thm:K4`** (`eq:carrychange`, `Δ(ȳ) = ω²`, `Δ(y) ∈ {1, ω²}`): for every
carry length `l ≥ 1` and stop digit `y`, the change of the geometric digit `K + i` of coordinate `c`
caused by a step of coordinate `c'` is the entry `(i, c - c')` of one of the listed change columns
(`ω² D(l)` or `D(l) + ω D(l-1)` of a listed pair tuple, rotated). -/
theorem K4_change (l : ℕ) (hl : 1 ≤ l) (y : F4) : ∃ t < 37, ∃ ty < 2, ∀ i < 8, ∀ c c' : Fin 3,
    carryChange f4code K4Dr i l y c c' = chgF t ty i (c - c') := by
  obtain ⟨t, ht, h⟩ := K4_resp l hl
  have hl0 : l ≠ 0 := by omega
  rcases digInc_cases4 y with hy | hy
  · refine ⟨t, ht, 1, by norm_num, fun i hi c c' => ?_⟩
    obtain ⟨h1, h2⟩ := h i hi (c - c')
    unfold carryChange chgF
    rw [digInc_top4, hy, K4Dr_rot i (l - 1), K4Dr_rot i l, K4Dr_pos i l hl0, h1, h2, if_neg one_ne_zero]
    exact f4_chg1 _ _
  · refine ⟨t, ht, 0, by norm_num, fun i hi c c' => ?_⟩
    obtain ⟨h1, h2⟩ := h i hi (c - c')
    unfold carryChange chgF
    rw [digInc_top4, hy, K4Dr_rot i (l - 1), K4Dr_rot i l, K4Dr_pos i l hl0, h1, h2, if_pos rfl]
    exact f4_chg2 _ _

set_option maxRecDepth 100000 in
/-- The words of the change columns (`K4Z`, one word per target offset). -/
theorem k4_chg : ∀ t : Fin 37, ∀ ty : Fin 2, ∀ c : Fin 3, (K4chg.getD t []).getD ty 0 < 67 ∧
    encVec f4code (fun i : Fin 8 => chgF t ty i c) = (K4Z.getD ((K4chg.getD t []).getD ty 0) []).getD c 0 := by
  decide +kernel

/-! ## The certificate check -/

set_option maxRecDepth 100000 in
/-- The certificate check for the moving sets with one or two coordinates. -/
theorem k4_check_part : ∀ m0 m1 m2 : Bool, (m0 && m1 && m2) = false → (m0 || m1 || m2) = true →
    k4chk m0 m1 m2 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The certificate check for the steps that move all three coordinates (`67³` choices). -/
theorem k4_check_full : k4chk true true true = true := by decide +kernel

lemma k4_check (m0 m1 m2 : Bool) (h : (m0 || m1 || m2) = true) : k4chk m0 m1 m2 = true := by
  by_cases h3 : (m0 && m1 && m2) = true
  · simp only [Bool.and_eq_true] at h3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
    exact k4_check_full
  · exact k4_check_part m0 m1 m2 (by simpa using h3) h

lemma k4chk_spec (m0 m1 m2 : Bool) (h : k4chk m0 m1 m2 = true) (a b d : List ℕ)
    (ha : a ∈ k4opt m0) (hb : b ∈ k4opt m1) (hd : d ∈ k4opt m2) :
    54774953 ≤ k4b m0 (a.getD 0 0 ^^^ b.getD 2 0 ^^^ d.getD 1 0) ^ 2 +
      k4b m1 (a.getD 1 0 ^^^ b.getD 0 0 ^^^ d.getD 2 0) ^ 2 +
      k4b m2 (a.getD 2 0 ^^^ b.getD 1 0 ^^^ d.getD 0 0) ^ 2 := by
  unfold k4chk at h
  rw [List.all_eq_true] at h
  have h1 := h a ha
  rw [List.all_eq_true] at h1
  have h2 := h1 b hb
  rw [List.all_eq_true] at h2
  have h3 := h2 d hd
  unfold k4ok at h3
  exact of_decide_eq_true h3

lemma intCast_f4 (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) : ((e : ℤ) : F4) = if e = 0 then 0 else 1 := by
  rcases (show e = -1 ∨ e = 0 ∨ e = 1 by omega) with rfl | rfl | rfl <;> rfl

lemma enc_ite4 (p : Prop) [Decidable p] (f : Fin 8 → F4) :
    encVec f4code (if p then 0 else f) = if p then 0 else encVec f4code f := by
  split_ifs
  · exact encVec_zero4
  · rfl

lemma k4b_le (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (σ : Fin 8 → F4) :
    k4b (decide (e ≠ 0)) (encVec f4code σ) ≤ gapNum f4code 8 e σ := by
  unfold k4b
  by_cases h0 : e = 0
  · subst h0
    simpa using gapNum4_zero 8 σ
  · have hpm : e = 1 ∨ e = -1 := by omega
    have := gapNum4_pm 8 e hpm σ
    simp only [ne_eq, h0, not_false_eq_true, decide_true, ite_true]
    have h4 : (4 : ℕ) ^ 8 = 65536 := by norm_num
    rw [h4] at this
    omega

lemma getD_zero3 (k : ℕ) : ([0, 0, 0] : List ℕ).getD k 0 = 0 := by
  rcases k with _ | _ | _ | k <;> rfl

/-- The lower-bound half of `K4_cert_min`: for every step, all carry lengths `l_c ≥ 1` and all stop
digits `y`, `∑_c (4^8 f_8(e_c, σ_c))² ≥ 54774953`. -/
theorem K4_cert_lb (e : Fin 3 → ℤ) (l : Fin 3 → ℕ) (y : Fin 3 → F4)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hne : ∃ c, e c ≠ 0) (hl : ∀ c, 1 ≤ l c) :
    54774953 ≤ ∑ c, gapNum f4code 8 (e c) (certSigma f4code K4Dr 8 e l y c) ^ 2 := by
  choose t ht ty hty hch using fun c' => K4_change (l c') (hl c') (y c')
  set z : Fin 3 → ℕ := fun c' => (K4chg.getD (t c') []).getD (ty c') 0 with hzdef
  have hz : ∀ c' (k : Fin 3), z c' < 67 ∧ encVec f4code (fun i : Fin 8 => chgF (t c') (ty c') i k) =
      (K4Z.getD (z c') []).getD k 0 := fun c' k => k4_chg ⟨t c', ht c'⟩ ⟨ty c', hty c'⟩ k
  set a : Fin 3 → List ℕ := fun c' => if e c' = 0 then [0, 0, 0] else K4Z.getD (z c') [] with hadef
  have ha : ∀ c', a c' ∈ k4opt (decide (e c' ≠ 0)) := by
    intro c'
    by_cases h0 : e c' = 0
    · simp [hadef, h0, k4opt]
    · simp only [hadef, h0, ite_false, k4opt, ne_eq, not_false_eq_true, decide_true, ite_true]
      exact getD_mem' _ _ _ (by rw [show K4Z.length = 67 from rfl]; exact (hz c' 0).1)
  have hterm : ∀ c c' : Fin 3, encVec f4code (if e c' = 0 then 0 else
      (fun i : Fin 8 => chgF (t c') (ty c') i (c - c'))) = (a c').getD (c - c' : Fin 3) 0 := by
    intro c c'
    rw [enc_ite4]
    by_cases h0 : e c' = 0
    · simp only [hadef, h0, ite_true, getD_zero3]
    · simp only [h0, ite_false, hadef]
      exact (hz c' (c - c')).2
  have hw : ∀ c : Fin 3, encVec f4code (certSigma f4code K4Dr 8 e l y c) =
      (a 0).getD (c - 0 : Fin 3) 0 ^^^ (a 1).getD (c - 1 : Fin 3) 0 ^^^ (a 2).getD (c - 2 : Fin 3) 0 := by
    intro c
    have hs : certSigma f4code K4Dr 8 e l y c =
        (if e 0 = 0 then 0 else (fun i : Fin 8 => chgF (t 0) (ty 0) i (c - 0))) +
        (if e 1 = 0 then 0 else (fun i : Fin 8 => chgF (t 1) (ty 1) i (c - 1))) +
        (if e 2 = 0 then 0 else (fun i : Fin 8 => chgF (t 2) (ty 2) i (c - 2))) := by
      funext i
      simp only [certSigma, Fin.sum_univ_three, Pi.add_apply]
      rw [hch 0 i i.isLt c 0, hch 1 i i.isLt c 1, hch 2 i i.isLt c 2,
        intCast_f4 _ (he 0), intCast_f4 _ (he 1), intCast_f4 _ (he 2)]
      split_ifs <;> simp
    rw [hs, encVec_xor4, encVec_xor4, hterm, hterm, hterm]
  have hb : ∀ c, k4b (decide (e c ≠ 0)) (encVec f4code (certSigma f4code K4Dr 8 e l y c)) ≤
      gapNum f4code 8 (e c) (certSigma f4code K4Dr 8 e l y c) := fun c => k4b_le _ (he c) _
  have hmask : (decide (e 0 ≠ 0) || decide (e 1 ≠ 0) || decide (e 2 ≠ 0)) = true := by
    obtain ⟨c, hc⟩ := hne
    fin_cases c <;> simp_all
  have hk := k4chk_spec _ _ _ (k4_check _ _ _ hmask) (a 0) (a 1) (a 2) (ha 0) (ha 1) (ha 2)
  have e0 := hw 0
  have e1 := hw 1
  have e2 := hw 2
  simp only [show ((0 : Fin 3) - 0 : Fin 3) = 0 from rfl, show ((0 : Fin 3) - 1 : Fin 3) = 2 from rfl,
    show ((0 : Fin 3) - 2 : Fin 3) = 1 from rfl, show ((1 : Fin 3) - 0 : Fin 3) = 1 from rfl,
    show ((1 : Fin 3) - 1 : Fin 3) = 0 from rfl, show ((1 : Fin 3) - 2 : Fin 3) = 2 from rfl,
    show ((2 : Fin 3) - 0 : Fin 3) = 2 from rfl, show ((2 : Fin 3) - 1 : Fin 3) = 1 from rfl,
    show ((2 : Fin 3) - 2 : Fin 3) = 0 from rfl, Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  rw [← e0, ← e1, ← e2] at hk
  rw [Fin.sum_univ_three]
  exact hk.trans (Nat.add_le_add (Nat.add_le_add (Nat.pow_le_pow_left (hb 0) 2)
    (Nat.pow_le_pow_left (hb 1) 2)) (Nat.pow_le_pow_left (hb 2) 2))

/-! ## `thm:K4` -/

lemma K4_LB_le_one : Real.sqrt 54774953 / 65536 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  rw [show (65536 : ℝ) = Real.sqrt (65536 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma K4_LB_pos : 0 < Real.sqrt 54774953 / 65536 := by positivity

/-- **`thm:K4`** (separation): `c(P_{3K}) ≥ √54774953/4^8 = 0.1129305…` for every `K ≥ 1`. -/
theorem K4_sep (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel 4 3 K (seqPoint f4code K4gen) (Real.sqrt 54774953 / 65536) := by
  have hK4 : 4 ≤ 4 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK)
  have hc := cert f4code K4gen K 8 hK4 (K4_net (3 * K) 0) K4Dr (fun i c c' => by simp [K4Dr])
    (fun i _ l h1 h2 c c' => by
      rw [show K4Dr i l c c' = lawD (fun _ => K4g) K4z K4G i l c c' by simp [K4Dr]; omega]
      exact K4_law K i l h1 h2 c c')
    (Real.sqrt 54774953 / 65536) ?_
  · rwa [min_eq_right K4_LB_le_one] at hc
  rintro e l ⟨he, hne, hl⟩ y
  have hb := K4_cert_lb e l y he hne (fun c => (hl c).1)
  rewrite [Fin.sum_univ_three] at hb
  unfold certTerm
  rewrite [Fin.sum_univ_three]
  generalize gapNum f4code 8 (e 0) (certSigma f4code K4Dr 8 e l y 0) = A at hb ⊢
  generalize gapNum f4code 8 (e 1) (certSigma f4code K4Dr 8 e l y 1) = B at hb ⊢
  generalize gapNum f4code 8 (e 2) (certSigma f4code K4Dr 8 e l y 2) = D at hb ⊢
  apply Real.le_sqrt_of_sq_le
  have hb' : (54774953 : ℝ) ≤ (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + (D : ℝ) ^ 2 := by exact_mod_cast hb
  rw [div_pow, Real.sq_sqrt (by norm_num), div_pow, div_pow, div_pow, ← add_div, ← add_div]
  push_cast
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  nlinarith

/-- **`thm:K4`** (all `N`): `δ(P_{[N]}) ≥ 0.0282 · N^{-1/3}` for every `N ≥ 2`. -/
theorem K4_allN : SepAllN 3 (seqPoint f4code K4gen) (282 / 10000) := by
  have h := prefix_sep 4 3 (by norm_num) (by norm_num) (seqPoint f4code K4gen) _ K4_LB_pos.le
    (fun K hK => K4_sep K hK)
  refine sepAllN_mono _ ?_ h
  have hs : (7393 : ℝ) ≤ Real.sqrt 54774953 := Real.le_sqrt_of_sq_le (by norm_num)
  push_cast
  rw [div_div, le_div_iff₀ (by norm_num)]
  nlinarith

/-- **`thm:K4`** (mesh ratio): `h(P_{[N]}) ≤ 61.4 · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean,
`δ = 2 · sepRad` toroidal), so the sequence is quasi-uniform. -/
theorem K4_mesh (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint f4code K4gen)) ≤
      614 / 10 * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint f4code K4gen))) := by
  have h := prefix_mesh f4code K4gen (by norm_num) (by norm_num) K4_net _ K4_LB_pos
    (fun K hK => K4_sep K hK) N hN
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have h3 : Real.sqrt 3 ≤ 173206 / 100000 := by
      rw [show (173206 / 100000 : ℝ) = Real.sqrt ((173206 / 100000) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs : (74009 / 10 : ℝ) ≤ Real.sqrt 54774953 := Real.le_sqrt_of_sq_le (by norm_num)
    push_cast
    rw [div_le_iff₀ K4_LB_pos]
    nlinarith
  · have : 0 ≤ Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint f4code K4gen)) :=
      Real.iInf_nonneg fun _ => div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    linarith

end GeoSeq
