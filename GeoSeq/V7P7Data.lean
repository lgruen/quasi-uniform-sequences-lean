/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7Graph
public import GeoSeq.Window
public import GeoSeq.OneDigit

@[expose] public section

/-!
# GeoSeq stage V7: the finite check of `thm:p7` — checker and soundness

The bound `LB(w) ≥ 1/7` of `thm:p7` is the statement that no combination makes every term vanish
(`rem:onedigit`: `f_1(±1, σ) = 0` only for `σ = ±1`, `f_1(0, σ) = 0` only for `σ ∈ {-1, 0, 1}`). The checker
`p7chk e₀ e₁ e₂` (natural numbers; a step entry `-1, 0, 1` is coded `6, 0, 1`) runs over one graph column
`(w(ξ), ξ_1, ξ_2)` per moving coordinate (`p7G`, the 49 columns of `tab:p7`) and tests that some coordinate does
not vanish. Soundness: `p7chk_sound`. The 13 steps up to sign are checked by `decide +kernel` in
`GeoSeq/V7P7a.lean`, `V7P7b.lean`, `V7P7c.lean` (one module per step class group, built one at a time).
-/

namespace GeoSeq

lemma graphCol_self {F : Type*} [Field F] (wt : F → F → F) (ξ : F × F) (c' : Fin 3) :
    graphCol wt ξ c' c' = wt ξ.1 ξ.2 := if_pos rfl

lemma graphCol_one {F : Type*} [Field F] (wt : F → F → F) (ξ : F × F) (c' : Fin 3) :
    graphCol wt ξ c' (c' + 1) = ξ.1 := by
  unfold graphCol; rw [if_neg (fin3_ne1 c'), if_pos rfl]

lemma graphCol_two {F : Type*} [Field F] (wt : F → F → F) (ξ : F × F) (c' : Fin 3) :
    graphCol wt ξ c' (c' + 2) = ξ.2 := by
  unfold graphCol; rw [if_neg (fin3_ne2 c'), if_neg (fin3_ne21 c')]

lemma mem_p7G : ∀ a b : ZMod 7, ((wP7 a b).val, a.val, b.val) ∈ p7G := by decide

lemma p7_term (x : ℤ) (hx : x = -1 ∨ x = 0 ∨ x = 1) (y : ZMod 7) (n : ℕ) (hn : x ≠ 0 → n = y.val) :
    (x : ZMod 7) * y = ((p7code x * n : ℕ) : ZMod 7) := by
  rcases hx with rfl | rfl | rfl
  · rw [hn (by decide)]
    have h6 : ((-1 : ℤ) : ZMod 7) = ((6 : ℕ) : ZMod 7) := by decide
    simp only [p7code, h6, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    norm_num
  · simp [p7code]
  · rw [hn (by decide)]
    simp [p7code]

lemma p7_van (x : ℤ) (hx : x = -1 ∨ x = 0 ∨ x = 1) (σ : ZMod 7) (h : gapNum1 7 x σ = 0) :
    p7van (p7code x) σ.val = true := by
  rcases hx with rfl | rfl | rfl
  · rw [F1_neg, f1_one_val] at h
    revert σ; decide
  · rw [f1_zero_val] at h
    revert σ; decide
  · rw [f1_one_val] at h
    revert σ; decide

/-- **Soundness of the checker**: if `p7chk` accepts the codes of a step `e ∈ {-1,0,1}^3`, then for every choice of
`ξ^{(c')} ∈ 𝔽_7^2` some coordinate has `f_1(e_c, σ_c) ≠ 0`. -/
theorem p7chk_sound (e : Fin 3 → ℤ) (he : ∀ c, e c = -1 ∨ e c = 0 ∨ e c = 1)
    (hchk : p7chk (p7code (e 0)) (p7code (e 1)) (p7code (e 2)) = true)
    (ξ : Fin 3 → ZMod 7 × ZMod 7) : ∃ c, gapNum1 7 (e c) (graphSig wP7 e ξ c) ≠ 0 := by
  set T : Fin 3 → ℕ × ℕ × ℕ := fun c' => if e c' = 0 then (0, 0, 0) else
    ((wP7 (ξ c').1 (ξ c').2).val, (ξ c').1.val, (ξ c').2.val) with hTdef
  have hT : ∀ c', T c' ∈ p7colL (p7code (e c')) := by
    intro c'
    by_cases h0 : e c' = 0
    · simp [hTdef, h0, p7colL, p7code]
    · have hc : p7code (e c') ≠ 0 := by unfold p7code; split_ifs <;> omega
      simp only [hTdef, h0, if_false, p7colL, hc]
      exact mem_p7G _ _
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hchk (T 0) (hT 0)) (T 1) (hT 1)) (T 2) (hT 2)
  -- the three rows
  have hT1 : ∀ c', e c' ≠ 0 → (T c').1 = (wP7 (ξ c').1 (ξ c').2).val := fun c' hne => by
    simp only [hTdef, hne, if_false]
  have hT2 : ∀ c', e c' ≠ 0 → (T c').2.1 = (ξ c').1.val := fun c' hne => by
    simp only [hTdef, hne, if_false]
  have hT3 : ∀ c', e c' ≠ 0 → (T c').2.2 = (ξ c').2.val := fun c' hne => by
    simp only [hTdef, hne, if_false]
  have g00 : graphCol wP7 (ξ 0) 0 0 = wP7 (ξ 0).1 (ξ 0).2 := graphCol_self wP7 (ξ 0) 0
  have g11 : graphCol wP7 (ξ 1) 1 1 = wP7 (ξ 1).1 (ξ 1).2 := graphCol_self wP7 (ξ 1) 1
  have g22 : graphCol wP7 (ξ 2) 2 2 = wP7 (ξ 2).1 (ξ 2).2 := graphCol_self wP7 (ξ 2) 2
  have g01 : graphCol wP7 (ξ 0) 0 1 = (ξ 0).1 := graphCol_one wP7 (ξ 0) 0
  have g12 : graphCol wP7 (ξ 1) 1 2 = (ξ 1).1 := graphCol_one wP7 (ξ 1) 1
  have g20 : graphCol wP7 (ξ 2) 2 0 = (ξ 2).1 := graphCol_one wP7 (ξ 2) 2
  have g02 : graphCol wP7 (ξ 0) 0 2 = (ξ 0).2 := graphCol_two wP7 (ξ 0) 0
  have g10 : graphCol wP7 (ξ 1) 1 0 = (ξ 1).2 := graphCol_two wP7 (ξ 1) 1
  have g21 : graphCol wP7 (ξ 2) 2 1 = (ξ 2).2 := graphCol_two wP7 (ξ 2) 2
  have hs0 : graphSig wP7 e ξ 0 =
      ((p7code (e 0) * (T 0).1 + p7code (e 1) * (T 1).2.2 + p7code (e 2) * (T 2).2.1 : ℕ) : ZMod 7) := by
    unfold graphSig
    rw [Fin.sum_univ_three, Nat.cast_add, Nat.cast_add, g00, g10, g20]
    congr 1; congr 1
    · exact p7_term _ (he 0) _ _ (hT1 0)
    · exact p7_term _ (he 1) _ _ (hT3 1)
    · exact p7_term _ (he 2) _ _ (hT2 2)
  have hs1 : graphSig wP7 e ξ 1 =
      ((p7code (e 0) * (T 0).2.1 + p7code (e 1) * (T 1).1 + p7code (e 2) * (T 2).2.2 : ℕ) : ZMod 7) := by
    unfold graphSig
    rw [Fin.sum_univ_three, Nat.cast_add, Nat.cast_add, g01, g11, g21]
    congr 1; congr 1
    · exact p7_term _ (he 0) _ _ (hT2 0)
    · exact p7_term _ (he 1) _ _ (hT1 1)
    · exact p7_term _ (he 2) _ _ (hT3 2)
  have hs2 : graphSig wP7 e ξ 2 =
      ((p7code (e 0) * (T 0).2.2 + p7code (e 1) * (T 1).2.1 + p7code (e 2) * (T 2).1 : ℕ) : ZMod 7) := by
    unfold graphSig
    rw [Fin.sum_univ_three, Nat.cast_add, Nat.cast_add, g02, g12, g22]
    congr 1; congr 1
    · exact p7_term _ (he 0) _ _ (hT3 0)
    · exact p7_term _ (he 1) _ _ (hT2 1)
    · exact p7_term _ (he 2) _ _ (hT1 2)
  by_contra hall
  push_neg at hall
  have v0 := p7_van _ (he 0) _ (hall 0)
  have v1 := p7_van _ (he 1) _ (hall 1)
  have v2 := p7_van _ (he 2) _ (hall 2)
  rw [hs0, ZMod.val_natCast] at v0
  rw [hs1, ZMod.val_natCast] at v1
  rw [hs2, ZMod.val_natCast] at v2
  rw [v0, v1, v2] at h
  exact absurd h (by decide)

end GeoSeq
