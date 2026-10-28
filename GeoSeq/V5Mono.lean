/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs

@[expose] public section

/-!
# GeoSeq stage V5: monotonicity of the threshold predicate (`prop:P0`(b))

* `stNP_anti`: every `N_t^+` is non-increasing in `p` (for `p > 0`, `up > 2`); `stMP_anti`: so is `M^+`.
* **`P0_mono`** (`prop:P0`(b)): `𝒫(p)` implies `𝒫(p')` for every `p' ≥ p > 0`, and `M⋆^+(p') ≤ M⋆^+(p)`; over any
  ordered field (in particular `ℝ`, the paper's real variable).
* **`StP_cast`**: `𝒫` at a rational point is the same over `ℚ` and over `ℝ` (exact evaluation by `decide`).
-/

namespace GeoSeq

open Finset

section Mono

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The first term of `N_1^+` is non-increasing: `max(0, (ap+1)/(k(up-2)))` for `p > 0`, `up > 2`, `k ≥ 0`. -/
lemma mono_term0 (a k u p p' : K) (hk : 0 ≤ k) (hp : 0 < p) (hpp : p ≤ p') (hu : 2 < u * p) :
    max 0 ((a * p' + 1) / (k * (u * p' - 2))) ≤ max 0 ((a * p + 1) / (k * (u * p - 2))) := by
  have hu0 : 0 < u := by
    by_contra h; push_neg at h; nlinarith
  have hup : u * p ≤ u * p' := mul_le_mul_of_nonneg_left hpp hu0.le
  rcases hk.lt_or_eq with hk | hk
  · have hD : 0 < k * (u * p - 2) := mul_pos hk (by linarith)
    have hD' : 0 < k * (u * p' - 2) := mul_pos hk (by linarith)
    refine max_le (le_max_left _ _) ?_
    by_cases hn : a * p' + 1 ≤ 0
    · exact (div_nonpos_of_nonpos_of_nonneg hn hD'.le).trans (le_max_left _ _)
    · push_neg at hn
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_div_iff₀ hD' hD]
      by_cases ha : 0 ≤ 2 * a + u
      · nlinarith [mul_nonneg ha (sub_nonneg.mpr hpp), mul_nonneg hk.le (mul_nonneg ha (sub_nonneg.mpr hpp))]
      · push_neg at ha
        have ha0 : a < 0 := by linarith
        have h1 : a * p' + 1 ≤ a * p + 1 := by nlinarith
        have h2 : k * (u * p - 2) ≤ k * (u * p' - 2) := mul_le_mul_of_nonneg_left (by linarith) hk.le
        nlinarith [mul_le_mul_of_nonneg_left h2 hn.le]
  · subst hk; simp

/-- The further terms `p/(k(up-2))` of `N_t^+` are non-increasing. -/
lemma mono_term (k u p p' : K) (hk : 0 ≤ k) (hp : 0 < p) (hpp : p ≤ p') (hu : 2 < u * p) :
    p' / (k * (u * p' - 2)) ≤ p / (k * (u * p - 2)) := by
  have hu0 : 0 < u := by
    by_contra h; push_neg at h; nlinarith
  have hup : u * p ≤ u * p' := mul_le_mul_of_nonneg_left hpp hu0.le
  rcases hk.lt_or_eq with hk | hk
  · have hD : 0 < k * (u * p - 2) := mul_pos hk (by linarith)
    have hD' : 0 < k * (u * p' - 2) := mul_pos hk (by linarith)
    rw [div_le_div_iff₀ hD' hD]
    nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hpp)]
  · subst hk; simp

/-- An affine inequality `a p ≤ b p - c` (`c ≥ 0`) persists for larger `p > 0`. -/
lemma mono_aff (a b c p p' : K) (hp : 0 < p) (hpp : p ≤ p') (hc : 0 ≤ c) (h : a * p ≤ b * p - c) :
    a * p' ≤ b * p' - c := by
  have hba : 0 ≤ b - a := by
    by_contra hn; push_neg at hn; nlinarith
  nlinarith [mul_nonneg hba (sub_nonneg.mpr hpp)]

variable {s : ℕ}

lemma stNuM_eq (D : StagData s) (p : K) (c' : Fin s) (t : ℕ) :
    stNuM D p c' t = (stCoef D c' (D.rows c' t) : K) * ((D.u : K) * p - 2) := rfl

lemma stNP_zero (D : StagData s) (p : K) (c' : Fin s) :
    stNP D p c' 0 = 2 + max 0 (((1 - 2 * (stFrac D c' (D.rows c' 0) : K)) * p + 1) /
      ((stCoef D c' (D.rows c' 0) : K) * ((D.u : K) * p - 2))) := by
  simp only [stNP, stEll, stNuM]
  congr 2; ring

/-- `N_t^+` is non-increasing in `p`. -/
theorem stNP_anti (D : StagData s) {p p' : K} (hp : 0 < p) (hpp : p ≤ p') (hu : 2 < (D.u : K) * p)
    (c' : Fin s) : ∀ t, stNP D p' c' t ≤ stNP D p c' t := by
  intro t
  induction t with
  | zero =>
    rw [stNP_zero, stNP_zero]
    have := mono_term0 (1 - 2 * (stFrac D c' (D.rows c' 0) : K)) (stCoef D c' (D.rows c' 0) : K) (D.u : K) p p'
      (Nat.cast_nonneg _) hp hpp hu
    linarith
  | succ t ih =>
    simp only [stNP, stNuM]
    have := mono_term (stCoef D c' (D.rows c' (t + 1)) : K) (D.u : K) p p' (Nat.cast_nonneg _) hp hpp hu
    linarith

lemma stNP_ge_two (D : StagData s) {p : K} (hp : 0 < p) (hu : 2 < (D.u : K) * p) (c' : Fin s) :
    ∀ t, 2 ≤ stNP D p c' t := by
  intro t
  induction t with
  | zero => simp only [stNP]; linarith [le_max_left (0 : K) ((p - stEll D p c' 0) / stNuM D p c' 0)]
  | succ t ih =>
    simp only [stNP]
    have : 0 ≤ p / stNuM D p c' (t + 1) := by
      unfold stNuM
      exact div_nonneg hp.le (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    linarith

/-! ### The fold `M^+` -/

lemma foldr_max_nonneg (cs : Fin s) (g : Fin s → K) (l : List (Fin s)) :
    0 ≤ l.foldr (fun c m => if c = cs then m else max (g c) m) 0 := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldr_cons]
    split_ifs
    · exact ih
    · exact ih.trans (le_max_right _ _)

lemma foldr_max_ge (cs : Fin s) (g : Fin s → K) (l : List (Fin s)) (c : Fin s) (hc : c ∈ l)
    (hcs : c ≠ cs) : g c ≤ l.foldr (fun c m => if c = cs then m else max (g c) m) 0 := by
  induction l with
  | nil => simp at hc
  | cons d l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hc with h | h
    · subst h; rw [if_neg hcs]; exact le_max_left _ _
    · split_ifs
      · exact ih h
      · exact (ih h).trans (le_max_right _ _)

lemma foldr_max_mono (cs : Fin s) (g g' : Fin s → K) (hg : ∀ c, g' c ≤ g c) (l : List (Fin s)) :
    l.foldr (fun c m => if c = cs then m else max (g' c) m) 0 ≤
      l.foldr (fun c m => if c = cs then m else max (g c) m) 0 := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldr_cons]
    split_ifs
    · exact ih
    · exact max_le_max (hg c) ih

lemma stMP_nonneg (D : StagData s) (p : K) : 0 ≤ stMP D p := foldr_max_nonneg _ _ _

lemma stMP_ge (D : StagData s) (p : K) (c : Fin s) (hc : c ≠ D.cs) :
    2 * stNP D p c (s - 2) - 1 ≤ stMP D p :=
  foldr_max_ge D.cs (fun c => 2 * stNP D p c (s - 2) - 1) _ c (List.mem_finRange c) hc

/-- `M^+` is non-increasing in `p`. -/
theorem stMP_anti (D : StagData s) {p p' : K} (hp : 0 < p) (hpp : p ≤ p') (hu : 2 < (D.u : K) * p) :
    stMP D p' ≤ stMP D p :=
  foldr_max_mono D.cs _ _ (fun c => by linarith [stNP_anti D hp hpp hu c (s - 2)]) _

lemma u_pos_of (u p : K) (hp : 0 < p) (h : 2 < u * p) : 0 < u := by
  by_contra hu; push_neg at hu; nlinarith

lemma coef_pos_of (a p b : K) (hp : 0 < p) (hb : 0 < b) (h : b ≤ a * p) : 0 < a := by
  by_contra ha; push_neg at ha; nlinarith

/-- **`prop:P0`(b)** (monotone threshold): for `0 < p ≤ p'`, `𝒫(p)` implies `𝒫(p')`, and `M⋆^+(p') ≤ M⋆^+(p)`
(each `N_t^+` is a sum of terms non-increasing in `p`, and after division by `p` every inequality of `𝒫` has
the form "non-increasing ≤ non-decreasing"). -/
theorem P0_mono (D : StagData s) {p p' : K} (hp : 0 < p) (hpp : p ≤ p') (hP : StP D p) :
    StP D p' ∧ stMstP D p' ≤ stMstP D p := by
  obtain ⟨hP1, hP2, hP3, hP3h, ⟨hP4a, hP4b⟩, ⟨hP5a, hP5b⟩, hP6a, hP6b, hP6c⟩ := hP
  have hp' : 0 < p' := lt_of_lt_of_le hp hpp
  have hu0 : 0 < (D.u : K) := u_pos_of _ _ hp hP1
  have hup : (D.u : K) * p ≤ (D.u : K) * p' := mul_le_mul_of_nonneg_left hpp hu0.le
  have hNP := fun c' t => stNP_anti D hp hpp hP1 c' t
  have hMP := stMP_anti D hp hpp hP1
  have hMst : stMstP D p' ≤ stMstP D p := hNP D.cs (s - 2)
  have hMP0 := stMP_nonneg D p
  have hMP0' := stMP_nonneg D p'
  have hMst2 : 2 ≤ stMstP D p := stNP_ge_two D hp hP1 D.cs (s - 2)
  -- `x > 0`, `y > 0`
  have hx0 : 0 < (stX D : K) := lt_of_le_of_lt (div_nonneg hMP0 hp.le) hP6c
  have hySC : (0 : K) < 1 - 2 * (D.eSC : K) :=
    coef_pos_of _ p (2 * stMstP D p + 3) hp (by linarith) (by linarith)
  have hy0 : 0 < (stY D : K) := by unfold stY; push_cast; linarith
  have hMPdiv : stMP D p' / p' ≤ stMP D p / p := by
    calc stMP D p' / p' ≤ stMP D p / p' := div_le_div_of_nonneg_right hMP hp'.le
      _ ≤ stMP D p / p := div_le_div_of_nonneg_left hMP0 hp hpp
  refine ⟨⟨lt_of_lt_of_le hP1 hup, fun c' => ⟨?_, fun t ht => ?_⟩, fun c c' hc hcc => ?_, fun i hi => ?_,
    ⟨hP4a, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩, hMst⟩
  · -- (P2), first row
    have h := (hP2 c').1
    unfold stNuP stEll at h ⊢
    rw [← mul_assoc] at h ⊢
    exact mono_aff _ _ 1 p p' hp hpp zero_le_one h
  · -- (P2), slow rows
    have h := (hP2 c').2 t ht
    unfold stNuP stEll at h ⊢
    have hc0 : (0 : K) ≤ (stCoef D c' (D.rows c' (t + 1)) : K) * ((D.u : K) * p') :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have h' : stNP D p c' t * (stCoef D c' (D.rows c' (t + 1)) : K) * D.u * p ≤
        2 * (stFrac D c' (D.rows c' (t + 1)) : K) * p - 1 := by
      rw [mul_assoc (stNP D p c' t * _), mul_assoc (stNP D p c' t)]; exact h
    have h2 := mono_aff _ _ 1 p p' hp hpp zero_le_one h'
    calc stNP D p' c' t * ((stCoef D c' (D.rows c' (t + 1)) : K) * ((D.u : K) * p'))
        ≤ stNP D p c' t * ((stCoef D c' (D.rows c' (t + 1)) : K) * ((D.u : K) * p')) :=
          mul_le_mul_of_nonneg_right (hNP c' t) hc0
      _ = stNP D p c' t * (stCoef D c' (D.rows c' (t + 1)) : K) * D.u * p' := by ring
      _ ≤ _ := h2
  · -- (P3)
    have h := hP3 c c' hc hcc
    rw [← mul_assoc] at h ⊢
    exact mono_aff _ _ 1 p p' hp hpp zero_le_one h
  · have h := hP3h i hi
    have h' : ((D.nI D.cs i).natAbs : K) * D.u * p ≤ 2 * (D.eSC : K) * p - 3 := by
      rw [mul_assoc]; linarith
    have := mono_aff _ _ 3 p p' hp hpp (by norm_num) h'
    rw [← mul_assoc]; linarith
  · -- (P4)
    have hq : (0 : K) ≤ (stX D : K) ^ 2 + (stY D : K) ^ 2 - 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_right hpp hq
    have h2 := mul_le_mul_of_nonneg_left hMP (show (0 : K) ≤ 2 * stX D by linarith)
    have h3 := mul_le_mul_of_nonneg_left (show stMstP D p' + 1 / 2 ≤ stMstP D p + 1 / 2 by linarith)
      (show (0 : K) ≤ 2 * stY D by linarith)
    linarith
  · -- (P5)
    unfold stZ at hP5a ⊢; linarith
  · unfold stZ at hP5a hP5b ⊢
    have hz : 1 - 2 * ((s - 2 : ℕ) : K) * (D.eCC : K) - 2 * (D.eCS : K) - stMP D p / p ≤
        1 - 2 * ((s - 2 : ℕ) : K) * (D.eCC : K) - 2 * (D.eCS : K) - stMP D p' / p' := by linarith
    have := pow_le_pow_left₀ hP5a hz 2
    linarith
  · -- (P6)
    have hα : (0 : K) < 1 - (2 * ((s - 2 : ℕ) : K) * (D.eCC : K) + 2 * (D.eCS : K)) :=
      coef_pos_of _ p (stMP D p + 3) hp (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left hpp hα.le
    linarith
  · have := mul_le_mul_of_nonneg_left hpp hySC.le
    linarith
  · exact lt_of_le_of_lt hMPdiv hP6c

end Mono

/-! ## `ℚ` versus `ℝ` -/

section Cast

variable {s : ℕ}

lemma stNP_cast (D : StagData s) (q : ℚ) (c' : Fin s) :
    ∀ t, ((stNP D q c' t : ℚ) : ℝ) = stNP D (q : ℝ) c' t := by
  intro t
  induction t with
  | zero => simp only [stNP, stEll, stNuM]; push_cast; rfl
  | succ t ih => simp only [stNP, stNuM]; push_cast; rw [ih]

lemma stMP_cast (D : StagData s) (q : ℚ) : ((stMP D q : ℚ) : ℝ) = stMP D (q : ℝ) := by
  unfold stMP
  induction (List.finRange s) with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldr_cons]
    split_ifs
    · exact ih
    · rw [Rat.cast_max, ih]; push_cast; rw [stNP_cast]

lemma stMstP_cast (D : StagData s) (q : ℚ) : ((stMstP D q : ℚ) : ℝ) = stMstP D (q : ℝ) := stNP_cast D q _ _

/-- **`𝒫` at a rational point** is the same over `ℚ` and over `ℝ`. -/
theorem StP_cast (D : StagData s) (q : ℚ) : StP D q ↔ StP D (q : ℝ) := by
  unfold StP stZ stNuP stEll
  simp only [← stNP_cast, ← stMP_cast, ← stMstP_cast]
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
  norm_cast

end Cast

end GeoSeq
