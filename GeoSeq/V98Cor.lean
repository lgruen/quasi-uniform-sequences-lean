/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Rigid

@[expose] public section

/-!
# GeoSeq stage V9-8 (part 4): corollaries of `thm:count`

Over any field, distinct places, any scramble of the frame.

* `count_ge`: `thm:count` with lower bounds `d_T ≤ dim W_T`, summed over `T ∈ [K₀, K₀ + R]`.
* **`layer_a`** (`cor:layer`(a), range form): `s · |E ∩ [K₀, K₀+R]| ≤ J + R + 1`; **`layer_b`** (`cor:layer`(b));
  **`layer_c`** (`cor:layer`(c)); **`N1_count`** (`cor:N1`, by the refined count at coordinate `1`);
  **`density`** (`cor:density`, range form): `|S ∩ I| + (s-1)|E ∩ I| ≤ J + R + 1`.
* **`onerel_dim`** (`prop:onerel`(i), dimension part): the level-independent relations form a space of dimension at
  most one; **`blockrel`** (`prop:blockrel`): `d_0 + … + d_{ℓ-1} ≤ ℓ`. Both are proved here for EVERY scramble of the
  frame by `thm:count` (the paper states them for self-similar resp. block-periodic scrambles, with a different
  proof; the lead-in to `prop:onerel` derives the bound from `thm:count` as here).
-/

namespace GeoSeq

open Finset Polynomial Module

section Cor
variable {F : Type*} [Field F] {s : ℕ}

/-- Relations on a larger prefix are relations on a smaller one. -/
lemma relSpace_mono (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (T : ℕ) {m m' : ℕ} (h : m' ≤ m) :
    relSpace a L T m ≤ relSpace a L T m' :=
  fun _ hf => ⟨hf.1, fun V hV => hf.2 V (by omega)⟩

lemma sum_Icc_eq_range (g : ℕ → ℕ) (K₀ R : ℕ) :
    ∑ T ∈ Finset.Icc K₀ (K₀ + R), g T = ∑ i ∈ range (R + 1), g (K₀ + i) := by
  rw [show Finset.Icc K₀ (K₀ + R) = Finset.Ico K₀ (K₀ + R + 1) by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range, show K₀ + R + 1 - K₀ = R + 1 by omega]

lemma sum_ite_card (P : ℕ → Prop) [DecidablePred P] (t : Finset ℕ) (k : ℕ) :
    ∑ T ∈ t, (if P T then k else 0) = k * (t.filter P).card := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

/-- `thm:count` with lower bounds `d_T ≤ dim W_T`, summed over the levels `T ∈ [K₀, K₀ + R]`. -/
theorem count_ge (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀)
    (W : ℕ → Submodule F (Fin s → ℕ → F))
    (hW : ∀ T, K₀ ≤ T → T ≤ K₀ + R → W T ≤ relSpace a L T (s * T) ⊓ depthSub T J c)
    (d : ℕ → ℕ) (hd : ∀ T, K₀ ≤ T → T ≤ K₀ + R → d T ≤ finrank F (W T)) :
    ∑ T ∈ Finset.Icc K₀ (K₀ + R), d T ≤ J + R + 1 := by
  have h := count a ha L hL c K₀ R J hJ hadm W (fun i hi => (hW (K₀ + i) (by omega) (by omega)).trans inf_le_left)
    (fun i hi f hf => ((hW (K₀ + i) (by omega) (by omega)) hf).2)
  rw [sum_Icc_eq_range]
  exact le_trans (Finset.sum_le_sum fun i hi => hd (K₀ + i) (by omega)
    (by have := Finset.mem_range.mp hi; omega)) h

/-- Families with prescribed "pivot" coefficients are linearly independent. -/
lemma linInd_pivot {k : ℕ} (v : Fin k → Fin s → ℕ → F) (pc : Fin k → Fin s) (pn : ℕ)
    (hv : ∀ i j, v i (pc j) pn = if i = j then 1 else 0) : LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrFun (congrFun hg (pc j)) pn
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
  exact this

lemma finrank_span_pivot {k : ℕ} (v : Fin k → Fin s → ℕ → F) (pc : Fin k → Fin s) (pn : ℕ)
    (hv : ∀ i j, v i (pc j) pn = if i = j then 1 else 0) :
    finrank F (Submodule.span F (Set.range v)) = k := by
  rw [finrank_span_eq_card (linInd_pivot v pc pn hv), Fintype.card_fin]

/-- The `s` design relations of a level `T ∈ E` are independent (pivots `(i, T)`). -/
lemma design_pivot (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (J T : ℕ) (d : Fin s → Fin s → ℕ → F)
    (hd : ∀ i, IsDesign a L J T i (d i)) : ∀ i j, d i j T = if i = j then 1 else 0 := by
  intro i j
  split_ifs with h
  · subst h; exact (hd i).2.1
  · exact (hd i).2.2.1 j (Ne.symm h)

/-- **`cor:layer`(a)**, range form: if `E` is the set of levels at which all `s` geometric digits of `P_{sT}` are
designed by exact relations of depth at most `J`, then `s · |E ∩ [K₀, K₀+R]| ≤ J + R + 1` for every admissible
range. -/
theorem layer_a (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀) [DecidablePred (AllDesigned a L J)] :
    s * ((Finset.Icc K₀ (K₀ + R)).filter (AllDesigned a L J)).card ≤ J + R + 1 := by
  classical
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp
  have c : Fin s := ⟨0, hs⟩
  choose! dsg hdsg using fun T (h : AllDesigned a L J T) => (show ∀ i, ∃ f, IsDesign a L J T i f from h)
  let W : ℕ → Submodule F (Fin s → ℕ → F) := fun T =>
    if AllDesigned a L J T then Submodule.span F (Set.range (fun i => dsg T i)) else ⊥
  have h := count_ge a ha L hL c K₀ R J hJ hadm W (fun T _ _ => by
      simp only [W]; split_ifs with hT
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨(hdsg T hT i).1, (hdsg T hT i).2.2.2 c⟩
      · exact bot_le)
    (fun T => if AllDesigned a L J T then s else 0) (fun T _ _ => by
      by_cases hT : AllDesigned a L J T
      · have hWT : W T = Submodule.span F (Set.range fun i => dsg T i) := if_pos hT
        rw [hWT, finrank_span_pivot (fun i => dsg T i) id T (design_pivot a L J T _ (hdsg T hT)), if_pos hT]
      · simp only [if_neg hT]; exact Nat.zero_le _)
  rwa [sum_ite_card] at h

/-- **`cor:layer`(b)**: two geometric digits of coordinates `i ≠ i'` are not both designed with depth at most `J`
at all the levels `K₀, …, K₀ + J`, if `K₀ > (s-1)J + s - 2` (`s ≥ 2`). -/
theorem layer_b (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (K₀ J : ℕ) (hadm : (s - 1) * J + s - 2 < K₀) (i i' : Fin s) (hii : i ≠ i')
    (f f' : ℕ → Fin s → ℕ → F)
    (hf : ∀ T, K₀ ≤ T → T ≤ K₀ + J → IsDesign a L J T i (f T) ∧ IsDesign a L J T i' (f' T)) : False := by
  have hJ : J ≤ K₀ := by
    have : J ≤ (s - 1) * J := Nat.le_mul_of_pos_left J (by omega)
    omega
  let v : ℕ → Fin 2 → Fin s → ℕ → F := fun T => ![f T, f' T]
  let W : ℕ → Submodule F (Fin s → ℕ → F) := fun T => Submodule.span F (Set.range (v T))
  have h := count_ge a ha L hL i K₀ J J hJ hadm W (fun T h1 h2 => by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      fin_cases k
      · exact ⟨(hf T h1 h2).1.1, (hf T h1 h2).1.2.2.2 i⟩
      · exact ⟨(hf T h1 h2).2.1, (hf T h1 h2).2.2.2.2 i⟩)
    (fun _ => 2) (fun T h1 h2 => by
      refine le_of_eq (finrank_span_pivot (v T) ![i, i'] T (fun k k' => ?_)).symm
      obtain ⟨⟨h1a, h1b, h1c, -⟩, ⟨h2a, h2b, h2c, -⟩⟩ := hf T h1 h2
      fin_cases k <;> fin_cases k' <;> simp [v, h1b, h2b, h1c i' (Ne.symm hii), h2c i hii])
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h
  omega

/-- **`cor:layer`(c)**: a staggered relation `y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` and a skeleton
relation `∑_c u_c y_{c,T} = 0` on `P_{s(T+1)-1}` (any coefficients, `u ≠ 0`) do not both hold at two consecutive
levels `T = K₀, K₀ + 1` with `K₀ ≥ 2s - 2` (`s ≥ 2`). -/
theorem layer_c (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (K₀ : ℕ) (hK : 2 * s - 2 ≤ K₀) (cs : Fin s) (k : ℕ → Fin s → F) (u : ℕ → Fin s → F)
    (hrel : ∀ T, K₀ ≤ T → T ≤ K₀ + 1 → stagVec cs (k T) T ∈ relSpace a L T (s * T) ∧ u T ≠ 0 ∧
      skelVec T (u T) ∈ relSpace a L T (s * (T + 1) - 1)) : False := by
  have hadm : (s - 1) * 1 + s - 2 < K₀ := by omega
  obtain ⟨c', hc'⟩ : ∃ c : Fin s, c ≠ cs := by
    by_cases h : (cs : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
  let v : ℕ → Fin 2 → Fin s → ℕ → F := fun T => ![stagVec cs (k T) T, skelVec T (u T)]
  let W : ℕ → Submodule F (Fin s → ℕ → F) := fun T => Submodule.span F (Set.range (v T))
  have h := count_ge a ha L hL cs K₀ 1 1 (by omega) hadm W (fun T h1 h2 => by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      fin_cases j
      · refine ⟨(hrel T h1 h2).1, fun n hn => ?_⟩
        simp [v, stagVec, show n ≠ T by omega]
      · refine ⟨relSpace_mono a L T (by rw [Nat.mul_succ]; omega) (hrel T h1 h2).2.2, fun n hn => ?_⟩
        simp [v, skelVec, show n ≠ T by omega])
    (fun _ => 2) (fun T h1 h2 => by
      obtain ⟨-, hu, hsk⟩ := hrel T h1 h2
      have hu0 := (rigid a ha L hL T (u T) hu hsk).1
      suffices hli : LinearIndependent F (v T) by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      have e1 := congrFun (congrFun hg c') T
      have e2 := congrFun (congrFun hg cs) T
      simp [v, stagVec, skelVec, Fin.sum_univ_two, hc'] at e1 e2
      have hg1 : g 1 = 0 := e1.resolve_right (hu0 c')
      have hg0 : g 0 = 0 := by rw [hg1, zero_mul, add_zero] at e2; exact e2
      fin_cases j
      · exact hg0
      · exact hg1)
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h
  omega

/-- **`cor:N1`** (no lattice offset map), relation form, by the refined count at coordinate `1` (V4 route). For
`s = 2`, any two distinct places (e.g. `a = (0, 1)`) over any field, any scramble and `K ≥ 2`, the following three
relations do not hold together: `y_{0,K} = X y_{1,K-1} + (cell digits of coordinate 0)` on `P_{2K}` (`f₁`),
`y_{0,K+1} = X' y_{1,K} + (cell digits of coordinate 0)` on `P_{2K+2}` (`f₂`), and
`y_{1,K} = O y_{1,K-1} + (cell digits of coordinate 0)` on `P_{2K}` (`f₃`): the coefficients of coordinate `1` vanish
outside the indicated positions. (The direct proof of the V3 `prop:N1` is `GeoSeq.N1`.) -/
theorem N1_count (a : Fin 2 → F) (ha : Function.Injective a) (L : Fin 2 → ℕ → ℕ → F) (hL : IsScramble L)
    (K : ℕ) (hK : 2 ≤ K) (f₁ f₂ f₃ : Fin 2 → ℕ → F)
    (h₁ : f₁ ∈ relSpace a L K (2 * K) ∧ f₁ 0 K = 1 ∧ ∀ n, n ≠ K - 1 → f₁ 1 n = 0)
    (h₂ : f₂ ∈ relSpace a L (K + 1) (2 * (K + 1)) ∧ f₂ 0 (K + 1) = 1 ∧ ∀ n, n ≠ K → f₂ 1 n = 0)
    (h₃ : f₃ ∈ relSpace a L K (2 * K) ∧ f₃ 0 K = 0 ∧ f₃ 1 K = 1 ∧ ∀ n, n ≠ K - 1 → n ≠ K → f₃ 1 n = 0) :
    False := by
  classical
  let v : Fin 2 → Fin 2 → ℕ → F := ![f₁, f₃]
  let W : ℕ → Submodule F (Fin 2 → ℕ → F) := fun T =>
    if T = K then Submodule.span F (Set.range v) else Submodule.span F {f₂}
  have hWK : W K = Submodule.span F (Set.range v) := if_pos rfl
  have hWK1 : W (K + 1) = Submodule.span F {f₂} := if_neg (by omega)
  have h := count_refined a ha L hL 1 K 1 (by omega) W (fun i hi => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · rw [add_zero, hWK]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        fin_cases j
        · exact h₁.1
        · exact h₃.1
      · rw [hWK1, Submodule.span_le, Set.singleton_subset_iff]; exact h₂.1)
    {K - 1, K} (fun i hi => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · rw [add_zero, hWK]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        fin_cases j
        · intro n hn
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          exact h₁.2.2 n hn.1
        · intro n hn
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
          exact h₃.2.2.2 n hn.1 hn.2
      · rw [hWK1, Submodule.span_le, Set.singleton_subset_iff]
        intro n hn
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        exact h₂.2.2 n hn.2)
  have hli : LinearIndependent F v := linInd_pivot v ![0, 1] K (fun i j => by
    have h11 : f₁ 1 K = 0 := h₁.2.2 K (by omega)
    fin_cases i <;> fin_cases j <;> simp [v, h₁.2.1, h₃.2.1, h₃.2.2.1, h11])
  have hf₂ : f₂ ≠ 0 := fun h0 => by have := h₂.2.1; rw [h0] at this; simp at this
  have hcard : ({K - 1, K} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
  rw [Finset.sum_range_succ, Finset.sum_range_one, add_zero, hWK, hWK1, finrank_span_eq_card hli,
    finrank_span_singleton hf₂, Fintype.card_fin, hcard] at h
  omega

/-- **`cor:density`**, range form. Let `E` be the set of levels `T` at which all `s` geometric digits of `P_{sT}` are
designed by exact relations of depth at most `J`, and `S` the set of levels at which `P_{s(T+1)-1}` satisfies a
skeleton relation. Then `|S ∩ I| + (s-1) |E ∩ I| ≤ J + R + 1` for every admissible range `I = [K₀, K₀ + R]`. -/
theorem density (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀) [DecidablePred (AllDesigned a L J)]
    [DecidablePred (HasSkel a L)] :
    ((Finset.Icc K₀ (K₀ + R)).filter (HasSkel a L)).card +
      (s - 1) * ((Finset.Icc K₀ (K₀ + R)).filter (AllDesigned a L J)).card ≤ J + R + 1 := by
  classical
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : ∀ T, ¬ HasSkel a L T := fun T ⟨u, hu, _⟩ => hu (funext fun c => c.elim0)
    simp [this]
  have c : Fin s := ⟨0, hs⟩
  choose! dsg hdsg using fun T (h : AllDesigned a L J T) => (show ∀ i, ∃ f, IsDesign a L J T i f from h)
  choose! sk hsk using fun T (h : HasSkel a L T) => (show ∃ u, _ from h)
  let W : ℕ → Submodule F (Fin s → ℕ → F) := fun T =>
    if AllDesigned a L J T then Submodule.span F (Set.range (fun i => dsg T i))
    else if HasSkel a L T then Submodule.span F {skelVec T (sk T)} else ⊥
  let d : ℕ → ℕ := fun T => if AllDesigned a L J T then s else if HasSkel a L T then 1 else 0
  have h := count_ge a ha L hL c K₀ R J hJ hadm W (fun T _ _ => by
      by_cases hE : AllDesigned a L J T
      · have hWT : W T = Submodule.span F (Set.range fun i => dsg T i) := if_pos hE
        rw [hWT]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨(hdsg T hE i).1, (hdsg T hE i).2.2.2 c⟩
      · by_cases hS : HasSkel a L T
        · have hWT : W T = Submodule.span F {skelVec T (sk T)} := by simp only [W, if_neg hE, if_pos hS]
          rw [hWT, Submodule.span_le, Set.singleton_subset_iff]
          refine ⟨relSpace_mono a L T (by rw [Nat.mul_succ]; omega) (hsk T hS).2, fun n hn => ?_⟩
          simp [skelVec, show n ≠ T by omega]
        · have hWT : W T = ⊥ := by simp only [W, if_neg hE, if_neg hS]
          rw [hWT]; exact bot_le)
    d (fun T _ _ => by
      by_cases hE : AllDesigned a L J T
      · have hWT : W T = Submodule.span F (Set.range fun i => dsg T i) := if_pos hE
        rw [hWT, finrank_span_pivot (fun i => dsg T i) id T (design_pivot a L J T _ (hdsg T hE))]
        simp [d, hE]
      · by_cases hS : HasSkel a L T
        · have hWT : W T = Submodule.span F {skelVec T (sk T)} := by simp only [W, if_neg hE, if_pos hS]
          rw [hWT, finrank_span_singleton (skelVec_ne_zero T _ (hsk T hS).1)]
          simp [d, hE, hS]
        · simp [d, hE, hS])
  refine le_trans ?_ h
  have e1 : ((Finset.Icc K₀ (K₀ + R)).filter (HasSkel a L)).card =
      ∑ T ∈ Finset.Icc K₀ (K₀ + R), (if HasSkel a L T then 1 else 0) := by rw [sum_ite_card, one_mul]
  rw [e1, ← sum_ite_card, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  by_cases hE : AllDesigned a L J T <;> by_cases hS : HasSkel a L T <;> simp [d, hE, hS]; omega

/-- The linear map `ϑ ↦ liEmbed J T ϑ`. -/
def liEmbedLin (J T : ℕ) : (Fin s → ℕ → F) →ₗ[F] (Fin s → ℕ → F) where
  toFun := liEmbed J T
  map_add' := by intro f g; funext c n; simp only [liEmbed, Pi.add_apply]; split_ifs <;> simp
  map_smul' := by intro r f; funext c n; simp only [liEmbed, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

lemma liEmbed_inj (J T : ℕ) (hJT : J ≤ T) (ϑ : Fin s → ℕ → F) (hϑ : ∀ c i, J < i → ϑ c i = 0)
    (h0 : liEmbed J T ϑ = 0) : ϑ = 0 := by
  funext c i
  rcases Nat.lt_or_ge J i with h | h
  · exact hϑ c i h
  · have := congrFun (congrFun h0 c) (T - i)
    simp only [liEmbed, Pi.zero_apply] at this
    rw [if_pos ⟨by omega, by omega⟩, show T - (T - i) = i by omega] at this
    exact this

lemma liEmbed_depth (J T : ℕ) (ϑ : Fin s → ℕ → F) (c : Fin s) : DepthAt T J c (liEmbed J T ϑ) := by
  intro n hn; simp only [liEmbed]; rw [if_neg (by omega)]

/-- The level-`T` images of a space of level-independent families, as a space of relations. -/
lemma li_finrank (P : Submodule F (Fin s → ℕ → F)) (J T : ℕ) (hJT : J ≤ T)
    (hP : ∀ ϑ ∈ P, ∀ c i, J < i → ϑ c i = 0) :
    finrank F (LinearMap.range ((liEmbedLin J T : (Fin s → ℕ → F) →ₗ[F] _) ∘ₗ P.subtype)) = finrank F P := by
  refine LinearMap.finrank_range_of_inj fun x y hxy => ?_
  have h : liEmbed J T (x.1 - y.1) = 0 := by
    have := congrArg (fun z => z) hxy
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    have e := (liEmbedLin (F := F) (s := s) J T).map_sub x.1 y.1
    simp only [liEmbedLin, LinearMap.coe_mk, AddHom.coe_mk] at e this
    rw [e, this, sub_self]
  have := liEmbed_inj J T hJT (x.1 - y.1) (fun c i hi => by
    simp [hP x.1 x.2 c i hi, hP y.1 y.2 c i hi]) h
  exact Subtype.ext (sub_eq_zero.mp this)

/-- **`prop:onerel`(i), dimension part** — here for EVERY scramble of the frame: the level-independent relations
`∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i} = 0` on `P_{sT}` for all `T ≥ T₀` (`T₀ ≥ J`) form a space of dimension at most
one. -/
theorem onerel_dim (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (J T₀ : ℕ) (hJ : J ≤ T₀) : finrank F (liSpace a L J T₀) ≤ 1 := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : liSpace a L J T₀ = ⊥ := by
      rw [eq_bot_iff]; intro ϑ _; funext c; exact c.elim0
    rw [this, finrank_bot]; exact Nat.zero_le _
  have c : Fin s := ⟨0, hs⟩
  set P := liSpace a L J T₀
  set K₀ := T₀ + (s - 1) * J + s
  let W : ℕ → Submodule F (Fin s → ℕ → F) := fun T =>
    LinearMap.range ((liEmbedLin J T : (Fin s → ℕ → F) →ₗ[F] _) ∘ₗ P.subtype)
  have h := count_ge a ha L hL c K₀ J J (by omega) (by omega) W (fun T h1 _ => by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.2.2 T (by omega), liEmbed_depth J T x.1 c⟩)
    (fun _ => finrank F P) (fun T h1 _ => (li_finrank P J T (by omega) fun ϑ hϑ => hϑ.1).ge)
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, show K₀ + J + 1 - K₀ = J + 1 by omega] at h
  by_contra hc
  have : (J + 1) * 2 ≤ (J + 1) * finrank F P := Nat.mul_le_mul_left _ (by omega)
  omega

lemma sum_range_mod (ℓ M : ℕ) (g : ℕ → ℕ) :
    ∑ i ∈ range (ℓ * M), g (i % ℓ) = M * ∑ j ∈ range ℓ, g j := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, add_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx)]

/-- **`prop:blockrel`** — here for EVERY scramble of the frame: if `d_j` is the dimension of the space of
level-independent relations of class `j` (coefficients the same at all levels `T ≥ T₀` with `T ≡ j (mod ℓ)`, on
`P_{sT}`; `T₀ ≥ J`), then `d_0 + … + d_{ℓ-1} ≤ ℓ`. -/
theorem blockrel (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (ℓ J T₀ : ℕ) (hℓ : 1 ≤ ℓ) (hJ : J ≤ T₀) :
    ∑ j ∈ range ℓ, finrank F (classSpace a L ℓ j J T₀) ≤ ℓ := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : ∀ j, classSpace a L ℓ j J T₀ = ⊥ := fun j => by
      rw [eq_bot_iff]; intro ϑ _; funext c; exact c.elim0
    exact le_trans (le_of_eq (Finset.sum_eq_zero fun j _ => by rw [this j, finrank_bot])) (Nat.zero_le _)
  have c : Fin s := ⟨0, hs⟩
  set M := J + 1
  set R := ℓ * M - 1
  have hR : R + 1 = ℓ * M := by have : 1 ≤ ℓ * M := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
  set K₀ := ℓ * (T₀ + (s - 1) * R + s)
  have hK₀ : T₀ + (s - 1) * R + s ≤ K₀ := Nat.le_mul_of_pos_left _ hℓ
  let P : ℕ → Submodule F (Fin s → ℕ → F) := fun j => classSpace a L ℓ j J T₀
  let W : ℕ → Submodule F (Fin s → ℕ → F) := fun T =>
    LinearMap.range ((liEmbedLin J T : (Fin s → ℕ → F) →ₗ[F] _) ∘ₗ (P (T % ℓ)).subtype)
  have h := count_ge a ha L hL c K₀ R J (by omega) (by omega) W (fun T h1 _ => by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.2.2 T (by omega) rfl, liEmbed_depth J T x.1 c⟩)
    (fun T => finrank F (P (T % ℓ))) (fun T h1 _ => (li_finrank (P (T % ℓ)) J T (by omega)
      fun ϑ hϑ => hϑ.1).ge)
  rw [sum_Icc_eq_range, hR] at h
  have hmod : ∀ i, (K₀ + i) % ℓ = i % ℓ := fun i => by rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
  have e : ∀ i, finrank F (P ((K₀ + i) % ℓ)) = finrank F (P (i % ℓ)) := fun i => by
    rw [hmod i]
  rw [Finset.sum_congr rfl (fun i _ => e i), sum_range_mod ℓ M (fun j => finrank F (P j))] at h
  have hM : M = J + 1 := rfl
  show ∑ j ∈ range ℓ, finrank F (P j) ≤ ℓ
  by_contra hc
  have h2 : M * (ℓ + 1) ≤ M * ∑ j ∈ range ℓ, finrank F (P j) := Nat.mul_le_mul_left _ (by omega)
  have h3 := le_trans h2 h
  rw [add_assoc, hR, mul_add, mul_one, mul_comm M ℓ] at h3
  omega

end Cor

end GeoSeq
