/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Rel

@[expose] public section

/-!
# GeoSeq stage V9-8 (part 2): counting exact digit relations (`thm:count`)

Over any field, distinct places, any scramble of the frame; a range of levels `[K₀, K₀ + R]` that is admissible
(`(s-1)R + s - 2 < K₀`; for depth `J` also `J ≤ K₀`).

* `count_key`: relations at the levels `K₀ + i` whose place-`c` parts add up to zero all vanish (the proof of
  `thm:count`: `B = ∑ A_T w^{T*-T}` is divisible by `(z - a_c)^{T*+1}` and has smaller degree, so `B = 0`, and the
  `w`-adic expansion is unique).
* **`count_refined`** (`thm:count`, refined form): `∑_T r_T ≤ |𝒩_c|` for spaces of relations whose coordinate-`c`
  coefficients vanish outside a set `𝒩_c` of digit positions; **`count`** (`thm:count`): `∑_T r_T ≤ J + R + 1` for
  relations of depth at most `J` at `c`.
-/

namespace GeoSeq

open Finset Polynomial Module

section Count
variable {F : Type*} [Field F] {s : ℕ}

lemma resAt_level (a : Fin s → F) (ha : Function.Injective a) (c : Fin s) (k e : ℕ) (V : F[X]) :
    locRes (a c) (k + e) (V * wPoly a ^ e) (wCo a c ^ (k + e)) = locRes (a c) k V (wCo a c ^ k) := by
  rw [wPoly_eq a c, mul_pow, show wCo a c ^ (k + e) = wCo a c ^ e * wCo a c ^ k by ring,
    locRes_shift _ _ _ _ _ _ (by rw [eval_pow]; exact pow_ne_zero _ (wCo_eval_ne a ha c))]

/-- **The key step of `thm:count`.** If `g_i` is a relation of top index `K₀ + i` on `P_{s(K₀+i)}` (`i ≤ R`) and
the coordinate-`c` coefficients of the `g_i` add up to zero, then every `g_i` is zero. -/
theorem count_key (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R : ℕ) (hadm : (s - 1) * R + s - 2 < K₀) (g : ℕ → Fin s → ℕ → F)
    (hg : ∀ i ≤ R, g i ∈ relSpace a L (K₀ + i) (s * (K₀ + i)))
    (hsum : ∀ n, ∑ i ∈ range (R + 1), g i c n = 0) : ∀ i ≤ R, g i = 0 := by
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact c.elim0)
  set Ts := K₀ + R with hTs
  set A : ℕ → F[X] := fun i => relPoly a L (g i) (K₀ + i) with hAdef
  have hdegA : ∀ i ≤ R, (A i).degree < (s : WithBot ℕ) := by
    intro i hi
    have := relPoly_degree_lt a ha L (g i) (K₀ + i) (s * (K₀ + i)) (hg i hi)
    rwa [show s * (K₀ + i + 1) - s * (K₀ + i) = s by rw [Nat.mul_succ]; omega] at this
  have hnatA : ∀ i ≤ R, (A i).natDegree ≤ s - 1 := by
    intro i hi
    rcases eq_or_ne (A i) 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · have := hdegA i hi
      rw [degree_eq_natDegree h0] at this
      have : (A i).natDegree < s := by exact_mod_cast this
      omega
  set B : F[X] := ∑ i ∈ range (R + 1), A i * wPoly a ^ (R - i) with hB
  -- `(z - a_c)^{Ts+1}` divides `B`
  have hdvd : (X - C (a c)) ^ (Ts + 1) ∣ B := by
    refine dvd_of_locRes (a c) Ts B (wCo a c ^ (Ts + 1))
      (by rw [eval_pow]; exact pow_ne_zero _ (wCo_eval_ne a ha c)) fun V => ?_
    rw [hB, Finset.mul_sum, locRes_sum]
    have hterm : ∀ i ∈ range (R + 1), locRes (a c) (Ts + 1) (V * (A i * wPoly a ^ (R - i))) (wCo a c ^ (Ts + 1)) =
        ∑ k ∈ range (Ts + 1), (∑ n ∈ range (Ts + 1), if k ≤ n then g i c n * L c n k else 0) *
          (taylor (a c) V).coeff k := by
      intro i hi
      have hi' : i ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have e := resAt_level a ha c (K₀ + i + 1) (R - i) (V * A i)
      rw [show K₀ + i + 1 + (R - i) = Ts + 1 by omega] at e
      rw [show V * (A i * wPoly a ^ (R - i)) = (V * A i) * wPoly a ^ (R - i) by ring, e,
        ← place_eq_locRes a ha]
      rw [← Finset.sum_range_add_sum_Ico _ (show K₀ + i + 1 ≤ Ts + 1 by omega)]
      have hz : ∑ k ∈ Finset.Ico (K₀ + i + 1) (Ts + 1),
          (∑ n ∈ range (Ts + 1), if k ≤ n then g i c n * L c n k else 0) *
            (taylor (a c) V).coeff k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [← relG_ext L (g i) c (K₀ + i) Ts k (by omega) (fun n hn => (hg i hi').1 c n hn),
          relG_high _ _ _ _ _ (by simp at hk; omega), zero_mul]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [relG_ext L (g i) c (K₀ + i) Ts k (by omega) (fun n hn => (hg i hi').1 c n hn)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i ∈ range (R + 1), ∑ n ∈ range (Ts + 1), (if k ≤ n then g i c n * L c n k else 0) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun n _ => ?_
      split_ifs
      · rw [← Finset.sum_mul, hsum n, zero_mul]
      · exact Finset.sum_const_zero
    rw [this, zero_mul]
  -- degree bound and `B = 0`
  have hBdeg : B.natDegree < Ts + 1 := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := s - 1 + s * R) fun i hi => ?_) ?_
    · have hi' : i ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      refine natDegree_mul_le.trans ?_
      rw [natDegree_pow, natDegree_wPoly]
      have := hnatA i hi'
      have : (R - i) * s ≤ s * R := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hadm ⊢
      rw [add_mul, one_mul]
      omega
  have hB0 : B = 0 := eq_zero_of_dvd_of_natDegree_lt hdvd (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact hBdeg)
  -- uniqueness of the `w`-adic expansion
  have hrefl : ∑ j ∈ range (R + 1), A (R - j) * wPoly a ^ j = 0 := by
    rw [← hB0, hB, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < R + 1 := Finset.mem_range.mp hj
    rw [show R + 1 - 1 - j = R - j by omega, show R - (R - j) = j by omega]
  have hAz := wadic_unique (wPoly a) (wPoly_monic a).ne_zero (R + 1) (fun j => A (R - j))
    (fun j hj => by
      rw [degree_eq_natDegree (wPoly_monic a).ne_zero, natDegree_wPoly]
      exact hdegA (R - j) (by omega)) hrefl
  intro i hi
  have h0 : A i = 0 := by have := hAz (R - i) (by omega); rwa [show R - (R - i) = i by omega] at this
  exact (relPoly_eq_zero_iff a ha L hL (g i) (K₀ + i) (hg i hi).1).mp h0

/-- **`thm:count`, refined form.** Let `[K₀, K₀ + R]` be admissible (`(s-1)R + s - 2 < K₀`), fix a coordinate `c`, and
for every level `T = K₀ + i` let `W_T` be a space of exact digit relations of top index `T` on `P_{sT}` (the
coefficients may depend on `T`) whose coordinate-`c` coefficients vanish outside the digit positions `𝒩`. Then
`∑_T dim W_T ≤ |𝒩|`. -/
theorem count_refined (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R : ℕ) (hadm : (s - 1) * R + s - 2 < K₀) (W : ℕ → Submodule F (Fin s → ℕ → F))
    (hW : ∀ i ≤ R, W (K₀ + i) ≤ relSpace a L (K₀ + i) (s * (K₀ + i))) (𝒩 : Finset ℕ)
    (hN : ∀ i ≤ R, W (K₀ + i) ≤ colSupp c 𝒩) :
    ∑ i ∈ range (R + 1), finrank F (W (K₀ + i)) ≤ 𝒩.card := by
  classical
  let Φ : ((i : Fin (R + 1)) → W (K₀ + (i : ℕ))) →ₗ[F] (𝒩 → F) :=
    { toFun := fun x n => ∑ i : Fin (R + 1), (x i).1 c n
      map_add' := by intro x y; funext n; simp [Finset.sum_add_distrib]
      map_smul' := by intro r x; funext n; simp [Finset.mul_sum] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    let g : ℕ → Fin s → ℕ → F := fun i => if h : i < R + 1 then (x ⟨i, h⟩).1 else 0
    have hg : ∀ i ≤ R, g i ∈ relSpace a L (K₀ + i) (s * (K₀ + i)) := by
      intro i hi
      simp only [g, dif_pos (show i < R + 1 by omega)]
      exact hW i hi (x ⟨i, by omega⟩).2
    have hsum : ∀ n, ∑ i ∈ range (R + 1), g i c n = 0 := by
      intro n
      rw [← Fin.sum_univ_eq_sum_range (fun i => g i c n)]
      by_cases hn : n ∈ 𝒩
      · have e : ∑ i : Fin (R + 1), g i c n = ∑ i : Fin (R + 1), (x i).1 c n :=
          Finset.sum_congr rfl fun i _ => by simp only [g, dif_pos i.2]
        rw [e]
        have := congrFun hx ⟨n, hn⟩
        simpa [Φ] using this
      · refine Finset.sum_eq_zero fun i _ => ?_
        simp only [g, dif_pos i.2]
        exact hN i (by omega) (x i).2 n hn
    have hz := count_key a ha L hL c K₀ R hadm g hg hsum
    funext i
    have := hz i (by omega)
    simp only [g, dif_pos i.2] at this
    exact Subtype.ext this
  have hfin : ∀ i : Fin (R + 1), Module.Finite F (W (K₀ + (i : ℕ))) := fun i =>
    Module.Finite.of_injective (Φ ∘ₗ LinearMap.single F (fun i : Fin (R + 1) => W (K₀ + (i : ℕ))) i)
      (hinj.comp (by rw [LinearMap.coe_single]; exact Pi.single_injective i))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
  rw [← Fin.sum_univ_eq_sum_range (fun i => finrank F (W (K₀ + i)))]
  exact h1

/-- **`thm:count`** (counting exact digit relations). Let `[K₀, K₀ + R]` be admissible for depth `J`
(`J ≤ K₀` and `(s-1)R + s - 2 < K₀`) and fix a coordinate `c`. For every level `T = K₀ + i` let `W_T` be a space
of exact digit relations of top index `T` on `P_{sT}` whose depth at coordinate `c` is at most `J` (the depth at the
other coordinates is arbitrary, the coefficients may depend on `T`). Then `∑_{T=K₀}^{K₀+R} dim W_T ≤ J + R + 1`. -/
theorem count (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (c : Fin s) (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀)
    (W : ℕ → Submodule F (Fin s → ℕ → F))
    (hW : ∀ i ≤ R, W (K₀ + i) ≤ relSpace a L (K₀ + i) (s * (K₀ + i)))
    (hdepth : ∀ i ≤ R, ∀ f ∈ W (K₀ + i), DepthAt (K₀ + i) J c f) :
    ∑ i ∈ range (R + 1), finrank F (W (K₀ + i)) ≤ J + R + 1 := by
  have h := count_refined a ha L hL c K₀ R hadm W hW (Finset.Ico (K₀ - J) (K₀ + R + 1)) (fun i hi f hf n hn => by
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
    rcases hn with hn | hn
    · exact hdepth i hi f hf n (by omega)
    · exact (hW i hi hf).1 c n (by omega))
  rwa [Nat.card_Ico, show K₀ + R + 1 - (K₀ - J) = J + R + 1 by omega] at h

end Count

end GeoSeq
