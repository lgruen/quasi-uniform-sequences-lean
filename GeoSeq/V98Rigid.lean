/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Count

@[expose] public section

/-!
# GeoSeq stage V9-8 (part 3): skeleton relations fix the rows (`lem:rigid`, `cor:residuerows`, `cor:nodesign`)

Over any field, distinct places, any scramble of the frame.

* **`rigid`** (`lem:rigid`): an exact skeleton relation `∑_c v_c y_{c,n} = 0` on `P_{s(n+1)-1}` forces every `v_c ≠ 0`
  and `y_{c,n} = (ξ/v_c) ŷ_{c,n}` with one `ξ ≠ 0` (`ŷ_{c,n}(V) = Res_{a_c}(V w^{-n-1} dz)`, `resDig`).
* **`residuerows`** (`cor:residuerows`, first part, one level at a time): a skeleton relation at level `n` exists iff
  row `n` is the residue row up to nonzero scalars `μ_{c,n}`, and then `u_n ∝ (1/μ_{c,n})_c` (`residuerows_prop`).
* **`nodesign`** (`cor:nodesign`): with skeleton relations at the levels `K-J, …, K` (`K ≥ max(s-1, sJ)`), every
  exact relation of top index `K` and depth `≤ J` on `P_{sK}` is a multiple of `∑_c u_{c,K} y_{c,K}`;
  `nodesign_no_design`: no designed geometric digit of depth `≤ J` there (`s ≥ 2`).
-/

namespace GeoSeq

open Finset Polynomial

section Rigid
variable {F : Type*} [Field F] {s : ℕ}

lemma resDig_eq_resAt (a : Fin s → F) (c : Fin s) (n : ℕ) (V : F[X]) :
    resDig a c n V = resAt a (fun _ => n + 1) V c := by
  rw [resDig, resAt, placeCo_const]

lemma resDig_unit (a : Fin s → F) (ha : Function.Injective a) (c : Fin s) (n : ℕ) :
    resDig a c n ((X - C (a c)) ^ n * wCo a c ^ (n + 1)) = 1 := by
  have e := locRes_cancel_unit (a c) (n + 1) ((X - C (a c)) ^ n) (wCo a c ^ (n + 1)) 1
    (by rw [eval_pow]; exact pow_ne_zero _ (wCo_eval_ne a ha c))
  rw [mul_one] at e
  rw [resDig, e, locRes_one, taylor_X_sub_C_pow_coeff, if_pos rfl]

lemma resDig_C_mul (a : Fin s → F) (c : Fin s) (n : ℕ) (r : F) (V : F[X]) :
    resDig a c n (V * C r) = r * resDig a c n V := by
  rw [resDig, resDig, mul_comm, locRes_C_mul]

lemma skelVec_supp (n : ℕ) (u : Fin s → F) : ∀ c k, n < k → skelVec n u c k = 0 := by
  intro c k hk; simp [skelVec, show k ≠ n by omega]

lemma place_skelVec (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (n : ℕ) (u : Fin s → F) (c : Fin s) (V : F[X]) :
    ∑ k ∈ range (n + 1), skelVec n u c k * frDigit a L c k V = u c * frDigit a L c n V := by
  rw [Finset.sum_eq_single n]
  · simp [skelVec]
  · intro k _ hk; simp [skelVec, hk]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

lemma skelVec_ne_zero (n : ℕ) (u : Fin s → F) (hu : u ≠ 0) : skelVec n u ≠ 0 := by
  intro h; apply hu; funext c; have := congrFun (congrFun h c) n; simpa [skelVec] using this

/-- **`lem:rigid`** (an exact skeleton relation fixes the row): if `∑_c v_c y_{c,n}(V) = 0` for every `V` with
`deg V ≤ s(n+1) - 2`, `v ≠ 0`, then every `v_c ≠ 0` and `y_{c,n} = (ξ/v_c) ŷ_{c,n}` for one `ξ ≠ 0`. -/
theorem rigid (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L) (n : ℕ)
    (v : Fin s → F) (hv : v ≠ 0) (hrel : skelVec n v ∈ relSpace a L n (s * (n + 1) - 1)) :
    (∀ c, v c ≠ 0) ∧ ∃ ξ : F, ξ ≠ 0 ∧ ∀ c V, frDigit a L c n V = ξ / v c * resDig a c n V := by
  set A := relPoly a L (skelVec n v) n with hAd
  have hs1 : 1 ≤ s := by
    by_contra h; rw [not_le] at h; apply hv; funext c; exact absurd c.2 (by omega)
  have hdeg := relPoly_degree_lt a ha L _ n _ hrel
  rw [show s * (n + 1) - (s * (n + 1) - 1) = 1 by
    have : 1 ≤ s * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity); omega] at hdeg
  have hAC : A = C (A.coeff 0) := eq_C_of_degree_le_zero (by exact_mod_cast Order.le_of_lt_succ hdeg)
  set ξ := A.coeff 0
  have hξ : ξ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hAC
    exact skelVec_ne_zero n v hv ((relPoly_eq_zero_iff a ha L hL _ n (skelVec_supp n v)).mp hAC)
  have hrow : ∀ c V, v c * frDigit a L c n V = ξ * resDig a c n V := by
    intro c V
    rw [← place_skelVec a L n v c V, place_eq, place_eq_locRes a ha, ← hAd, hAC, ← resDig, resDig_C_mul]
  have hvc : ∀ c, v c ≠ 0 := by
    intro c h0
    have := hrow c ((X - C (a c)) ^ n * wCo a c ^ (n + 1))
    rw [h0, zero_mul, resDig_unit a ha, mul_one] at this
    exact hξ this.symm
  refine ⟨hvc, ξ, hξ, fun c V => ?_⟩
  have := hrow c V
  field_simp [hvc c]
  rw [mul_comm]; exact this

/-- **`cor:residuerows`, converse direction** (one level): if row `n` is the residue row up to nonzero scalars,
`y_{c,n} = μ_c ŷ_{c,n}`, then `∑_c μ_c^{-1} y_{c,n} = 0` on `P_{s(n+1)-1}` (`lem:resform`(c)). -/
theorem rows_skel (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (n : ℕ) (μ : Fin s → F)
    (hμ : ∀ c, μ c ≠ 0) (hrow : ∀ c V, frDigit a L c n V = μ c * resDig a c n V) :
    skelVec n (fun c => (μ c)⁻¹) ∈ relSpace a L n (s * (n + 1) - 1) := by
  refine ⟨skelVec_supp n _, fun V hV => ?_⟩
  rw [relForm]
  have : ∀ c, ∑ k ∈ range (n + 1), skelVec n (fun c => (μ c)⁻¹) c k * frDigit a L c k V =
      resAt a (fun _ => n + 1) V c := by
    intro c
    rw [place_skelVec, hrow, ← mul_assoc, inv_mul_cancel₀ (hμ c), one_mul, resDig_eq_resAt]
  rw [Finset.sum_congr rfl fun c _ => this c]
  refine res_thm_zero a ha _ V ?_
  have hs : (∑ c : Fin s, (fun _ => n + 1) c) = s * (n + 1) := by simp [Finset.sum_const]
  rw [hs]; omega

/-- **`cor:residuerows`** (first part, at one level `n`, `s ≥ 1`): `P_{s(n+1)-1}` satisfies a skeleton relation
`∑_c u_c y_{c,n} = 0` with some `u ≠ 0` iff there are `μ_c ≠ 0` with `y_{c,n} = μ_c ŷ_{c,n}` for all `c`. -/
theorem residuerows (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (n : ℕ) :
    (∃ u : Fin s → F, u ≠ 0 ∧ skelVec n u ∈ relSpace a L n (s * (n + 1) - 1)) ↔
      ∃ μ : Fin s → F, (∀ c, μ c ≠ 0) ∧ ∀ c V, frDigit a L c n V = μ c * resDig a c n V := by
  constructor
  · rintro ⟨u, hu, hrel⟩
    obtain ⟨hu0, ξ, hξ, hrow⟩ := rigid a ha L hL n u hu hrel
    exact ⟨fun c => ξ / u c, fun c => div_ne_zero hξ (hu0 c), hrow⟩
  · rintro ⟨μ, hμ, hrow⟩
    refine ⟨fun c => (μ c)⁻¹, fun h => ?_, rows_skel a ha L n μ hμ hrow⟩
    have := congrFun h ⟨0, hs⟩
    exact inv_ne_zero (hμ ⟨0, hs⟩) this

/-- `cor:residuerows`: then the check vector of the skeleton relation is proportional to `(1/μ_c)_c`. -/
theorem residuerows_prop (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (n : ℕ) (u μ : Fin s → F) (hu : u ≠ 0) (hrel : skelVec n u ∈ relSpace a L n (s * (n + 1) - 1))
    (hrow : ∀ c V, frDigit a L c n V = μ c * resDig a c n V) :
    ∃ r : F, r ≠ 0 ∧ ∀ c, u c = r * (μ c)⁻¹ := by
  obtain ⟨hu0, ξ, hξ, hrow'⟩ := rigid a ha L hL n u hu hrel
  have hs1 : 1 ≤ s := by
    by_contra h; rw [not_le] at h; apply hu; funext c; exact absurd c.2 (by omega)
  refine ⟨ξ, hξ, fun c => ?_⟩
  have h1 := hrow c ((X - C (a c)) ^ n * wCo a c ^ (n + 1))
  rw [hrow' c, resDig_unit a ha, mul_one, mul_one] at h1
  rw [← h1]; field_simp [hu0 c]

/-- **`cor:nodesign`** (no designed relation next to skeleton relations). Let `K ≥ max(s-1, sJ)` and suppose the
skeleton relations `∑_c u_{c,n} y_{c,n} = 0` on `P_{s(n+1)-1}` hold at the `J+1` levels `n = K-J, …, K`. Then every
exact digit relation of top index `K` and depth at most `J` on `P_{sK}` is a multiple of `∑_c u_{c,K} y_{c,K} = 0`. -/
theorem nodesign (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (K J : ℕ) (hK1 : s - 1 ≤ K) (hKJ : s * J ≤ K) (u : ℕ → Fin s → F)
    (hu : ∀ n, K - J ≤ n → n ≤ K → u n ≠ 0 ∧ skelVec n (u n) ∈ relSpace a L n (s * (n + 1) - 1))
    (f : Fin s → ℕ → F) (hf : f ∈ relSpace a L K (s * K)) (hdep : ∀ c, DepthAt K J c f) :
    ∃ ν : F, f = ν • skelVec K (u K) := by
  classical
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; refine absurd ?_ (hu K (Nat.sub_le _ _) le_rfl).1; funext c; exact c.elim0
    · exact h
  have hJK : J ≤ K := le_trans (Nat.le_mul_of_pos_left J hs1) hKJ
  have hr : ∀ n, K - J ≤ n → n ≤ K → (∀ c, u n c ≠ 0) ∧
      ∃ ξ : F, ξ ≠ 0 ∧ ∀ c V, frDigit a L c n V = ξ / u n c * resDig a c n V :=
    fun n h1 h2 => rigid a ha L hL n (u n) (hu n h1 h2).1 (hu n h1 h2).2
  choose! ξ hξ hrow using fun n (h : K - J ≤ n ∧ n ≤ K) => (hr n h.1 h.2).2
  have hu0 : ∀ n, K - J ≤ n → n ≤ K → ∀ c, u n c ≠ 0 := fun n h1 h2 => (hr n h1 h2).1
  set A := relPoly a L f K with hAd
  have hdegA : A.degree < (s : WithBot ℕ) := by
    have := relPoly_degree_lt a ha L f K (s * K) hf
    rwa [show s * (K + 1) - s * K = s by rw [Nat.mul_succ]; omega] at this
  have hnatA : A.natDegree ≤ s - 1 := by
    rcases eq_or_ne A 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · rw [degree_eq_natDegree h0] at hdegA
      have : A.natDegree < s := by exact_mod_cast hdegA
      omega
  -- at each place: `A = ∑_{j ≤ J} b_j w^{J-j}` with `b_j = f_{c,K-J+j} ξ_{K-J+j} / u_{K-J+j,c}`
  have hplace : ∀ c, A = C (f c K * ξ K / u K c) ∧ ∀ n, K - J ≤ n → n < K → f c n = 0 := by
    intro c
    set b : ℕ → F := fun j => f c (K - J + j) * ξ (K - J + j) / u (K - J + j) c with hb
    set P : F[X] := ∑ j ∈ range (J + 1), C (b j) * wPoly a ^ (J - j) with hP
    have hres : ∀ V : F[X], locRes (a c) (K + 1) (V * (A - P)) (wCo a c ^ (K + 1)) = 0 := by
      intro V
      have h1 : ∑ k ∈ range (K + 1), f c k * frDigit a L c k V =
          locRes (a c) (K + 1) (V * A) (wCo a c ^ (K + 1)) := by
        rw [place_eq, place_eq_locRes a ha]
      have h2 : ∑ k ∈ range (K + 1), f c k * frDigit a L c k V =
          locRes (a c) (K + 1) (V * P) (wCo a c ^ (K + 1)) := by
        rw [← Finset.sum_range_add_sum_Ico _ (show K - J ≤ K + 1 by omega)]
        rw [Finset.sum_eq_zero (s := range (K - J)) fun k hk => by
          rw [hdep c k (by simp at hk; omega), zero_mul], zero_add, Finset.sum_Ico_eq_sum_range,
          show K + 1 - (K - J) = J + 1 by omega, hP, Finset.mul_sum, locRes_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [show V * (C (b j) * wPoly a ^ (J - j)) = C (b j) * (V * wPoly a ^ (J - j)) by ring, locRes_C_mul,
          show K + 1 = (K - J + j + 1) + (J - j) by omega, resAt_level a ha c, ← resDig,
          hrow (K - J + j) ⟨by omega, by omega⟩ c V, hb]
        field_simp
      rw [mul_sub, show V * A - V * P = V * A + (-1 : F) • (V * P) by simp [sub_eq_add_neg],
        show (-1 : F) • (V * P) = C (-1) * (V * P) by rw [smul_eq_C_mul], locRes_add, locRes_C_mul, ← h1, ← h2]
      ring
    have hdvd := dvd_of_locRes (a c) K (A - P) (wCo a c ^ (K + 1))
      (by rw [eval_pow]; exact pow_ne_zero _ (wCo_eval_ne a ha c)) hres
    have hPdeg : P.natDegree ≤ s * J := by
      refine natDegree_sum_le_of_forall_le _ _ fun j hj => (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_pow, natDegree_wPoly]
      have : (J - j) * s ≤ s * J := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      exact this
    have hAP : A - P = 0 := eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (by omega))
    -- `w`-adic uniqueness
    let D : ℕ → F[X] := fun i => C (b (J - i)) - if i = 0 then A else 0
    have hD : ∑ i ∈ range (J + 1), D i * wPoly a ^ i = 0 := by
      have e1 : ∑ i ∈ range (J + 1), D i * wPoly a ^ i =
          ∑ i ∈ range (J + 1), C (b (J - i)) * wPoly a ^ i - A := by
        simp only [D, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
          Finset.mem_range, show 0 < J + 1 by omega, if_true, pow_zero, mul_one]
      have e2 : ∑ i ∈ range (J + 1), C (b (J - i)) * wPoly a ^ i = P := by
        rw [hP, ← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun j hj => ?_
        have := Finset.mem_range.mp hj
        rw [show J + 1 - 1 - j = J - j by omega, show J - (J - j) = j by omega]
      rw [e1, e2, ← neg_sub, sub_eq_zero.mp hAP, sub_self, neg_zero]
    have hDz := wadic_unique (wPoly a) (wPoly_monic a).ne_zero (J + 1) D (fun i hi => by
      rw [degree_eq_natDegree (wPoly_monic a).ne_zero, natDegree_wPoly]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ((degree_C_le).trans_lt ?_) ?_)
      · exact_mod_cast hs1
      · split_ifs
        · exact hdegA
        · rw [degree_zero]; exact WithBot.bot_lt_coe _) hD
    refine ⟨?_, fun n h1 h2 => ?_⟩
    · have := hDz 0 (by omega)
      simp only [D, Nat.sub_zero, sub_eq_zero, if_true, ↓reduceIte] at this
      rw [← this, hb]; simp only [show K - J + J = K by omega]
    · have := hDz (K - n) (by omega)
      simp only [D, if_neg (show K - n ≠ 0 by omega), sub_zero, C_eq_zero, hb,
        show K - J + (J - (K - n)) = n by omega] at this
      rcases mul_eq_zero.mp (div_eq_zero_iff.mp this |>.resolve_right (hu0 n h1 h2.le c)) with h | h
      · exact h
      · exact absurd h (hξ n ⟨h1, h2.le⟩)
  -- assemble
  obtain ⟨c0, _⟩ : ∃ c0 : Fin s, True := ⟨⟨0, hs1⟩, trivial⟩
  refine ⟨A.coeff 0 / ξ K, ?_⟩
  funext c k
  simp only [Pi.smul_apply, smul_eq_mul, skelVec]
  split_ifs with hk
  · subst hk
    have h := (hplace c).1
    have hc : A.coeff 0 = f c k * ξ k / u k c := by rw [h, coeff_C_zero]
    rw [hc]; field_simp [hξ k ⟨by omega, le_rfl⟩, hu0 k (by omega) le_rfl c]
  · rw [mul_zero]
    rcases Nat.lt_or_ge K k with h1 | h1
    · exact hf.1 c k h1
    · rcases Nat.lt_or_ge k (K - J) with h2 | h2
      · exact hdep c k (by omega)
      · exact (hplace c).2 k h2 (by omega)

/-- `cor:nodesign`, "in particular": the full level `P_{sK}` has no designed geometric digit of depth at most `J`
(`s ≥ 2`). -/
theorem nodesign_no_design (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 2 ≤ s) (K J : ℕ) (hK1 : s - 1 ≤ K) (hKJ : s * J ≤ K) (u : ℕ → Fin s → F)
    (hu : ∀ n, K - J ≤ n → n ≤ K → u n ≠ 0 ∧ skelVec n (u n) ∈ relSpace a L n (s * (n + 1) - 1))
    (i : Fin s) (f : Fin s → ℕ → F) : ¬ IsDesign a L J K i f := by
  rintro ⟨hf, hfi, hfc, hdep⟩
  obtain ⟨ν, hν⟩ := nodesign a ha L hL K J hK1 hKJ u hu f hf hdep
  obtain ⟨c, hc⟩ : ∃ c : Fin s, c ≠ i := by
    by_cases h : (i : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
  have hu0 := (rigid a ha L hL K (u K) (hu K (Nat.sub_le _ _) le_rfl).1 (hu K (Nat.sub_le _ _) le_rfl).2).1
  have h1 := hfc c hc
  rw [hν] at h1 hfi
  simp only [Pi.smul_apply, smul_eq_mul, skelVec] at h1 hfi
  have hν0 : ν = 0 := (mul_eq_zero.mp h1).resolve_right (hu0 c)
  rw [hν0, zero_mul] at hfi
  exact zero_ne_one hfi

end Rigid

end GeoSeq
