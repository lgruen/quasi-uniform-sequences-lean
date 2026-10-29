/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4Defs
public import GeoSeq.V99Gen
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section

/-!
# GeoSeq stage V10-4 (part 1): the design multipliers of `def:block`(a) from reachability, every `s`

Over any field, for distinct places, nonzero row constants and a reachable design (`IsReachable`):

* `designNum_exists`: identity (a) of `def:block` has a solution (numerators `N_n`, `n ≤ s-2`, of degree `≤ s-2`);
  explicitly `N_n = ∑_{j ≠ c} x_{n,j} wCoCo a c j`, where `∑_n x_{n,j} γ_{c,n} = -τ_{jc}⁻¹ ℓ_j` (`ℓ_j` the Lagrange basis
  polynomial at the nodes `τ_{ic}`) — the triangular change of basis of the proof of `thm:block`(i);
* `designNum_unique`: the solution is unique;
* `designNum_order`: every solution has the vanishing orders of `def:block`(a): `N_n = (z - a_c)^n N'` with
  `N'(a_c) ≠ 0` (the power-series argument of the proof of `thm:block`(i): the Taylor coefficients `θ_{n,k}` of
  `N_n / w_c` at `a_c` satisfy `X^k = ∑_n θ_{n,k} γ_{c,n}` for `k ≤ s - 2`).
-/

namespace GeoSeq

open Finset Polynomial

section Tri
variable {F : Type*} [Field F]

/-- A triangular family (`natDegree γ_n = n`, `γ_n ≠ 0` for `n ≤ M`): if `∑_{n ≤ m} x_n γ_n` has degree `≤ k`, then
`x_n = 0` for `k < n ≤ m`. -/
theorem triF_zero_above (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) (k : ℕ) :
    ∀ m, m ≤ M → ∀ x : ℕ → F, (∑ n ∈ range (m + 1), C (x n) * γ n).natDegree ≤ k →
      ∀ n, k < n → n ≤ m → x n = 0 := by
  intro m
  induction m with
  | zero => intro _ x _ n hkn hn; omega
  | succ m ih =>
    intro hm x hdeg n hkn hn
    by_cases hmk : m + 1 ≤ k
    · omega
    have hx : x (m + 1) = 0 := by
      have h0 : (∑ n ∈ range (m + 1 + 1), C (x n) * γ n).coeff (m + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [finset_sum_coeff, sum_range_succ] at h0
      have hlow : ∑ n ∈ range (m + 1), (C (x n) * γ n).coeff (m + 1) = 0 := by
        refine sum_eq_zero fun n hn => ?_
        rw [mem_range] at hn
        rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [(hγ n (by omega)).1]; omega), mul_zero]
      rw [hlow, zero_add, coeff_C_mul] at h0
      have hlc : (γ (m + 1)).coeff (m + 1) ≠ 0 := by
        have h2 := hγ (m + 1) hm
        have h3 : (γ (m + 1)).coeff (m + 1) = (γ (m + 1)).leadingCoeff := by rw [leadingCoeff, h2.1]
        rw [h3]; exact leadingCoeff_ne_zero.mpr h2.2
      exact (mul_eq_zero.mp h0).resolve_right hlc
    by_cases hnm : n = m + 1
    · rw [hnm]; exact hx
    · have hsum : ∑ n ∈ range (m + 1 + 1), C (x n) * γ n = ∑ n ∈ range (m + 1), C (x n) * γ n := by
        rw [sum_range_succ, hx, C_0, zero_mul, add_zero]
      rw [hsum] at hdeg
      exact ih (by omega) x hdeg n hkn (by omega)

/-- The coefficient `k` of `∑_{n ≤ m} x_n γ_n` when that sum has degree `≤ k ≤ m`: `x_k · lc(γ_k)`. -/
theorem triF_coeff (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) (k m : ℕ)
    (hm : m ≤ M) (hkm : k ≤ m) (x : ℕ → F) (hdeg : (∑ n ∈ range (m + 1), C (x n) * γ n).natDegree ≤ k) :
    (∑ n ∈ range (m + 1), C (x n) * γ n).coeff k = x k * (γ k).leadingCoeff := by
  have hz := triF_zero_above γ M hγ k m hm x hdeg
  rw [finset_sum_coeff, ← sum_range_add_sum_Ico _ (show k + 1 ≤ m + 1 by omega)]
  have hhi : ∑ n ∈ Ico (k + 1) (m + 1), (C (x n) * γ n).coeff k = 0 := by
    refine sum_eq_zero fun n hn => ?_
    rw [mem_Ico] at hn
    rw [hz n (by omega) (by omega), C_0, zero_mul, coeff_zero]
  rw [hhi, add_zero, sum_range_succ]
  have hlo : ∑ n ∈ range k, (C (x n) * γ n).coeff k = 0 := by
    refine sum_eq_zero fun n hn => ?_
    rw [mem_range] at hn
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [(hγ n (by omega)).1]; omega), mul_zero]
  rw [hlo, zero_add, coeff_C_mul, leadingCoeff, (hγ k (by omega)).1]

/-- Linear independence of a triangular family. -/
theorem triF_unique (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) (m : ℕ)
    (hm : m ≤ M) (x : ℕ → F) (h0 : ∑ n ∈ range (m + 1), C (x n) * γ n = 0) : ∀ n, n ≤ m → x n = 0 := by
  have hdeg : (∑ n ∈ range (m + 1), C (x n) * γ n).natDegree ≤ 0 := by rw [h0, natDegree_zero]
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hc := triF_coeff γ M hγ 0 m hm (Nat.zero_le _) x hdeg
    rw [h0, coeff_zero] at hc
    have hlc : (γ 0).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hγ 0 (Nat.zero_le _)).2
    exact ((mul_eq_zero.mp hc.symm).resolve_right hlc)
  · exact triF_zero_above γ M hγ 0 m hm x hdeg n hpos hn

/-- Expansion in a triangular family: every polynomial of degree `≤ m` is `∑_{n ≤ m} x_n γ_n`. -/
theorem triF_expand (γ : ℕ → F[X]) (M : ℕ) (hγ : ∀ n, n ≤ M → (γ n).natDegree = n ∧ γ n ≠ 0) :
    ∀ m, m ≤ M → ∀ h : F[X], h.natDegree ≤ m → ∃ x : ℕ → F, h = ∑ n ∈ range (m + 1), C (x n) * γ n := by
  intro m
  induction m with
  | zero =>
    intro hm h hh
    have hγ0 := hγ 0 (Nat.zero_le _)
    set g0 := (γ 0).coeff 0 with hg0def
    have hg : γ 0 = C g0 := eq_C_of_natDegree_le_zero hγ0.1.le
    have hg0 : g0 ≠ 0 := by
      intro h0; rw [h0, C_0] at hg; exact hγ0.2 hg
    refine ⟨fun _ => h.coeff 0 / g0, ?_⟩
    rw [zero_add, sum_range_one, hg, ← C_mul, div_mul_cancel₀ _ hg0]
    exact eq_C_of_natDegree_le_zero hh
  | succ m ih =>
    intro hm h hh
    have hγm := hγ (m + 1) hm
    have hlc : (γ (m + 1)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hγm.2
    set t := h.coeff (m + 1) / (γ (m + 1)).leadingCoeff with ht
    have hh' : (h - C t * γ (m + 1)).natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul]
      by_cases hNm : N = m + 1
      · subst hNm
        have hcm : (γ (m + 1)).coeff (m + 1) = (γ (m + 1)).leadingCoeff := by rw [leadingCoeff, hγm.1]
        rw [hcm, ht, div_mul_cancel₀ _ hlc, sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by rw [hγm.1]; omega)]
        ring
    obtain ⟨x', hx'⟩ := ih (by omega) _ hh'
    refine ⟨fun n => if n = m + 1 then t else x' n, ?_⟩
    rw [sum_range_succ]
    simp only [↓reduceIte]
    have : ∑ n ∈ range (m + 1), C (if n = m + 1 then t else x' n) * γ n =
        ∑ n ∈ range (m + 1), C (x' n) * γ n := by
      refine sum_congr rfl fun n hn => ?_
      rw [mem_range] at hn
      rw [if_neg (by omega)]
    rw [this, ← hx']
    ring

end Tri

section Num
variable {F : Type*} [Field F] {s : ℕ}

lemma tauF_ne (a : Fin s → F) (ha : Function.Injective a) {i c : Fin s} (h : i ≠ c) : tauF a i c ≠ 0 :=
  inv_ne_zero (sub_ne_zero.mpr fun he => h (ha he))

lemma tauF_injOn (a : Fin s → F) (ha : Function.Injective a) (c : Fin s) :
    Set.InjOn (fun i => tauF a i c) ↑(univ.erase c) := by
  intro i _ j _ h
  simp only [tauF, inv_inj, sub_left_inj] at h
  exact ha h

lemma tauF_mul (a : Fin s → F) (ha : Function.Injective a) {i c : Fin s} (h : i ≠ c) :
    tauF a i c * (a i - a c) = 1 :=
  inv_mul_cancel₀ (sub_ne_zero.mpr fun he => h (ha he))

/-- A polynomial of degree `≤ s - 2` vanishing at the `s - 1` nodes `τ_{ic}`, `i ≠ c`, is zero. -/
theorem poly_zero_of_nodes (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (c : Fin s) (P : F[X])
    (hdeg : P.natDegree ≤ s - 2) (hev : ∀ i, i ≠ c → P.eval (tauF a i c) = 0) : P = 0 := by
  classical
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P ((univ.erase c).image fun i => tauF a i c)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    exact hev i (ne_of_mem_erase hi)
  · rw [card_image_of_injOn (tauF_injOn a ha c), card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    omega

lemma natDegree_wCoCo_le (a : Fin s → F) {c j : Fin s} (hj : j ≠ c) : (wCoCo a c j).natDegree ≤ s - 2 := by
  classical
  unfold wCoCo
  refine (natDegree_prod_le _ _).trans ?_
  have : ∀ i' ∈ (univ.erase c).erase j, (X - C (a i')).natDegree ≤ 1 := fun i' _ =>
    (natDegree_X_sub_C (a i')).le
  refine (sum_le_sum this).trans ?_
  rw [sum_const, smul_eq_mul, mul_one, card_erase_of_mem (mem_erase.mpr ⟨hj, mem_univ j⟩),
    card_erase_of_mem (mem_univ c), card_univ, Fintype.card_fin]
  omega

/-- The reachability data of the column `c` as a triangular family (`n ≤ s - 2`). -/
lemma reach_tri {a : Fin s → F} {v : Fin s → F} {Fd : ℕ → Fin s → Fin s → F} {γ : Fin s → ℕ → F[X]}
    (hs : 2 ≤ s) (hR : IsReachable a v Fd γ) (c : Fin s) :
    ∀ n, n ≤ s - 2 → (γ c n).natDegree = n ∧ γ c n ≠ 0 :=
  fun n hn => hR.1 c n (by omega)

/-- In identity (a) the design entries are `v_i⁻¹ τ γ(τ)`: `v_i ∑_n F_n[i][c] N_n = τ_{ic} ∑_n γ_{c,n}(τ_{ic}) N_n`. -/
lemma idA_sum {a : Fin s → F} {v : Fin s → F} {Fd : ℕ → Fin s → Fin s → F} {γ : Fin s → ℕ → F[X]}
    (hv : ∀ c, v c ≠ 0) (hR : IsReachable a v Fd γ) {c i : Fin s} (hic : i ≠ c) (N : ℕ → F[X]) :
    C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * N n =
      C (tauF a i c) * ∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * N n := by
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [hR.2 c i hic n (by omega), ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul]
  congr 2
  field_simp [hv i]

/-- **`def:block`(a), existence** (proof of `thm:block`(i)): for distinct places, nonzero row constants and a
reachable design, identity (a) has a solution `N_0, …, N_{s-2}` for every column, of degree `≤ s - 2`. -/
theorem designNum_exists (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ)
    (c : Fin s) : ∃ N : ℕ → F[X], IdA a v Fd c N ∧ ∀ n, (N n).natDegree ≤ s - 2 := by
  classical
  set T : Fin s → F := fun i => tauF a i c with hT
  have hTinj := tauF_injOn a ha c
  -- the target polynomials `h_j = -τ_j⁻¹ ℓ_j` and their expansions in the triangular family `γ_{c,·}`
  set hp : Fin s → F[X] := fun j => C (-(T j)⁻¹) * Lagrange.basis (univ.erase c) T j with hhp
  have hpdeg : ∀ j, j ≠ c → (hp j).natDegree ≤ s - 2 := by
    intro j hj
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Lagrange.natDegree_basis hTinj (mem_erase.mpr ⟨hj, mem_univ j⟩), card_erase_of_mem (mem_univ c),
      card_univ, Fintype.card_fin]
    omega
  have hexp : ∀ j, ∃ x : ℕ → F, j ≠ c → hp j = ∑ n ∈ range (s - 2 + 1), C (x n) * γ c n := by
    intro j
    by_cases hj : j = c
    · exact ⟨fun _ => 0, fun h => absurd hj h⟩
    · obtain ⟨x, hx⟩ := triF_expand (γ c) (s - 2) (reach_tri hs hR c) (s - 2) le_rfl (hp j) (hpdeg j hj)
      exact ⟨x, fun _ => hx⟩
  choose x hx using hexp
  have hr : s - 2 + 1 = s - 1 := by omega
  refine ⟨fun n => ∑ j ∈ univ.erase c, C (x j n) * wCoCo a c j, fun i hic => ?_, fun n => ?_⟩
  · have hsum := idA_sum hv hR hic (fun n => ∑ j ∈ univ.erase c, C (x j n) * wCoCo a c j)
    have hval : ∀ j ∈ univ.erase c, ∑ n ∈ range (s - 1), (γ c n).eval (T i) * x j n =
        (hp j).eval (T i) := by
      intro j hj
      rw [hx j (ne_of_mem_erase hj), ← hr, eval_finsetSum]
      refine sum_congr rfl fun n _ => ?_
      rw [eval_mul, eval_C]; ring
    have hswap : ∑ n ∈ range (s - 1), C ((γ c n).eval (T i)) * ∑ j ∈ univ.erase c, C (x j n) * wCoCo a c j =
        ∑ j ∈ univ.erase c, C ((hp j).eval (T i)) * wCoCo a c j := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j hj => ?_
      rw [← hval j hj, map_sum, sum_mul]
      refine sum_congr rfl fun n _ => ?_
      rw [C_mul]; ring
    have hdelta : ∀ j ∈ univ.erase c, C ((hp j).eval (T i)) * wCoCo a c j =
        if j = i then C (-(T i)⁻¹) * wCoCo a c i else 0 := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, hhp]
        simp only [eval_mul, eval_C]
        rw [Lagrange.eval_basis_self hTinj (mem_erase.mpr ⟨hic, mem_univ _⟩), mul_one]
      · rw [if_neg hji, hhp]
        simp only [eval_mul, eval_C]
        rw [Lagrange.eval_basis_of_ne hji (mem_erase.mpr ⟨hic, mem_univ _⟩), mul_zero, C_0, zero_mul]
    rw [hswap, sum_congr rfl hdelta, sum_ite_eq' (univ.erase c) i, if_pos (mem_erase.mpr ⟨hic, mem_univ _⟩)]
      at hsum
    have hTi : T i ≠ 0 := tauF_ne a ha hic
    have hv' : (C (v i) : F[X]) ≠ 0 := C_ne_zero.mpr (hv i)
    have key : C (v i) * (-C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) *
        ∑ j ∈ univ.erase c, C (x j n) * wCoCo a c j) = C (v i) * wCoCo a c i := by
      have e3 : C (v i) * (-C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) *
          ∑ j ∈ univ.erase c, C (x j n) * wCoCo a c j) = -C (v i) * (C (v i) * ∑ n ∈ range (s - 1),
            C (Fd n i c) * ∑ j ∈ univ.erase c, C (x j n) * wCoCo a c j) := by ring
      rw [e3, hsum, ← mul_assoc (C (T i)), ← C_mul, show T i * -(T i)⁻¹ = -1 by field_simp]
      simp
    exact (mul_left_cancel₀ hv' key).symm
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (natDegree_C_mul_le _ _).trans (natDegree_wCoCo_le a (ne_of_mem_erase hj))

/-- **`def:block`(a), uniqueness**: two solutions of identity (a) for the column `c` agree at every depth
`n ≤ s - 2`. -/
theorem designNum_unique (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ)
    (c : Fin s) (N N' : ℕ → F[X]) (hN : IdA a v Fd c N) (hN' : IdA a v Fd c N') :
    ∀ n, n + 2 ≤ s → N n = N' n := by
  have hr : s - 2 + 1 = s - 1 := by omega
  -- for every node: `∑_n γ_{c,n}(τ_i) (N_n - N'_n) = 0`
  have hnode : ∀ i, i ≠ c → ∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * (N n - N' n) = 0 := by
    intro i hic
    have h1 := hN i hic
    have h2 := hN' i hic
    have e1 := idA_sum hv hR hic N
    have e2 := idA_sum hv hR hic N'
    have hd : C (tauF a i c) * (∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * N n -
        ∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * N' n) = 0 := by
      rw [mul_sub, ← e1, ← e2]
      linear_combination h1 - h2
    rw [mul_eq_zero] at hd
    rcases hd with hd | hd
    · exact absurd (C_eq_zero.mp hd) (tauF_ne a ha hic)
    · rw [← hd, ← sum_sub_distrib]
      refine sum_congr rfl fun n _ => ?_
      ring
  -- coefficientwise: a polynomial of degree `≤ s-2` in `τ` vanishing at the `s - 1` nodes
  have hcoef : ∀ k, ∀ n, n ≤ s - 2 → (N n - N' n).coeff k = 0 := by
    intro k
    have hQ : ∑ n ∈ range (s - 2 + 1), C ((N n - N' n).coeff k) * γ c n = 0 := by
      apply poly_zero_of_nodes hs a ha c
      · refine natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
        rw [mem_range] at hn
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [(hR.1 c n (by omega)).1]; omega
      · intro i hic
        have := congrArg (fun P => P.coeff k) (hnode i hic)
        simp only [finset_sum_coeff, coeff_C_mul, coeff_zero] at this
        rw [eval_finsetSum, hr, ← this]
        refine sum_congr rfl fun n _ => ?_
        rw [eval_mul, eval_C]; ring
    exact triF_unique (γ c) (s - 2) (reach_tri hs hR c) (s - 2) le_rfl _ hQ
  intro n hn
  rw [← sub_eq_zero]
  ext k
  rw [coeff_zero]
  exact hcoef k n (by omega)

/-- The polynomial identity behind the orders of vanishing: after the Taylor shift to `a_c`, identity (a) at the
node `τ = τ_{ic}` reads `T(w_c) = (1 - τX) ∑_n γ_{c,n}(τ) T(N_n)` (`T = taylor a_c`). -/
lemma idA_taylor {a : Fin s → F} (ha : Function.Injective a) {v : Fin s → F} (hv : ∀ c, v c ≠ 0)
    {Fd : ℕ → Fin s → Fin s → F} {γ : Fin s → ℕ → F[X]} (hR : IsReachable a v Fd γ) {c : Fin s} {N : ℕ → F[X]}
    (hN : IdA a v Fd c N) {i : Fin s} (hic : i ≠ c) :
    taylor (a c) (wCo a c) = (1 - C (tauF a i c) * X) *
      ∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * taylor (a c) (N n) := by
  have h1 := hN i hic
  have e1 := idA_sum hv hR hic N
  have hw : wCo a c = (X - C (a i)) *
      -(C (tauF a i c) * ∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * N n) := by
    rw [wCo_eq a hic, h1, neg_mul, e1]
  rw [hw, taylor_mul, map_neg, taylor_mul, taylor_C, map_sub, taylor_X, taylor_C, map_sum]
  simp_rw [taylor_mul, taylor_C]
  have h2 : C (tauF a i c) * (C (a i) - C (a c)) = 1 := by
    rw [← C_sub, ← C_mul, tauF_mul a ha hic, C_1]
  linear_combination (∑ n ∈ range (s - 1), C ((γ c n).eval (tauF a i c)) * taylor (a c) (N n)) * h2

/-- **`def:block`(a), orders of vanishing** (proof of `thm:block`(i)): every solution of identity (a) for the column
`c` of a reachable design has `N_n = (z - a_c)^n N'` with `N'(a_c) ≠ 0`, `n ≤ s - 2`. -/
theorem designNum_order (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ)
    (c : Fin s) (N : ℕ → F[X]) (hN : IdA a v Fd c N) :
    ∀ n, n + 2 ≤ s → ∃ N', N n = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0 := by
  have hr : s - 2 + 1 = s - 1 := by omega
  set ψ : F[X] →+* PowerSeries F := Polynomial.coeToPowerSeries.ringHom with hψ
  have hψC : ∀ t : F, ψ (C t) = PowerSeries.C t := fun t => by
    rw [hψ, coeToPowerSeries.ringHom_apply, coe_C]
  have hψX : ψ X = PowerSeries.X := by rw [hψ, coeToPowerSeries.ringHom_apply, coe_X]
  have hψc : ∀ (P : F[X]) k, PowerSeries.coeff k (ψ P) = P.coeff k := fun P k => by
    rw [hψ, coeToPowerSeries.ringHom_apply, coeff_coe]
  set W : PowerSeries F := ψ (taylor (a c) (wCo a c)) with hW
  have hW0 : PowerSeries.constantCoeff W ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hW, hψc, taylor_coeff_zero]
    exact wCo_eval_ne a ha c
  set θ : ℕ → ℕ → F := fun n k => PowerSeries.coeff k (ψ (taylor (a c) (N n)) * W⁻¹) with hθdef
  -- the geometric identity at every node
  have hgeo : ∀ i, i ≠ c → ∀ k, ∑ n ∈ range (s - 1), (γ c n).eval (tauF a i c) * θ n k = tauF a i c ^ k := by
    intro i hic
    set τ := tauF a i c
    set G : PowerSeries F := ∑ n ∈ range (s - 1), PowerSeries.C ((γ c n).eval τ) *
      (ψ (taylor (a c) (N n)) * W⁻¹) with hG
    have hG1 : (1 - PowerSeries.C τ * PowerSeries.X) * G = 1 := by
      have h := congrArg ψ (idA_taylor ha hv hR hN hic)
      rw [← hW] at h
      simp only [map_mul, map_sub, map_one, map_sum, hψC, hψX] at h
      calc (1 - PowerSeries.C τ * PowerSeries.X) * G =
            ((1 - PowerSeries.C τ * PowerSeries.X) * ∑ n ∈ range (s - 1),
              PowerSeries.C ((γ c n).eval τ) * ψ (taylor (a c) (N n))) * W⁻¹ := by
            rw [hG, mul_sum, mul_sum, sum_mul]
            exact sum_congr rfl fun n _ => by ring
        _ = W * W⁻¹ := by rw [← h]
        _ = 1 := PowerSeries.mul_inv_cancel W hW0
    have hcG : ∀ k, PowerSeries.coeff k G = ∑ n ∈ range (s - 1), (γ c n).eval τ * θ n k := by
      intro k
      rw [hG, map_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [PowerSeries.coeff_C_mul]
    intro k
    rw [← hcG]
    have hsplit : ∀ j, PowerSeries.coeff j ((1 - PowerSeries.C τ * PowerSeries.X) * G) =
        PowerSeries.coeff j G - τ * PowerSeries.coeff j (PowerSeries.X * G) := by
      intro j
      rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
    induction k with
    | zero =>
      have := hsplit 0
      rw [hG1, PowerSeries.coeff_zero_X_mul, mul_zero, sub_zero, PowerSeries.coeff_one, if_pos rfl] at this
      rw [pow_zero, ← this]
    | succ k ih =>
      have := hsplit (k + 1)
      rw [hG1, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k), ih] at this
      rw [pow_succ]
      linear_combination -this
  -- the triangular identities `X^k = ∑_n θ_{n,k} γ_{c,n}` for `k ≤ s - 2`
  have hXk : ∀ k, k ≤ s - 2 → ∑ n ∈ range (s - 2 + 1), C (θ n k) * γ c n = X ^ k := by
    intro k hk
    rw [← sub_eq_zero]
    apply poly_zero_of_nodes hs a ha c
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
        rw [mem_range] at hn
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [(hR.1 c n (by omega)).1]; omega
      · rw [natDegree_X_pow]; exact hk
    · intro i hic
      rw [eval_sub, eval_finsetSum, eval_pow, eval_X, hr, ← hgeo i hic k, sub_eq_zero]
      refine sum_congr rfl fun n _ => ?_
      rw [eval_mul, eval_C]; ring
  have hθz : ∀ k n, k < n → n ≤ s - 2 → θ n k = 0 := by
    intro k n hkn hn
    have hk : k ≤ s - 2 := by omega
    exact triF_zero_above (γ c) (s - 2) (reach_tri hs hR c) k (s - 2) le_rfl (fun n => θ n k)
      (by rw [hXk k hk, natDegree_X_pow]) n hkn hn
  have hθd : ∀ k, k ≤ s - 2 → θ k k ≠ 0 := by
    intro k hk h0
    have := triF_coeff (γ c) (s - 2) (reach_tri hs hR c) k (s - 2) le_rfl hk (fun n => θ n k)
      (by rw [hXk k hk, natDegree_X_pow])
    rw [hXk k hk, coeff_X_pow_self] at this
    rw [h0, zero_mul] at this
    exact one_ne_zero this
  -- the Taylor coefficients of `N_n` at `a_c`
  intro n hn
  have hTN : ∀ j, (taylor (a c) (N n)).coeff j =
      ∑ q ∈ antidiagonal j, θ n q.1 * PowerSeries.coeff q.2 W := by
    intro j
    rw [← hψc, show ψ (taylor (a c) (N n)) = (ψ (taylor (a c) (N n)) * W⁻¹) * W by
      rw [mul_assoc, PowerSeries.inv_mul_cancel W hW0, mul_one], PowerSeries.coeff_mul]
  have hlow : ∀ j, j < n → (taylor (a c) (N n)).coeff j = 0 := by
    intro j hj
    rw [hTN]
    refine sum_eq_zero fun q hq => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    rw [hθz q.1 n (by omega) (by omega), zero_mul]
  have htop : (taylor (a c) (N n)).coeff n = θ n n * PowerSeries.coeff 0 W := by
    rw [hTN, sum_eq_single (n, 0)]
    · intro q hq hqn
      have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have h2 : q.1 ≠ n := by
        intro h; apply hqn; ext <;> simp <;> omega
      rw [hθz q.1 n (by omega) (by omega), zero_mul]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero n)) h
  obtain ⟨Q, hQ⟩ := (X_pow_dvd_iff).mpr hlow
  refine ⟨taylor (-a c) Q, ?_, ?_⟩
  · have hback : N n = taylor (-a c) (taylor (a c) (N n)) := by
      rw [taylor_taylor, neg_add_cancel, taylor_zero]
    rw [hback, hQ, taylor_mul, taylor_X_pow, C_neg, ← sub_eq_add_neg]
  · rw [taylor_eval, add_neg_cancel, ← coeff_zero_eq_eval_zero]
    have h1 : (taylor (a c) (N n)).coeff n = Q.coeff 0 := by
      rw [hQ, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [← h1, htop]
    refine mul_ne_zero (hθd n (by omega)) ?_
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hW0

/-- **`def:block`(a) for the chosen numerators `designNd`**: identity (a) and the vanishing orders, for every
reachable design (distinct places, nonzero row constants). -/
theorem designNd_spec (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (Fd : ℕ → Fin s → Fin s → F) (γ : Fin s → ℕ → F[X]) (hR : IsReachable a v Fd γ) :
    (∀ c i, i ≠ c → wCoCo a c i = -C (v i) * ∑ n ∈ range (s - 1), C (Fd n i c) * designNd a v Fd c (s - 1 - n)) ∧
      ∀ c n, n + 2 ≤ s → ∃ N', designNd a v Fd c (s - 1 - n) = (X - C (a c)) ^ n * N' ∧ N'.eval (a c) ≠ 0 := by
  classical
  have hex : ∀ c, ∃ N : ℕ → F[X], IdA a v Fd c N := fun c =>
    (designNum_exists hs a ha v hv Fd γ hR c).imp fun N h => h.1
  have hval : ∀ c n, n + 2 ≤ s → designNd a v Fd c (s - 1 - n) = Classical.choose (hex c) n := by
    intro c n hn
    simp only [designNd, dif_pos (hex c)]
    rw [show s - 1 - (s - 1 - n) = n by omega]
  refine ⟨fun c i hic => ?_, fun c n hn => ?_⟩
  · have hsum : ∑ n ∈ range (s - 1), C (Fd n i c) * Classical.choose (hex c) n =
        ∑ n ∈ range (s - 1), C (Fd n i c) * designNd a v Fd c (s - 1 - n) :=
      Finset.sum_congr rfl (fun (n : ℕ) (hn : n ∈ range (s - 1)) => by
        rw [mem_range] at hn; rw [hval c n (by omega)])
    rw [Classical.choose_spec (hex c) i hic, hsum]
  · rw [hval c n hn]
    exact designNum_order hs a ha v hv Fd γ hR c _ (Classical.choose_spec (hex c)) n hn

end Num

end GeoSeq
