/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_4Num

@[expose] public section

/-!
# GeoSeq stage V10-4 (part 2): the transfer of the nets' design `U*_s` under `x ↦ 1/(x+1)`

The proof of `thm:block`(c), "Reachability": by the nets library (`Z3NetA.Ustar_reach`, the formal `thm:A` proof,
reachability of `U*_s` over `R_S = ℤ[1/(s-2)!]` at the places `∞, 0, 1, …, s-2` with constant row scalars `λ' ≡ 1`),
`F_n[c][d] = w̃_{cd} G_{d,n}(ỹ_{cd})` with `G_{d,n} = ∑_{n' ≤ n} U'_d[n', n] Y^{n'}` of exact degree `n`. Reducing modulo
a prime `p ≥ s` (`rsHom`, `R_S → ℤ/pℤ`) and moving the places by `x ↦ 1/(x+1)`:

* `w̃_{ic} = ϱ_i τ_{ic} ς_c` and `ỹ_{ic} = A_c(τ_{ic})` with `A_c` affine with column-only coefficients
  (`wN_transfer`, `yN_transfer`; `ϱ_i = -1/(â_i+1)`, `ς_c = 1/(â_c + 1)`, `A_c(X) = -X/(â_c+1)² - 1/(â_c+1)`, and
  `ϱ_∞ = -1`, `ς_∞ = -1`, `A_∞(X) = X - 1`), so
* **`ustar_reachable`**: the design `U*_s` is reachable (`IsReachable`) at the places `0, 1, 1/2, …, 1/(s-1)` with the
  row constants `v = (1, 1, 2, …, s-1)` (`v_i⁻¹ = -ϱ_i`) and `γ_{c,n} = -ς_c G_{c,n}(A_c(X))`, for every prime `p ≥ s`.
-/

namespace GeoSeq

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- `(s-2)!` is a unit modulo every prime `p > s - 2`. -/
lemma fact_isUnit (s : ℕ) (hp : s - 2 < p) : IsUnit ((Int.castRingHom (ZMod p)) (((s - 2).factorial : ℕ) : ℤ)) := by
  rw [isUnit_iff_ne_zero]
  simp only [eq_intCast, Int.cast_natCast]
  intro h
  rw [ZMod.natCast_eq_zero_iff, (Fact.out : p.Prime).dvd_factorial] at h
  omega

/-- The reduction `R_S = ℤ[1/(s-2)!] → ℤ/pℤ` for a prime `p > s - 2`. -/
noncomputable def rsHom (s : ℕ) (hp : s - 2 < p) : Z3NetA.RS s →+* ZMod p :=
  IsLocalization.Away.lift (S := Z3NetA.RS s) (((s - 2).factorial : ℕ) : ℤ) (fact_isUnit s hp)

lemma natCast_ne_zero_of_lt {n : ℕ} (h0 : n ≠ 0) (hn : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h) (by omega)

lemma natCast_sub_ne_zero {s : ℕ} (hsp : s ≤ p) {i c : Fin s} (h : i ≠ c) :
    ((i : ℕ) : ZMod p) - ((c : ℕ) : ZMod p) ≠ 0 := by
  rw [sub_ne_zero]
  intro he
  have := (ZMod.natCast_eq_natCast_iff' (i : ℕ) (c : ℕ) p).mp he
  rw [Nat.mod_eq_of_lt (by omega : (i : ℕ) < p), Nat.mod_eq_of_lt (by omega : (c : ℕ) < p)] at this
  exact h (Fin.ext this)

/-- The places `1/c` are distinct for `p ≥ s`. -/
lemma ustarA_injective {s : ℕ} (hsp : s ≤ p) : Function.Injective (ustarA (p := p) s) := by
  intro i c h
  by_contra hic
  unfold ustarA at h
  by_cases hi : (i : ℕ) = 0
  · have hc : (c : ℕ) ≠ 0 := fun hc => hic (Fin.ext (hi.trans hc.symm))
    rw [hi, Nat.cast_zero, inv_zero] at h
    exact inv_ne_zero (natCast_ne_zero_of_lt hc (by omega)) h.symm
  · by_cases hc : (c : ℕ) = 0
    · rw [hc, Nat.cast_zero, inv_zero] at h
      exact inv_ne_zero (natCast_ne_zero_of_lt hi (by omega)) h
    · rw [inv_inj] at h
      exact natCast_sub_ne_zero hsp hic (sub_eq_zero.mpr h)

/-- The row constants `(1, 1, 2, …, s-1)` are nonzero for `p ≥ s`. -/
lemma ustarV_ne {s : ℕ} (hsp : s ≤ p) (c : Fin s) : ustarV (p := p) s c ≠ 0 := by
  unfold ustarV
  split_ifs with h
  · exact one_ne_zero
  · exact natCast_ne_zero_of_lt h (by omega)

lemma natDegree_affC {s : ℕ} (hsp : s ≤ p) (c : Fin s) : (affC (p := p) c).natDegree = 1 := by
  unfold affC
  split_ifs with h
  · exact natDegree_X_sub_C 1
  · refine natDegree_linear (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 ?_)))
    exact natCast_ne_zero_of_lt h (by omega)

/-- **The transfer of the weights**: `w̃_{ic} = v_i⁻¹ τ_{ic} (-ς_c)` at the places `a = 1/(â+1)`. -/
lemma wN_transfer {s : ℕ} (hsp : s ≤ p) {i c : Fin s} (hic : i ≠ c) :
    wNp (p := p) i c = (ustarV s i)⁻¹ * tauF (ustarA s) i c * -sgC c := by
  have hne := natCast_sub_ne_zero (p := p) hsp hic
  unfold wNp ustarV tauF ustarA sgC
  by_cases hi : (i : ℕ) = 0
  · have hc : (c : ℕ) ≠ 0 := fun hc => hic (Fin.ext (hi.trans hc.symm))
    have hc' := natCast_ne_zero_of_lt (p := p) hc (by omega)
    simp only [hi, hc, true_or, if_true, if_false, Nat.cast_zero, inv_zero, inv_one, one_mul, zero_sub]
    field_simp
  · have hi' := natCast_ne_zero_of_lt (p := p) hi (by omega)
    by_cases hc : (c : ℕ) = 0
    · simp only [hi, hc, or_true, if_true, if_false, Nat.cast_zero, inv_zero, sub_zero, neg_neg, mul_one]
      field_simp
      simp
    · have hc' := natCast_ne_zero_of_lt (p := p) hc (by omega)
      simp only [hi, hc, or_self, if_false]
      have h2 : ((i : ℕ) : ZMod p)⁻¹ - ((c : ℕ) : ZMod p)⁻¹ ≠ 0 := by
        rw [inv_sub_inv hi' hc']
        exact div_ne_zero (fun h => hne (by linear_combination -h)) (mul_ne_zero hi' hc')
      have hne' : ((c : ℕ) : ZMod p) - ((i : ℕ) : ZMod p) ≠ 0 := fun h => hne (by linear_combination -h)
      rw [inv_sub_inv hi' hc']
      field_simp
      ring

/-- **The transfer of the nodes**: `ỹ_{ic} = A_c(τ_{ic})`, an affine function with column-only coefficients. -/
lemma yN_transfer {s : ℕ} (hsp : s ≤ p) {i c : Fin s} (hic : i ≠ c) :
    yNp (p := p) i c = (affC c).eval (tauF (ustarA s) i c) := by
  have hne := natCast_sub_ne_zero (p := p) hsp hic
  unfold yNp affC tauF ustarA
  by_cases hi : (i : ℕ) = 0
  · have hc : (c : ℕ) ≠ 0 := fun hc => hic (Fin.ext (hi.trans hc.symm))
    have hc' := natCast_ne_zero_of_lt (p := p) hc (by omega)
    simp only [hi, hc, if_true, if_false, Nat.cast_zero, inv_zero, zero_sub, eval_add, eval_mul, eval_C, eval_X]
    field_simp
    ring
  · have hi' := natCast_ne_zero_of_lt (p := p) hi (by omega)
    by_cases hc : (c : ℕ) = 0
    · simp only [hi, hc, if_true, if_false, Nat.cast_zero, inv_zero, eval_sub, eval_X, eval_C]
      rw [show (((i : ℕ) : ZMod p)⁻¹ - 0) = ((i : ℕ) : ZMod p)⁻¹ from sub_zero _, inv_inv]
    · have hc' := natCast_ne_zero_of_lt (p := p) hc (by omega)
      simp only [hi, hc, if_false, eval_add, eval_mul, eval_C, eval_X]
      have hne' : ((c : ℕ) : ZMod p) - ((i : ℕ) : ZMod p) ≠ 0 := fun h => hne (by linear_combination -h)
      rw [inv_sub_inv hi' hc']
      field_simp
      ring

/-- `ψ(1/(a_i - a_c))` for a unit difference of places of `R_S`. -/
lemma rsHom_inverse {s : ℕ} (hp : s - 2 < p) (u : Z3NetA.RS s) (hu : IsUnit u) :
    rsHom s hp (Ring.inverse u) = (rsHom s hp u)⁻¹ := by
  have h1 : rsHom s hp (Ring.inverse u) * rsHom s hp u = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel u hu, map_one]
  exact eq_inv_of_mul_eq_one_left h1

lemma rsHom_placeA {s : ℕ} (hp : s - 2 < p) (c : Fin s) :
    rsHom s hp (Z3NetA.placeA c) = ((c : ℕ) : ZMod p) - 1 := by
  rw [Z3NetA.placeA, RingHom.map_sub, map_natCast, map_one]

lemma rsHom_wN {s : ℕ} [NeZero s] (hp : s - 2 < p) (hPOK : Z3NetF.PlacesOK (0 : Fin s) (Z3NetA.placeA : Fin s → Z3NetA.RS s))
    {i c : Fin s} (hic : i ≠ c) :
    rsHom s hp (Z3NetF.wN (0 : Fin s) Z3NetA.placeA i c) = wNp i c := by
  unfold Z3NetF.wN wNp
  have e0 : ∀ x : Fin s, x = 0 ↔ (x : ℕ) = 0 := fun x => by rw [Fin.ext_iff]; simp
  by_cases h : i = 0 ∨ c = 0
  · rw [if_pos h, if_pos (by rwa [← e0, ← e0]), map_one]
  · rw [if_neg h, if_neg (by rwa [← e0, ← e0])]
    push Not at h
    rw [rsHom_inverse hp _ (hPOK i c h.1 h.2 hic), RingHom.map_sub, rsHom_placeA, rsHom_placeA]
    congr 1; ring

lemma rsHom_yN {s : ℕ} [NeZero s] (hp : s - 2 < p) (hPOK : Z3NetF.PlacesOK (0 : Fin s) (Z3NetA.placeA : Fin s → Z3NetA.RS s))
    {i c : Fin s} (hic : i ≠ c) :
    rsHom s hp (Z3NetF.yN (0 : Fin s) Z3NetA.placeA i c) = yNp i c := by
  unfold Z3NetF.yN yNp
  have e0 : ∀ x : Fin s, x = 0 ↔ (x : ℕ) = 0 := fun x => by rw [Fin.ext_iff]; simp
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos ((e0 i).mp hi), map_zero]
  · rw [if_neg hi, if_neg (fun h => hi ((e0 i).mpr h))]
    by_cases hc : c = 0
    · rw [if_pos hc, if_pos ((e0 c).mp hc), rsHom_placeA]
    · rw [if_neg hc, if_neg (fun h => hc ((e0 c).mpr h)), rsHom_inverse hp _ (hPOK i c hi hc hic), RingHom.map_sub,
        rsHom_placeA, rsHom_placeA]
      congr 1; ring

/-- **From the nets' form to `def:block`'s reachability** (the transfer, for any design): if
`F_n[i][c] = w̃_{ic} G_{c,n}(ỹ_{ic})` (`i ≠ c`, the nets' weights and nodes at the places `∞, 0, …, s-2`, reduced
modulo `p`) with `G_{c,n}` of exact degree `n`, then the design is reachable at the places `0, 1, 1/2, …, 1/(s-1)` with
the row constants `(1, 1, 2, …, s-1)` and `γ_{c,n} = -ς_c G_{c,n}(A_c(X))`. -/
theorem reach_of_netsForm {s : ℕ} (hsp : s ≤ p) (Fd : ℕ → Fin s → Fin s → ZMod p) (G : Fin s → ℕ → (ZMod p)[X])
    (hG : ∀ c n, n + 2 ≤ s → (G c n).natDegree = n ∧ (G c n).coeff n ≠ 0)
    (hF : ∀ c i, i ≠ c → ∀ n, n + 2 ≤ s → Fd n i c = wNp i c * (G c n).eval (yNp i c)) :
    IsReachable (ustarA s) (ustarV s) Fd (fun c n => C (-sgC c) * (G c n).comp (affC c)) := by
  refine ⟨fun c n hn => ?_, fun c i hic n hn => ?_⟩
  · have hsg : -sgC (p := p) c ≠ 0 := by
      unfold sgC
      split_ifs with h
      · exact neg_ne_zero.mpr (neg_ne_zero.mpr (one_ne_zero (α := ZMod p)))
      · exact neg_ne_zero.mpr (inv_ne_zero (natCast_ne_zero_of_lt h (by omega)))
    obtain ⟨hd, hc⟩ := hG c n hn
    have hcomp : ((G c n).comp (affC c)).natDegree = n := by
      rw [natDegree_comp, hd, natDegree_affC hsp, mul_one]
    refine ⟨by rw [natDegree_C_mul hsg, hcomp], ?_⟩
    refine mul_ne_zero (C_ne_zero.mpr hsg) fun h0 => ?_
    have hlc : ((G c n).comp (affC c)).leadingCoeff ≠ 0 := by
      rw [leadingCoeff_comp (by rw [natDegree_affC hsp]; exact one_ne_zero)]
      refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
      · rw [leadingCoeff, hd]; exact hc
      · exact leadingCoeff_ne_zero.mpr fun h => by
          have := natDegree_affC (p := p) hsp c; rw [h, natDegree_zero] at this; exact zero_ne_one this
    rw [h0, leadingCoeff_zero] at hlc
    exact hlc rfl
  · rw [hF c i hic n hn, eval_mul, eval_C, eval_comp, ← yN_transfer hsp hic, wN_transfer hsp hic]
    ring

/-- **The proof of `thm:block`(c), "Reachability"**: for `s ≥ 3` and every prime `p ≥ s`, the nets' design `U*_s`
(`Z3NetA.UstarF s`) is reachable (`IsReachable`, `def:block`) at the places `0, 1, 1/2, …, 1/(s-1)` with the row
constants `v = (1, 1, 2, …, s-1)`. -/
theorem ustar_reachable {s : ℕ} [NeZero s] (hs : 3 ≤ s) (hsp : s ≤ p) :
    ∃ γ : Fin s → ℕ → (ZMod p)[X], IsReachable (ustarA s) (ustarV s) (ustarFd s) γ := by
  have hp : s - 2 < p := by omega
  obtain ⟨hPOK, Ur, hres⟩ := Z3NetA.Ustar_reach hs
  obtain ⟨_, _, hUd, hF⟩ := hres
  set ψ := rsHom s hp
  set G : Fin s → ℕ → (ZMod p)[X] := fun c n => ∑ n' ∈ range (n + 1), C (ψ (Ur c n' n)) * X ^ n' with hG
  have hGdeg : ∀ c n, n + 2 ≤ s → (G c n).natDegree = n ∧ (G c n).coeff n ≠ 0 := by
    intro c n hn
    have hcoef : (G c n).coeff n = ψ (Ur c n n) := by
      rw [hG]
      simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow]
      rw [sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero]) (by simp), if_pos rfl, mul_one]
    have hu : ψ (Ur c n n) ≠ 0 := ((hUd c n (by omega)).map ψ).ne_zero
    refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoef]; exact hu), by rw [hcoef]; exact hu⟩
    refine natDegree_sum_le_of_forall_le _ _ fun n' hn' => ?_
    rw [mem_range] at hn'
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  refine ⟨_, reach_of_netsForm hsp (ustarFd s) G hGdeg fun c i hic n hn => ?_⟩
  have hFn := hF i c hic n (by omega)
  have h1 : (ustarFd (p := p) s n i c) = ψ (Z3NetA.UstarR s n i c) := by
    simp [ustarFd, blockF, Z3NetA.UstarR, map_intCast]
  have hw : ψ (Z3NetF.wN (0 : Fin s) Z3NetA.placeA i c) = wNp i c := rsHom_wN hp hPOK hic
  have hy : ψ (Z3NetF.yN (0 : Fin s) Z3NetA.placeA i c) = yNp i c := rsHom_yN hp hPOK hic
  rw [h1, hFn, Pi.one_apply, one_mul, map_sum]
  simp only [map_mul, map_pow, hw, hy, hG, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  ring

end GeoSeq
