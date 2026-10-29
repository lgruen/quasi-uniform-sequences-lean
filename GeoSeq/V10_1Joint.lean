/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V97Joint

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 2): `prop:joint`(ii) for a general local multiplier

Stage V9-7 proved the one-factor step `φ_c ↦ φ_c (1 + ε w^j)` (`joint_transfer`). Here the general statement, for
two self-similar scrambles in residue form (`ssResGen`, rational local multipliers `φ_c = N_c/U_c`) that differ only
in the multiplier of coordinate `c`, with `φ'_c ≡ φ_c` modulo `(z - a_c)^l`:

* **`joint_transfer_gen`**: the cross responses `X^{(l)}_{c'←c}` coincide and `O^{(l)}_c + Ψ_c(l)` coincides.
* **`joint_ii`** (`prop:joint`(ii) as stated): the congruence holds as soon as the two multipliers have the same `v_c`
  and the same correction coefficients `χ_{c,1}, …, χ_{c,l-1}` (`cong_of_corrTrunc`).

The route differs from the paper's (no factorization of the unit `φ'_c/φ_c` into factors `1 + ε w^j`): (1) the
crosses — a carry of length `l` in coordinate `c` is the index polynomial `V` whose cell digits are the carry pattern;
its digits `0, …, K-l-1` in coordinate `c` vanish, so `(z - a_c)^{K-l}` divides `V` (`dvd_of_locRes_low`), and then
`V (φ'_c - φ_c)` vanishes to order `K` at `a_c`, so the cell digits of `V` are the same for both scrambles; the other
coordinates are unchanged functions of `V`; (2) the own response — by `prop:joint`(i) for both scrambles
(`joint_col`), `v_c (O^{(l)}_c + Ψ_c(l)) = -∑_{c' ≠ c} v_{c'} X^{(l)}_{c'←c}`, and the right side is unchanged.
-/

namespace GeoSeq

open Finset Polynomial

section Joint
variable {F : Type*} [Field F] {s : ℕ}

/-- A simple pole: `Res_a(H / ((z - a) U) dz) = H(a)/U(a)`. -/
lemma locRes_one_eval (a : F) (H U : F[X]) : locRes a 1 H U = H.eval a * (U.eval a)⁻¹ := by
  unfold locRes
  rw [if_neg one_ne_zero, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    PowerSeries.constantCoeff_inv, constantCoeff_taylor, constantCoeff_taylor]

/-- If `Res_a(H / ((z - a)^{n+1} U W^{n+1}) dz) = 0` for all `n < M` (`U(a), W(a) ≠ 0`), then `(z - a)^M ∣ H`. -/
lemma dvd_of_locRes_low (a : F) (H U W : F[X]) (hU : U.eval a ≠ 0) (hW : W.eval a ≠ 0) :
    ∀ M : ℕ, (∀ n < M, locRes a (n + 1) H (U * W ^ (n + 1)) = 0) → (X - C a) ^ M ∣ H := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro h
    obtain ⟨H₁, rfl⟩ := ih fun n hn => h n (by omega)
    have h1 := h M (by omega)
    rw [show (X - C a) ^ M * H₁ = H₁ * (X - C a) ^ M by ring, show M + 1 = 1 + M by ring,
      locRes_cancel_pow, locRes_one_eval] at h1
    have hev : (U * W ^ (1 + M)).eval a ≠ 0 := by
      rw [eval_mul, eval_pow]; exact mul_ne_zero hU (pow_ne_zero _ hW)
    have hr : H₁.eval a = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd (inv_eq_zero.mp h2) hev
    obtain ⟨H₂, rfl⟩ := dvd_iff_isRoot.mpr hr
    exact ⟨H₂, by ring⟩

/-- Digit `n` of coordinate `c` of `ssResGen` at the index vector `V`, as one residue. -/
lemma ssRes_vecDigit (a : Fin s → F) (θ : F) (N U : Fin s → F[X]) {m : ℕ} (V : Fin m → F) (c : Fin s) (n : ℕ) :
    vecDigit (ssResGen a θ N U) V c n =
      θ ^ (n + 1) * locRes (a c) (n + 1) (vecPoly (vext V) m * N c) (U c * wCo a c ^ (n + 1)) := by
  rw [← vecDigit_vext, ssResGen_vecPoly]

/-- **`prop:joint`(ii), general multiplier**: two self-similar scrambles in residue form that differ only in the
local multiplier of coordinate `c`, with `φ'_c ≡ φ_c (mod (z - a_c)^l)` (i.e. `(z - a_c)^l ∣ N'_c U_c - N_c U'_c`),
and correction coefficients `χ`, `χ'` up to order `K + 1` for the same `v` (`v_c ≠ 0`). Then at every full level
`K ≥ l ≥ 1` the cross responses `X^{(l)}_{c'←c}` (carry length `l` in coordinate `c`) coincide and
`O^{(l)}_c + Ψ_c(l)` coincides. -/
theorem joint_transfer_gen (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U N' U' : Fin s → F[X]) (c : Fin s) (hN' : ∀ c', c' ≠ c → N' c' = N c')
    (hU' : ∀ c', c' ≠ c → U' c' = U c') (hU : ∀ c, (U c).eval (a c) ≠ 0) (hUc : (U' c).eval (a c) ≠ 0)
    (hNc : (N' c).eval (a c) ≠ 0) (v : Fin s → F) (hv : v c ≠ 0) (χ χ' : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (hχ0' : ∀ c, χ' c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTrunc a θ N U v χ (K + 1)) (htr' : CorrTrunc a θ N' U' v χ' (K + 1)) (l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) (hcong : (X - C (a c)) ^ l ∣ N' c * U c - N c * U' c) (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (ssResGen a θ N U) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (ssResGen a θ N' U') K 0 l c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧ Dnew c + psiSum χ' c l = Dold c + psiSum χ c l := by
  set G := ssResGen a θ N U
  set G' := ssResGen a θ N' U'
  have hother : ∀ c₁, c₁ ≠ c → G' c₁ = G c₁ := fun c₁ h => by
    funext n k; simp only [G, G', ssResGen, hN' c₁ h, hU' c₁ h]
  have hUall : ∀ c₁, (U' c₁).eval (a c₁) ≠ 0 := fun c₁ => by
    by_cases h : c₁ = c
    · subst h; exact hUc
    · rw [hU' c₁ h]; exact hU c₁
  obtain ⟨V, hV⟩ := (hnew c).1
  set P := vecPoly (vext V) (s * K) with hP
  have hw := wCo_eval_ne a ha c
  -- the new digits `0, …, K-l-1` of coordinate `c` vanish, so `(z - a_c)^{K-l} ∣ P`
  have hPdvd : (X - C (a c)) ^ (K - l) ∣ P := by
    have h1 : (X - C (a c)) ^ (K - l) ∣ P * N' c := by
      refine dvd_of_locRes_low (a c) _ (U' c) (wCo a c) hUc hw (K - l) fun n hn => ?_
      have := hV c n (by omega)
      rw [ssRes_vecDigit, carryPat, if_neg (by omega)] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hθ)
    have hcop : IsCoprime ((X - C (a c)) ^ (K - l)) (N' c) := by
      refine IsCoprime.pow_left ?_
      rw [(irreducible_X_sub_C (a c)).coprime_iff_not_dvd, dvd_iff_isRoot]
      exact hNc
    exact hcop.dvd_of_dvd_mul_right h1
  -- hence the old cell digits are the new ones
  have hcell : ∀ c₁, ∀ n < K, vecDigit G V c₁ n = carryPat K l c c₁ n := by
    intro c₁ n hn
    by_cases hc : c₁ = c
    · subst hc
      rw [← hV c₁ n hn, ssRes_vecDigit, ssRes_vecDigit]
      congr 1
      obtain ⟨P₁, hP₁⟩ := hPdvd
      obtain ⟨Q₁, hQ₁⟩ := hcong
      have e1 : locRes (a c₁) (n + 1) (P * N' c₁) (U' c₁ * wCo a c₁ ^ (n + 1)) =
          locRes (a c₁) (n + 1) (P * N' c₁ * U c₁) (U c₁ * U' c₁ * wCo a c₁ ^ (n + 1)) := by
        rw [mul_assoc (U c₁) (U' c₁), locRes_cancel_unit _ _ _ _ _ (hU c₁)]
      have e2 : locRes (a c₁) (n + 1) (P * N c₁) (U c₁ * wCo a c₁ ^ (n + 1)) =
          locRes (a c₁) (n + 1) (P * N c₁ * U' c₁) (U c₁ * U' c₁ * wCo a c₁ ^ (n + 1)) := by
        rw [show U c₁ * U' c₁ * wCo a c₁ ^ (n + 1) = U' c₁ * (U c₁ * wCo a c₁ ^ (n + 1)) by ring,
          locRes_cancel_unit _ _ _ _ _ hUc]
      have e3 : P * N' c₁ * U c₁ = P * N c₁ * U' c₁ + (P₁ * Q₁) * (X - C (a c₁)) ^ K := by
        rw [show K = (K - l) + l by omega, pow_add]
        linear_combination P * hQ₁ + ((X - C (a c₁)) ^ l * Q₁) * hP₁
      rw [e1, e2, e3, locRes_add, locRes_high _ _ _ _ _ (by omega), add_zero]
    · have e : vecDigit G V c₁ n = vecDigit G' V c₁ n := by unfold vecDigit; rw [hother c₁ hc]
      rw [e]; exact hV c₁ n hn
  have hO : ∀ c₁, Dold c₁ = vecDigit G V c₁ K := fun c₁ => by
    have := (hold c₁).2 V hcell; rw [Nat.add_zero] at this; exact this.symm
  have hN : ∀ c₁, Dnew c₁ = vecDigit G' V c₁ K := fun c₁ => by
    have := (hnew c₁).2 V hV; rw [Nat.add_zero] at this; exact this.symm
  have hcross : ∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁ := fun c₁ h => by
    rw [hN, hO]; unfold vecDigit; rw [hother c₁ h]
  refine ⟨hcross, ?_⟩
  have j1 := joint_col hs a ha θ hθ N U hU v χ hχ0 K hK htr l hlK c Dold hold
  have j2 := joint_col hs a ha θ hθ N' U' hUall v χ' hχ0' K hK htr' l hlK c Dnew hnew
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)] at j1 j2
  have hrest : ∑ c₁ ∈ univ.erase c, v c₁ * Dnew c₁ = ∑ c₁ ∈ univ.erase c, v c₁ * Dold c₁ :=
    Finset.sum_congr rfl fun c₁ hc₁ => by rw [hcross c₁ (Finset.ne_of_mem_erase hc₁)]
  rw [hrest] at j2
  have : v c * ((Dnew c + psiSum χ' c l) - (Dold c + psiSum χ c l)) = 0 := by linear_combination j2 - j1
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hv)

/-- Same `v_c` and the same correction coefficients `χ_{c,d}`, `d < l`, give `φ'_c ≡ φ_c (mod (z - a_c)^l)`. -/
theorem cong_of_corrTrunc (a : Fin s → F) (θ : F) (N U N' U' : Fin s → F[X]) (c : Fin s) (v : Fin s → F)
    (χ χ' : Fin s → ℕ → F) (K l : ℕ) (hlK : l ≤ K + 1) (htr : CorrTrunc a θ N U v χ (K + 1))
    (htr' : CorrTrunc a θ N' U' v χ' (K + 1)) (hχ : ∀ d, d < l → χ' c d = χ c d) :
    (X - C (a c)) ^ l ∣ N' c * U c - N c * U' c := by
  set S := ∑ d ∈ range (K + 1), C (χ c d) * (C θ⁻¹ * wPoly a) ^ d
  set S' := ∑ d ∈ range (K + 1), C (χ' c d) * (C θ⁻¹ * wPoly a) ^ d
  have h1 : (X - C (a c)) ^ l ∣ U c - C (v c) * N c * S := (pow_dvd_pow _ hlK).trans (htr c)
  have h2 : (X - C (a c)) ^ l ∣ U' c - C (v c) * N' c * S' := (pow_dvd_pow _ hlK).trans (htr' c)
  have h3 : (X - C (a c)) ^ l ∣ S - S' := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun d _ => ?_
    by_cases hd : d < l
    · rw [hχ d hd, sub_self]; exact dvd_zero _
    · rw [← sub_mul]
      refine Dvd.dvd.mul_left ?_ _
      rw [wPoly_eq a c, mul_pow, mul_pow]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _) _
  have e : N' c * U c - N c * U' c = N' c * (U c - C (v c) * N c * S) - N c * (U' c - C (v c) * N' c * S') +
      C (v c) * N c * N' c * (S - S') := by ring
  rw [e]
  exact dvd_add (dvd_sub (h1.mul_left _) (h2.mul_left _)) (h3.mul_left _)

/-- **`prop:joint`(ii)** (as stated): for every column `c` and depth `l`, `O^{(l)}_c + Ψ_c(l)` and the cross responses
`X^{(l)}_{c'←c}` depend only on `v_c`, `χ_{c,1}, …, χ_{c,l-1}`, `θ` and the local multipliers of the other
coordinates: two self-similar scrambles in residue form that differ only in the multiplier of coordinate `c`, with
the same `v` and correction coefficients agreeing below `l` in coordinate `c`, have the same crosses and the same
`O^{(l)}_c + Ψ_c(l)` at every full level `K ≥ l ≥ 1`. -/
theorem joint_ii (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U N' U' : Fin s → F[X]) (c : Fin s) (hN' : ∀ c', c' ≠ c → N' c' = N c')
    (hU' : ∀ c', c' ≠ c → U' c' = U c') (hU : ∀ c, (U c).eval (a c) ≠ 0) (hUc : (U' c).eval (a c) ≠ 0)
    (hNc : (N' c).eval (a c) ≠ 0) (v : Fin s → F) (hv : v c ≠ 0) (χ χ' : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (hχ0' : ∀ c, χ' c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTrunc a θ N U v χ (K + 1)) (htr' : CorrTrunc a θ N' U' v χ' (K + 1)) (l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) (hχ : ∀ d, d < l → χ' c d = χ c d) (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (ssResGen a θ N U) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (ssResGen a θ N' U') K 0 l c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧ Dnew c + psiSum χ' c l = Dold c + psiSum χ c l :=
  joint_transfer_gen hs a ha θ hθ N U N' U' c hN' hU' hU hUc hNc v hv χ χ' hχ0 hχ0' K hK htr htr' l hl hlK
    (cong_of_corrTrunc a θ N U N' U' c v χ χ' K l (by omega) htr htr' hχ) Dold Dnew hold hnew

end Joint

end GeoSeq
