/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V94Defs
public import GeoSeq.V9Seq

@[expose] public section

/-!
# GeoSeq stage V9-4 (part 1): staggered residue sequences (`def:residuestar`, `lem:residuestar-t0`,
`lem:residuestar-rel`)

Over any field `F` with distinct places.

* `placeCo_stagK_ne`, `placeCo_stagK_self`: the cofactors of `(z - a_c)^{n+1}` in `(z - a_{c⋆}) w^N` are
  `(z - a_{c⋆}) w_c^N` (`c ≠ c⋆`) and `w_{c⋆}^N` (`c = c⋆`).
* `resStar_apply`, `resStar_apply_ne`, `resStar_apply_self` (**`def:residuestar`**, matrix form):
  `C_c[n][i] = μ_c θ^{n+1} [(z - a_c)^n] z^i / ((z - a_{c⋆}) w_c^{n+1})`, `C_{c⋆}[n][i] = μ⋆ θ^n [(z - a_{c⋆})^n]
  z^i / w_{c⋆}^n` (coefficients of `t^n` in power series in `t = z - a_c`).
* `resStar_digit` (**`def:residuestar`**, residue reading).
* `resStarL_diag`, `resStarL_diag_ne`, `resStar_t0` (**`lem:residuestar-t0`**): `L_c[n][n] = μ_c θ^{n+1} /
  ((a_c - a_{c⋆}) w'(a_c)^{n+1})`, `L_{c⋆}[n][n] = μ⋆ θ^n / w'(a_{c⋆})^n`; `𝓡^⋆_v` is a digital `(0,s)`-sequence.
* `resStar_rel`, `resStar_rel_shift`, `resStar_rel_seq` (**`lem:residuestar-rel`**):
  `y_{c⋆,K+i}(V) = ∑_{c ≠ c⋆} k_c y_{c,K-1+i}(V)` for `deg V < sK`, `i ≥ 0`; proof: `res_thm_zero` with
  `F = θ^K V / ((z - a_{c⋆}) w^K)` (pole orders `stagK cs K`, total `sK + 1`).
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F] {s : ℕ}

lemma stagK_own (cs c : Fin s) (n : ℕ) : stagK cs (stagLev cs c n) c = n + 1 := by
  unfold stagK stagLev; split_ifs <;> rfl

lemma placeCo_stagK_ne (a : Fin s → F) (cs c : Fin s) (hc : c ≠ cs) (N : ℕ) :
    placeCo a (stagK cs N) c = (X - C (a cs)) * wCo a c ^ N := by
  rw [placeCo, wCo, ← Finset.prod_pow]
  have hmem : cs ∈ univ.erase c := Finset.mem_erase.mpr ⟨Ne.symm hc, mem_univ cs⟩
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase (univ.erase c) _ hmem]
  have hrest : ∏ x ∈ (univ.erase c).erase cs, (X - C (a x)) ^ stagK cs N x =
      ∏ x ∈ (univ.erase c).erase cs, (X - C (a x)) ^ N :=
    Finset.prod_congr rfl fun x hx => by
      rw [stagK, if_neg (Finset.ne_of_mem_erase hx)]
  rw [hrest, stagK, if_pos rfl, pow_succ]; ring

lemma placeCo_stagK_self (a : Fin s → F) (cs : Fin s) (N : ℕ) :
    placeCo a (stagK cs N) cs = wCo a cs ^ N := by
  rw [placeCo, wCo, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun x hx => by rw [stagK, if_neg (Finset.ne_of_mem_erase hx)]

lemma stagK_sum (cs : Fin s) (N : ℕ) : ∑ c, stagK cs N c = s * N + 1 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ cs)]
  have : ∑ x ∈ univ.erase cs, stagK cs N x = ∑ x ∈ univ.erase cs, N :=
    Finset.sum_congr rfl fun x hx => by rw [stagK, if_neg (Finset.ne_of_mem_erase hx)]
  rw [this, Finset.sum_const, Finset.card_erase_of_mem (mem_univ cs), card_univ, Fintype.card_fin,
    stagK, if_pos rfl, smul_eq_mul]
  rcases Nat.eq_zero_or_pos s with h | h
  · exact absurd cs.isLt (by omega)
  · have : s - 1 + 1 = s := by omega
    calc N + 1 + (s - 1) * N = (s - 1 + 1) * N + 1 := by ring
      _ = s * N + 1 := by rw [this]

/-- **`def:residuestar`** (matrix form, uniform): `C_c[n][i] = μ_c θ^N [t^n] (a_c + t)^i U(a_c + t)^{-1}`,
`N = stagLev cs c n`, `U = placeCo a (stagK cs N) c`. -/
theorem resStar_apply (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (n i : ℕ) :
    resStar a θ cs μs k c n i = stagMu cs μs k c * θ ^ stagLev cs c n * PowerSeries.coeff n
      ((taylor (a c) (X ^ i) : PowerSeries F) *
        (taylor (a c) (placeCo a (stagK cs (stagLev cs c n)) c) : PowerSeries F)⁻¹) := by
  rw [resStar, scrGen, coeff_mul_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resStarL, Polynomial.coeff_coe, coeff_taylor_X_pow]
  ring

/-- **`def:residuestar`** (matrix form, `c ≠ c⋆`): `C_c[n][i] = μ_c θ^{n+1} [(z - a_c)^n] z^i /
((z - a_{c⋆}) w_c(z)^{n+1})`. -/
theorem resStar_apply_ne (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (hc : c ≠ cs) (n i : ℕ) :
    resStar a θ cs μs k c n i = -μs / k c * θ ^ (n + 1) * PowerSeries.coeff n
      ((taylor (a c) (X ^ i) : PowerSeries F) *
        (taylor (a c) ((X - C (a cs)) * wCo a c ^ (n + 1)) : PowerSeries F)⁻¹) := by
  rw [resStar_apply, stagMu, if_neg hc, stagLev, if_neg hc, placeCo_stagK_ne a cs c hc]

/-- **`def:residuestar`** (matrix form, `c = c⋆`): `C_{c⋆}[n][i] = μ⋆ θ^n [(z - a_{c⋆})^n] z^i / w_{c⋆}(z)^n`. -/
theorem resStar_apply_self (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (n i : ℕ) :
    resStar a θ cs μs k cs n i = μs * θ ^ n * PowerSeries.coeff n
      ((taylor (a cs) (X ^ i) : PowerSeries F) *
        (taylor (a cs) (wCo a cs ^ n) : PowerSeries F)⁻¹) := by
  rw [resStar_apply, stagMu, if_pos rfl, stagLev, if_pos rfl, placeCo_stagK_self]

/-- **`def:residuestar`** (residue reading): digit `n` of coordinate `c` of the point with index digits
`f_0, …, f_{m-1}` is `μ_c θ^N Res_{a_c}(V dz / ((z - a_{c⋆}) w^N))`, `N = stagLev cs c n` (`n + 1` for `c ≠ c⋆`,
`n` for `c⋆`; the pole order at `a_c` is `n + 1`, `stagK_own`). -/
theorem resStar_digit (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (f : ℕ → F)
    (m : ℕ) (c : Fin s) (n : ℕ) :
    ∑ j ∈ range m, resStar a θ cs μs k c n j * f j =
      stagMu cs μs k c * θ ^ stagLev cs c n *
        resAt a (stagK cs (stagLev cs c n)) (vecPoly f m) c := by
  rw [resAt, stagK_own, resStar, scrGen_res, locRes, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    coeff_mul_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [locRes_one, resStarL, Polynomial.coeff_coe]
  ring

/-- The diagonal of the scramble (`lem:residuestar-t0`): `L_c[n][n] = μ_c θ^N U(a_c)^{-1}`. -/
theorem resStarL_diag (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (n : ℕ) :
    resStarL a θ cs μs k c n n = stagMu cs μs k c * θ ^ stagLev cs c n *
      ((placeCo a (stagK cs (stagLev cs c n)) c).eval (a c))⁻¹ := by
  rw [resStarL, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.constantCoeff_inv, constantCoeff_taylor]

/-- `lem:residuestar-t0`, the diagonal for `c ≠ c⋆`: `L_c[n][n] = μ_c θ^{n+1} / ((a_c - a_{c⋆}) w'(a_c)^{n+1})`
(`w'(a_c) = w_c(a_c)`). -/
theorem resStarL_diag_ne (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (c : Fin s)
    (hc : c ≠ cs) (n : ℕ) :
    resStarL a θ cs μs k c n n =
      -μs / k c * θ ^ (n + 1) / ((a c - a cs) * (wCo a c).eval (a c) ^ (n + 1)) := by
  rw [resStarL_diag, stagMu, if_neg hc, stagLev, if_neg hc, placeCo_stagK_ne a cs c hc, eval_mul,
    eval_pow, eval_sub, eval_X, eval_C]; ring

/-- `lem:residuestar-t0`, the diagonal for `c⋆`: `L_{c⋆}[n][n] = μ⋆ θ^n / w'(a_{c⋆})^n`. -/
theorem resStarL_diag_self (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F) (n : ℕ) :
    resStarL a θ cs μs k cs n n = μs * θ ^ n / (wCo a cs).eval (a cs) ^ n := by
  rw [resStarL_diag, stagMu, if_pos rfl, stagLev, if_pos rfl, placeCo_stagK_self, eval_pow]; ring

lemma stagMu_ne (cs : Fin s) (μs : F) (hμ : μs ≠ 0) (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0)
    (c : Fin s) : stagMu cs μs k c ≠ 0 := by
  unfold stagMu
  split_ifs with h
  · exact hμ
  · exact div_ne_zero (neg_ne_zero.mpr hμ) (hk c h)

lemma resStarL_diag_ne_zero (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (cs : Fin s) (μs : F) (hμ : μs ≠ 0) (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) (c : Fin s)
    (n : ℕ) : resStarL a θ cs μs k c n n ≠ 0 := by
  rw [resStarL_diag]
  exact mul_ne_zero (mul_ne_zero (stagMu_ne cs μs hμ k hk c) (pow_ne_zero _ hθ))
    (inv_ne_zero (placeCo_eval_ne a ha _ c))

/-- **`lem:residuestar-t0`**: for distinct places, `θ, μ⋆ ≠ 0` and nonzero weights, the staggered residue
sequence `C_c = L_c P_{a_c}` is a digital `(0,s)`-sequence. -/
theorem resStar_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q)
    (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (cs : Fin s) (μs : F)
    (hμ : μs ≠ 0) (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) :
    IsSeq0 D (resStar a θ cs μs k) :=
  t0 D a ha _ fun c n => resStarL_diag_ne_zero a ha θ hθ cs μs hμ k hk c n

/-- **`lem:residuestar-rel`**: for `K ≥ 1` and `deg V < m ≤ sK`, `y_{c⋆,K}(V) = ∑_{c ≠ c⋆} k_c y_{c,K-1}(V)`. -/
theorem resStar_rel (a : Fin s → F) (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F)
    (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (f : ℕ → F) (m : ℕ)
    (hm : m ≤ s * K) :
    ∑ j ∈ range m, resStar a θ cs μs k cs K j * f j =
      ∑ c ∈ univ.erase cs, k c * ∑ j ∈ range m, resStar a θ cs μs k c (K - 1) j * f j := by
  have hdeg : (vecPoly f m).natDegree + 2 ≤ ∑ c, stagK cs K c := by
    have hs : 1 ≤ s := cs.pos
    have hsK : 1 ≤ s * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [stagK_sum]; have := vecPoly_natDegree f m; omega
  have h0 := res_thm_zero a ha (stagK cs K) (vecPoly f m) hdeg
  rw [← Finset.add_sum_erase _ _ (mem_univ cs)] at h0
  have hlev : ∀ c ∈ univ.erase cs, stagLev cs c (K - 1) = K := fun c hc => by
    rw [stagLev, if_neg (Finset.ne_of_mem_erase hc)]; omega
  rw [resStar_digit, stagLev, if_pos rfl, stagMu, if_pos rfl]
  have hrhs : ∑ c ∈ univ.erase cs, k c * ∑ j ∈ range m, resStar a θ cs μs k c (K - 1) j * f j =
      ∑ c ∈ univ.erase cs, (-μs) * θ ^ K * resAt a (stagK cs K) (vecPoly f m) c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [resStar_digit, hlev c hc, stagMu, if_neg (Finset.ne_of_mem_erase hc)]
    field_simp [hk c (Finset.ne_of_mem_erase hc)]
  rw [hrhs, ← Finset.mul_sum, eq_neg_of_add_eq_zero_right h0]
  ring

/-- **`lem:residuestar-rel`**, general form: `y_{c⋆,K+i}(V) = ∑_{c ≠ c⋆} k_c y_{c,K-1+i}(V)` for every `i ≥ 0`
and `deg V < m ≤ sK`. -/
theorem resStar_rel_shift (a : Fin s → F) (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F)
    (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : ℕ) (f : ℕ → F) (m : ℕ)
    (hm : m ≤ s * K) :
    ∑ j ∈ range m, resStar a θ cs μs k cs (K + i) j * f j =
      ∑ c ∈ univ.erase cs, k c * ∑ j ∈ range m, resStar a θ cs μs k c (K - 1 + i) j * f j := by
  have h := resStar_rel a ha θ cs μs k hk (K + i) (by omega) f m
    (le_trans hm (Nat.mul_le_mul_left s (by omega)))
  rwa [show K + i - 1 = K - 1 + i by omega] at h

/-- `lem:residuestar-rel` for the points of the digital sequence: for `K ≥ 1`, `i ≥ 0` and every index
`x < q^{sK}` (the full level `P_{sK}`), `y_{c⋆,K+i}(x) = ∑_{c ≠ c⋆} k_c y_{c,K-1+i}(x)`. -/
theorem resStar_rel_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F)
    (hk : ∀ c, c ≠ cs → k c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (i : ℕ) (x : ℕ) (hx : x < q ^ (s * K)) :
    seqDigit D (resStar a θ cs μs k) x cs (K + i) =
      ∑ c ∈ univ.erase cs, k c * seqDigit D (resStar a θ cs μs k) x c (K - 1 + i) := by
  have hdig : ∀ c n, seqDigit D (resStar a θ cs μs k) x c n =
      ∑ j ∈ range (s * K), resStar a θ cs μs k c n j * idxDigit D x j := fun c n =>
    seqDigit_eq_range D _ x c _ _ fun j hj => idxDigit_eq_zero D x j
      (digit_high x j (lt_of_lt_of_le hx (Nat.pow_le_pow_right (NeZero.pos q) hj)))
  simp_rw [hdig]
  exact resStar_rel_shift a ha θ cs μs k hk K hK i _ _ le_rfl

end GeoSeq
