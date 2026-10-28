/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Res
public import GeoSeq.T0
public import GeoSeq.SeqNet

@[expose] public section

/-!
# GeoSeq stage V9-2 (part 1): residue sequences (`def:residue`, `lem:residue-t0`, `lem:residue-rel`)

* `resSeq_apply`: the generator matrices `C_c = L_c P_{a_c}` of `resSeq` have the paper's entries
  `C_c[n][i] = v_c^{-1} θ^{n+1} [(z - a_c)^n] z^i / w_c(z)^{n+1}`, written as the coefficient of `t^n` in
  `(a_c + t)^i · w_c(a_c + t)^{-(n+1)}` (the form of the Palomar statement's `resGen`).
* `resSeq_digit` (`def:residue`, residue reading): digit `n` of coordinate `c` is
  `y_{c,n}(V) = v_c^{-1} Res_{a_c}(V (θ/w)^{n+1} dz)`.
* `resL_diag`, `resSeq_t0` (**`lem:residue-t0`**): `L_c[n][n] = v_c^{-1} θ^{n+1} / w'(a_c)^{n+1}`
  (`w'(a_c) = w_c(a_c)`), so `𝓡_v` is a digital `(0,s)`-sequence (`lem:t0`).
* `resSeq_skel`, `resSeq_skel_zero`, `resSeq_skel_top`, `resSeq_skel_shift` (**`lem:residue-rel`**, the
  skeleton relation): `∑_c v_c y_{c,K-1}(V) = θ^K [z^{sK-1}] V` for `deg V < sK`, so `0` for
  `deg V ≤ sK - 2`; and `∑_c v_c y_{c,K-1+i}(V) = 0` for every `i ≥ 0`, `deg V ≤ sK - 2`. Proof: the
  residue theorem `res_thm_of_deg` with `F = θ^K V / w^K`. `resSeq_skel_seq`: the same for the points of
  the digital sequence with index `< q^{sK-1}`.

The self-similarity clause of `lem:residue-t0` (multipliers `g_c = θ z_c'(θ x)/v_c`) needs
`lem:resform`(b) and is not formalized here (stage V9-8).
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F] {s : ℕ}

lemma ps_inv_pow (φ : PowerSeries F) (m : ℕ) : (φ ^ m)⁻¹ = (φ⁻¹) ^ m := by
  induction m with
  | zero => simp [ps_inv_one]
  | succ m ih => rw [pow_succ, PowerSeries.mul_inv_rev, ih, pow_succ, mul_comm]

lemma coeff_mul_range (φ ψ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (φ * ψ) =
      ∑ k ∈ range (n + 1), PowerSeries.coeff k φ * PowerSeries.coeff (n - k) ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma coeff_taylor_X_pow (a : F) (k i : ℕ) : (taylor a (X ^ i)).coeff k = pas a k i := by
  rw [taylor_X_pow, coeff_X_add_C_pow, pas, mul_comm]

/-- `placeCo` for equal pole orders `K` at every place is `w_c^K`. -/
lemma placeCo_const (a : Fin s → F) (K : ℕ) (c : Fin s) :
    placeCo a (fun _ => K) c = wCo a c ^ K := by
  rw [placeCo, wCo, Finset.prod_pow]

/-- **`def:residue`** (matrix form): `C_c[n][i] = v_c^{-1} θ^{n+1} [(z - a_c)^n] z^i / w_c(z)^{n+1}`, the
coefficient of `t^n` in `(a_c + t)^i · w_c(a_c + t)^{-(n+1)}`. -/
theorem resSeq_apply (a : Fin s → F) (θ : F) (v : Fin s → F) (c : Fin s) (n i : ℕ) :
    resSeq a θ v c n i = (v c)⁻¹ * θ ^ (n + 1) * PowerSeries.coeff n
      ((taylor (a c) (X ^ i) : PowerSeries F) *
        ((taylor (a c) (wCo a c) : PowerSeries F)⁻¹) ^ (n + 1)) := by
  rw [resSeq, scrGen, coeff_mul_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resL, Polynomial.coeff_coe, coeff_taylor_X_pow]
  ring

/-- **`def:residue`** (residue reading): digit `n` of coordinate `c` of the point with index digits
`f_0, …, f_{m-1}` is `y_{c,n}(V) = v_c^{-1} Res_{a_c}(V (θ/w)^{n+1} dz)
= v_c^{-1} θ^{n+1} Res_{a_c}(V / ((z - a_c)^{n+1} w_c^{n+1}) dz)`. -/
theorem resSeq_digit (a : Fin s → F) (θ : F) (v : Fin s → F) (f : ℕ → F) (m : ℕ) (c : Fin s)
    (n : ℕ) :
    ∑ j ∈ range m, resSeq a θ v c n j * f j =
      (v c)⁻¹ * θ ^ (n + 1) * locRes (a c) (n + 1) (vecPoly f m) (wCo a c ^ (n + 1)) := by
  rw [resSeq, scrGen_res, locRes, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, taylor_pow,
    Polynomial.coe_pow, ps_inv_pow, coeff_mul_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [locRes_one, resL, Polynomial.coeff_coe]
  ring

/-- The diagonal of the scramble (`lem:residue-t0`): `L_c[n][n] = v_c^{-1} θ^{n+1} w_c(a_c)^{-(n+1)}`. -/
theorem resL_diag (a : Fin s → F) (θ : F) (v : Fin s → F) (c : Fin s) (n : ℕ) :
    resL a θ v c n n = (v c)⁻¹ * θ ^ (n + 1) * ((wCo a c).eval (a c))⁻¹ ^ (n + 1) := by
  rw [resL, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    PowerSeries.constantCoeff_inv, constantCoeff_taylor]

lemma wCo_eval_ne (a : Fin s → F) (ha : Function.Injective a) (c : Fin s) :
    (wCo a c).eval (a c) ≠ 0 := by
  have := placeCo_eval_ne a ha (fun _ => 1) c
  rwa [placeCo_const, pow_one] at this

lemma resL_diag_ne (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (v : Fin s → F) (hv : ∀ c, v c ≠ 0) (c : Fin s) (n : ℕ) : resL a θ v c n n ≠ 0 := by
  rw [resL_diag]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hv c)) (pow_ne_zero _ hθ))
    (pow_ne_zero _ (inv_ne_zero (wCo_eval_ne a ha c)))

/-- **`lem:residue-t0`**: for distinct places, `θ ≠ 0` and a check vector in `(F^*)^s`, the residue
sequence `C_c = L_c P_{a_c}` is a digital `(0,s)`-sequence. -/
theorem resSeq_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q)
    (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) : IsSeq0 D (resSeq a θ v) :=
  t0 D a ha _ fun c n => resL_diag_ne a ha θ hθ v hv c n

lemma vecPoly_natDegree (f : ℕ → F) (m : ℕ) : (vecPoly f m).natDegree ≤ m - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [vecPoly_coeff, if_neg]
  have : m - 1 < j := by exact_mod_cast hj
  omega

/-- **`lem:residue-rel`** (skeleton relation, general form): for `K ≥ 1` and `deg V < m ≤ sK`,
`∑_c v_c y_{c,K-1}(V) = θ^K [z^{sK-1}] V`. -/
theorem resSeq_skel (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (f : ℕ → F) (m : ℕ) (hm : m ≤ s * K) :
    ∑ c, v c * ∑ j ∈ range m, resSeq a θ v c (K - 1) j * f j =
      θ ^ K * (vecPoly f m).coeff (s * K - 1) := by
  have hsK : 1 ≤ s * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hsum : ∑ c : Fin s, (fun _ => K) c = s * K := by simp
  have key := res_thm_of_deg a ha (fun _ => K) (vecPoly f m)
    (by rw [hsum]; have := vecPoly_natDegree f m; omega)
  rw [hsum] at key
  rw [← key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [resSeq_digit, Nat.sub_add_cancel hK, resAt, placeCo_const, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ (hv c), one_mul]

/-- **`lem:residue-rel`**, first case: `∑_c v_c y_{c,K-1}(V) = 0` for `deg V ≤ sK - 2`. -/
theorem resSeq_skel_zero (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (f : ℕ → F) (m : ℕ)
    (hm : m + 1 ≤ s * K) :
    ∑ c, v c * ∑ j ∈ range m, resSeq a θ v c (K - 1) j * f j = 0 := by
  rw [resSeq_skel a ha θ v hv K hK hs f m (by omega), vecPoly_coeff, if_neg (by omega), mul_zero]

/-- **`lem:residue-rel`**, second case: `∑_c v_c y_{c,K-1}(V) = θ^K [z^{sK-1}] V` for `deg V = sK - 1`
(index digits `f_0, …, f_{sK-1}`). -/
theorem resSeq_skel_top (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (f : ℕ → F) :
    ∑ c, v c * ∑ j ∈ range (s * K), resSeq a θ v c (K - 1) j * f j = θ ^ K * f (s * K - 1) := by
  have hsK : 1 ≤ s * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [resSeq_skel a ha θ v hv K hK hs f _ le_rfl, vecPoly_coeff, if_pos (by omega)]

/-- **`lem:residue-rel`**, "moreover": `∑_c v_c y_{c,K-1+i}(V) = 0` for every `i ≥ 0` and
`deg V ≤ sK - 2`. -/
theorem resSeq_skel_shift (a : Fin s → F) (ha : Function.Injective a) (θ : F) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) (i : ℕ) (f : ℕ → F) (m : ℕ)
    (hm : m + 1 ≤ s * K) :
    ∑ c, v c * ∑ j ∈ range m, resSeq a θ v c (K - 1 + i) j * f j = 0 := by
  have h := resSeq_skel_zero a ha θ v hv (K + i) (by omega) hs f m
    (le_trans hm (Nat.mul_le_mul_left s (by omega)))
  rwa [show K + i - 1 = K - 1 + i by omega] at h

/-- The skeleton relation for the points of the digital sequence: for `K ≥ 1` and every index
`x < q^{sK-1}` (the prefix `P_{sK-1}`), `∑_c v_c y_{c,K-1}(x) = 0`. -/
theorem resSeq_skel_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (v : Fin s → F) (hv : ∀ c, v c ≠ 0) (K : ℕ) (hK : 1 ≤ K)
    (hs : 1 ≤ s) (x : ℕ) (hx : x < q ^ (s * K - 1)) :
    ∑ c, v c * seqDigit D (resSeq a θ v) x c (K - 1) = 0 := by
  have hsK : 1 ≤ s * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdig : ∀ c, seqDigit D (resSeq a θ v) x c (K - 1) =
      ∑ j ∈ range (s * K - 1), resSeq a θ v c (K - 1) j * idxDigit D x j := fun c =>
    seqDigit_eq_range D _ x c _ _ fun j hj => idxDigit_eq_zero D x j
      (digit_high x j (lt_of_lt_of_le hx (Nat.pow_le_pow_right (NeZero.pos q) hj)))
  simp_rw [hdig]
  exact resSeq_skel_zero a ha θ v hv K hK hs _ _ (by omega)

end GeoSeq
