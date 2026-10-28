/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.T0

@[expose] public section

/-!
# GeoSeq stage S1: self-similar scrambles are scrambled frames; `t = 0` of `thm:WF`, `thm:B2`

* `ss_eq_scr`: `C_c[n][k] = [x^n] g_c z_c^k` equals `(L_c P_{a_c})[n][k]` with `a_c = z_c(0)` and
  `L_c[n][i] = [x^n] g_c (z_c - a_c)^i` (binomial expansion of `z_c^k = ((z_c - a_c) + a_c)^k`);
  `L_c` is lower triangular (`x^i ∣ (z_c - a_c)^i`) with diagonal `g_c(0) · ([x^1] z_c)^n`
  (`ssScr_diag`).
* `ss_t0`: distinct places, `g_c(0) ≠ 0`, `[x^1] z_c ≠ 0` ⟹ `(0,s)`-sequence (by `lem:t0`).
* `WF_net` (`thm:WF`, `t = 0`) and `B2_net` (`thm:B2`, `t = 0`).
-/

namespace GeoSeq

open Finset PowerSeries

variable {R : Type*} [CommRing R] {s : ℕ}

lemma coeff_mul_pow_eq_zero (g w : PowerSeries R) (hw : constantCoeff w = 0) (n i : ℕ)
    (h : n < i) : coeff n (g * w ^ i) = 0 := by
  obtain ⟨w', rfl⟩ := X_dvd_iff.mpr hw
  rw [mul_pow, ← mul_assoc, mul_comm g, mul_assoc, coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

lemma coeff_mul_pow_self (g w : PowerSeries R) (hw : constantCoeff w = 0) (n : ℕ) :
    coeff n (g * w ^ n) = constantCoeff g * coeff 1 w ^ n := by
  obtain ⟨w', rfl⟩ := X_dvd_iff.mpr hw
  rw [mul_pow, ← mul_assoc, mul_comm g, mul_assoc, coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h' => absurd le_rfl h'),
    Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
    show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]

/-- **Self-similar scrambles are scrambled frames** (`def:selfsim`, `lem:t0`):
`ssGen g zθ = scrGen (ssPlace zθ) (ssScr g zθ)`. -/
theorem ss_eq_scr (g zθ : Fin s → PowerSeries R) :
    ssGen g zθ = scrGen (ssPlace zθ) (ssScr g zθ) := by
  funext c n k
  set a := constantCoeff (zθ c)
  set w := zθ c - C a with hw
  have hw0 : constantCoeff w = 0 := by simp [w, a]
  have hz : zθ c = w + C a := by simp [w]
  simp only [ssGen, scrGen, ssPlace, ssScr, pas]
  have hterm : ∀ i ∈ range (k + 1), coeff n (g c * (w ^ i * C a ^ (k - i) * (k.choose i : PowerSeries R))) =
      coeff n (g c * w ^ i) * ((k.choose i : R) * a ^ (k - i)) := by
    intro i _
    rw [show (k.choose i : PowerSeries R) = C (k.choose i : R) from (map_natCast C _).symm,
      ← map_pow, show g c * (w ^ i * C (a ^ (k - i)) * C (k.choose i : R)) =
        g c * w ^ i * C ((k.choose i : R) * a ^ (k - i)) by rw [map_mul]; ring, coeff_mul_C]
  have hL : coeff n (g c * zθ c ^ k) =
      ∑ i ∈ range (k + 1), coeff n (g c * w ^ i) * ((k.choose i : R) * a ^ (k - i)) := by
    rw [hz, add_pow, Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl hterm
  rw [hL]
  have e1 : ∑ i ∈ range (k + 1), coeff n (g c * w ^ i) * ((k.choose i : R) * a ^ (k - i)) =
      ∑ i ∈ range (n + k + 1), coeff n (g c * w ^ i) * ((k.choose i : R) * a ^ (k - i)) := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega))
    · intro i hi
      simp only [mem_sdiff, mem_range] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    · intro i _; rfl
  have e2 : ∑ i ∈ range (n + 1), coeff n (g c * w ^ i) * ((k.choose i : R) * a ^ (k - i)) =
      ∑ i ∈ range (n + k + 1), coeff n (g c * w ^ i) * ((k.choose i : R) * a ^ (k - i)) := by
    apply Finset.sum_subset_zero_on_sdiff (Finset.range_subset_range.mpr (by omega))
    · intro i hi
      simp only [mem_sdiff, mem_range] at hi
      rw [coeff_mul_pow_eq_zero _ _ hw0 n i (by omega), zero_mul]
    · intro i _; rfl
  exact e1.trans e2.symm

/-- The diagonal of the scramble of a self-similar scramble: `L_c[n][n] = g_c(0) ([x^1] z_c)^n`. -/
theorem ssScr_diag (g zθ : Fin s → PowerSeries R) (c : Fin s) (n : ℕ) :
    ssScr g zθ c n n = constantCoeff (g c) * coeff 1 (zθ c) ^ n := by
  unfold ssScr
  rw [coeff_mul_pow_self _ _ (by simp)]
  simp

/-- **Self-similar scrambles have `t = 0`** (`lem:t0`): distinct places `z_c(0)`, `g_c(0) ≠ 0` and
`[x^1] z_c ≠ 0`. -/
theorem ss_t0 {K : Type*} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [NeZero q]
    (D : DigitCode K q) (g zθ : Fin s → PowerSeries K)
    (hplace : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hz : ∀ c, coeff 1 (zθ c) ≠ 0) : IsSeq0 D (ssGen g zθ) := by
  rw [ss_eq_scr]
  exact t0 D _ hplace _ fun c n => by
    rw [ssScr_diag]; exact mul_ne_zero (hg c) (pow_ne_zero _ (hz c))

end GeoSeq
