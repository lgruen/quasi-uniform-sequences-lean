/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# GeoSeq stage S0 proof: `lem:prefix`, the separation half

If every full level `P_{sK}` (`K ≥ 1`) has `c(P_{sK}) ≥ LB ≥ 0`, then
`δ(P_{[N]}) ≥ (LB/q) N^{-1/s}` for every `N ≥ 2` (`prefix_sep`). As in the paper's proof: for
`q^{sK} ≤ N < q^{s(K+1)}` the first `N` points lie in `P_{s(K+1)}`, and `N^{-1/s} ≤ q^{-K}`.
The covering half of `lem:prefix` is not part of this file.
-/

namespace GeoSeq

/-- **`lem:prefix`** (separation half): full-level separation `LB` for all `K ≥ 1` gives
`δ(P_{[N]}) ≥ (LB/q) · N^{-1/s}` for all `N ≥ 2`. -/
theorem prefix_sep (q s : ℕ) (hq : 2 ≤ q) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ) (LB : ℝ)
    (hLB : 0 ≤ LB) (h : ∀ K : ℕ, 1 ≤ K → SepAtLevel q s K pt LB) :
    SepAllN s pt (LB / q) := by
  intro N hN v w hv hw hvw
  set k := Nat.log q N with hk
  set K := k / s with hK
  have hq1 : 1 < q := by omega
  have hNle : q ^ (s * K) ≤ N := by
    have h1 : q ^ (s * K) ≤ q ^ k := Nat.pow_le_pow_right (by omega) (Nat.mul_div_le k s)
    exact h1.trans (Nat.pow_log_le_self q (by omega))
  have hNlt : N < q ^ (s * (K + 1)) := by
    have h1 : N < q ^ (k + 1) := Nat.lt_pow_succ_log_self hq1 N
    have h2 : k + 1 ≤ s * (K + 1) := by
      have := Nat.lt_mul_div_succ k (show 0 < s by omega)
      rw [hK]; linarith
    exact h1.trans_le (Nat.pow_le_pow_right (by omega) h2)
  have hsep := h (K + 1) (Nat.succ_pos K) v w (hv.trans hNlt) (hw.trans hNlt) hvw
  -- `N^{-1/s} ≤ q^{-K}`
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : (q : ℝ) ^ K ≤ (N : ℝ) ^ (1 / (s : ℝ)) := by
    have e1 : ((q : ℝ) ^ K) = (((q : ℝ) ^ K) ^ s) ^ ((s : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) (by omega)).symm
    rw [e1, one_div]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [← pow_mul, mul_comm]
    exact_mod_cast hNle
  have hNs : (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ ((q : ℝ) ^ K)⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ (by positivity) hroot
  have hd0 : 0 ≤ Z3NetDGS.torDist2 (pt v) (pt w) := Real.sqrt_nonneg _
  calc LB / q * (N : ℝ) ^ (-(1 / (s : ℝ)))
      ≤ LB / q * ((q : ℝ) ^ K)⁻¹ := by
        apply mul_le_mul_of_nonneg_left hNs (div_nonneg hLB hqpos.le)
    _ = LB / (q : ℝ) ^ (K + 1) := by
        rw [pow_succ]; field_simp
    _ ≤ Z3NetDGS.torDist2 (pt v) (pt w) := by
        rw [div_le_iff₀ (by positivity)]
        linarith [hsep]

end GeoSeq
