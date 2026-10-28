/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Sobol

@[expose] public section

/-!
# GeoSeq stage V9-5 (part 5): the explicit close pairs of `cor:sobol`

With the van der Corput coordinate as `ĉ` (`b_ĉ = z`, `e = 1`, `π = 1`, so `g = g' = 1`, `g̃ = 0`) and `k = 2^j ≥ ν`:

* `thetaP_coeff_zero`, `sobol_hTheta`: `Θ(0) = 1`, hence `Θ^{2^j} ≡ 1 (mod z^{2^j})` (Frobenius over `𝔽_2`), which is
  all `thm:nonqu` needs about `k`; `expand_two_pow`: `Θ^{2^m} = Θ(z^{2^m})`.
* `polyIdx_add_two`: addition in `𝔽_2[z]` is the XOR of the integer indices.
* `nonquV1_vdc`: `V_1 = z^{Qη+1} S_{Qν-1} = ∑_{i = Qη+1}^{L_Q - 1} z^i`.
* **`sobol_pair`** (`cor:sobol`, explicit pairs): `ι(V_1)`, `ι(V_2) = ι(V_1) XOR ι(D_Q)` are distinct, `< 2^{m_Q}`, and the
  two Sobol' points are at distance `< √(s+3) 2^{-L_Q}`, `D_Q = z^{Qη} S_{Qν} Θ^{Q 2^j}`, `L_Q = Q E (2^j+1)`,
  `m_Q = Q(sE(2^j+1) - (s-1)E)`; the pairs do not depend on the direction numbers.
-/

namespace GeoSeq

open Finset Polynomial

variable {s : ℕ}

lemma expand_two_pow (f : (ZMod 2)[X]) : ∀ m : ℕ, expand (ZMod 2) (2 ^ m) f = f ^ (2 ^ m)
  | 0 => by simp
  | m + 1 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [pow_succ, expand_mul, ZMod.expand_card, map_pow, expand_two_pow f m, ← pow_mul]

lemma thetaP_coeff_zero (b : Fin s → (ZMod 2)[X]) (ch : Fin s) (hb0 : ∀ c, c ≠ ch → (b c).coeff 0 = 1) :
    (thetaP b ch).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, thetaP, eval_prod]
  exact Finset.prod_eq_one fun c hc => by
    rw [eval_pow, ← coeff_zero_eq_eval_zero, hb0 c (Finset.ne_of_mem_erase hc), one_pow]

/-- `Θ(0) = 1` gives `Θ^{2^j} ≡ 1 (mod z^ν)` for `ν ≤ 2^j` (over `𝔽_2`). -/
lemma sobol_hTheta (b : Fin s → (ZMod 2)[X]) (ch : Fin s) (hb0 : ∀ c, c ≠ ch → (b c).coeff 0 = 1)
    (ν j : ℕ) (hνj : ν ≤ 2 ^ j) : (X : (ZMod 2)[X]) ^ ν ∣ thetaP b ch ^ (2 ^ j) - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : (X : (ZMod 2)[X]) ∣ thetaP b ch - 1 := by
    rw [X_dvd_iff, coeff_sub, coeff_one_zero, thetaP_coeff_zero b ch hb0, sub_self]
  have h := sub_pow_char_pow (thetaP b ch) 1 j (p := 2)
  rw [one_pow] at h
  rw [← h]
  exact (pow_dvd_pow X hνj).trans (pow_dvd_pow_of_dvd hX _)

lemma zmod2_val_add (x y : ZMod 2) : ((x + y).val = 1) = Bool.xor (decide (x.val = 1)) (decide (y.val = 1)) := by
  revert x y; decide

lemma polyIdx_digit_two (V : (ZMod 2)[X]) (k : ℕ) : polyIdx 2 V / 2 ^ k % 2 = (V.coeff k).val := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [polyIdx_digit]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), ZMod.val_zero]

/-- Addition in `𝔽_2[z]` is the XOR of the integer indices. -/
theorem polyIdx_add_two (V W : (ZMod 2)[X]) : polyIdx 2 (V + W) = polyIdx 2 V ^^^ polyIdx 2 W := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq, polyIdx_digit_two, polyIdx_digit_two, polyIdx_digit_two, coeff_add]
  generalize V.coeff k = x; generalize W.coeff k = y; revert x y; decide

/-- `V_1 = z^{Qη+1} S_{Qν-1} = ∑_{i=Qη+1}^{Q(η+ν)-1} z^i` for the van der Corput coordinate (`b = z`, `g̃ = 0`, `g' = 1`). -/
lemma nonquV1_vdc (b : Fin s → (ZMod 2)[X]) (ch : Fin s) (hch : b ch = X) (ν η Q : ℕ) :
    nonquV1 b ch 0 (-1) ν η Q = ∑ i ∈ Finset.Ico (Q * η + 1) (Q * (η + ν)), X ^ i := by
  rw [nonquV1, carryV1, hch, runS, zero_mul, zero_add, show (-1 : (ZMod 2)[X]) = 1 from by
      ext n; rw [coeff_neg, coeff_one]; split_ifs <;> decide, one_mul,
    Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by first | rfl | (congr 1; omega)) fun i _ => by rw [← pow_add]

/-- **`cor:sobol`, the explicit pairs** (van der Corput coordinate as `ĉ`): let `b_ĉ = z`, let `ν ≥ 1` with
`(1 + z) Θ ∣ z^ν - 1` (`carryR`), `ν ≤ 2^j`, `η = E(2^j+1) - ν`, `Q = 2^w`. Then for every Sobol' sequence with these
polynomials (any admissible direction numbers) the indices `ι(V_1)` and `ι(V_1 + D_Q) = ι(V_1) XOR ι(D_Q)`,
`V_1 = ∑_{i = Qη+1}^{L_Q - 1} z^i`, `D_Q = z^{Qη} S_{Qν} Θ^{Q 2^j}`, are distinct and `< 2^{m_Q}`, and the two points
are at Euclidean distance `< √(s+3) 2^{-L_Q}`. -/
theorem sobol_pair (hs : 2 ≤ s) (b : Fin s → (ZMod 2)[X]) (u : Fin s → ℕ → ℕ)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (hco : ∀ c, SobolCoord (b c) (u c)) (ch : Fin s)
    (hch : b ch = X) (ν j η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ X ^ ν - 1) (hνj : ν ≤ 2 ^ j)
    (hη : η + ν = lcmDeg b * (2 ^ j + 1)) (w : ℕ) :
    polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w)) <
        2 ^ (2 ^ w * (s * lcmDeg b * (2 ^ j + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) <
        2 ^ (2 ^ w * (s * lcmDeg b * (2 ^ j + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w)) ≠
        polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) ∧
      polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) =
        polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w)) ^^^ polyIdx 2 (nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) ∧
      euclDist (seqPoint (zcode 2) (sobolGen u) (polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w))))
        (seqPoint (zcode 2) (sobolGen u)
          (polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)))) <
        Real.sqrt (s + 3) / (2 : ℝ) ^ (2 ^ w * lcmDeg b * (2 ^ j + 1)) := by
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := fun c => (sobolCoord_radInv (hco c)).1
  have hb0 : ∀ c, c ≠ ch → (b c).coeff 0 = 1 := by
    intro c hc
    rcases hco c with ⟨hX, -⟩ | ⟨-, h0, -⟩
    · exfalso
      obtain ⟨x, y, hxy⟩ := hcop hc
      rw [hX, hch] at hxy
      have := congrArg (fun f => f.coeff 0) hxy
      simp at this
    · exact h0
  have hrad : IsRadInv (sobY (u ch)) (b ch) (fun a _ => a.coeff 0) := by
    rcases hco ch with ⟨hX, hu⟩ | ⟨-, h0, -⟩
    · rw [hX]; exact vdc_radInv _ hu
    · rw [hch] at h0; simp at h0
  have he : (b ch).natDegree = 1 := by rw [hch, natDegree_X]
  have hpts : seqPoint (zcode 2) (sobolGen u) = linPt 2 (fun c => sobY (u c)) := by
    rw [seqPoint_eq_linPt]; rfl
  obtain ⟨k1, k2, k3, k4⟩ := nonqu_pair hs (fun c => sobY (u c)) (fun c => sobY_lin (u c)) b hdeg ch
    (fun c _ => by
      obtain ⟨π', hπ'⟩ := (sobolCoord_radInv (hco c)).2
      exact hπ'.isBAdic (hdeg c) (sobY_lin (u c)))
    _ hrad 1 0 (-1) (by rw [he, natDegree_one]; omega) (by rw [he, natDegree_zero]; omega)
    (by rw [he, natDegree_neg, natDegree_one]; omega)
    (fun i hi => by rw [he] at hi; obtain rfl : i = 0 := (by omega); simp <;> decide)
    (fun i hi => by rw [he] at hi; obtain rfl : i = 0 := (by omega); simp <;> decide)
    (fun i hi => by rw [he] at hi; obtain rfl : i = 0 := (by omega); simp <;> decide)
    ν (2 ^ j) η hν (by rwa [hch]) (by rw [hch]; exact sobol_hTheta b ch hb0 ν j hνj)
    (by rw [he, Nat.div_one]; exact hη) w
  rw [hpts]
  exact ⟨k1, k2, k3, polyIdx_add_two _ _, k4⟩

end GeoSeq
