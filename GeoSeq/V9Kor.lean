/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Thm

@[expose] public section

/-!
# GeoSeq stage V9-2 (part 4): `cor:korobov`, `cor:residueQU`

* `korRho_pow_le`, `lt_korRho_succ_pow`, `korRho_pow_lt`: `ρ^s ≤ p < (ρ+1)^s`, and `ρ^s < p` for prime
  `p`, `s ≥ 2` (`p` is not an `s`-th power); `korRho_two_le_iff` (`ρ ≥ 2 ⟺ p > 2^s`),
  `korRho_three_le_iff` (`ρ ≥ 3 ⟺ p > 3^s`).
* `korobov_lat`, `korobov_jit`, `korobov_ljit` (**`cor:korobov`**, the integer lemma): every nonzero
  `b ∈ Λ_v`, `v = (ρ, …, ρ^{s-1}, -1)`, has a coordinate `|b_c| ≥ ρ`, so `ℓ_jit(Λ_v) ≥ ρ - 1`
  (`T = ∑_{c<s-1} ρ^{c+1} b_c - b_{s-1}` has `|T| ≤ ρ^s - 1 < p`, so `T = 0`, and balanced base-`ρ` digits
  of `0` vanish).
* `korobov_sep` (**`cor:korobov`**): `sep(P_{sK-1}) ≥ (ρ - 1) p^{-1/s}` for every `K ≥ 1` (written out for
  distinct indices `< p^{sK-1}`); `korobov_forms`: `> max(1 - 2p^{-1/s}, (ρ-1)/(ρ+1))`, `> 1/3` for
  `p > 2^s`, `> 1/2` for `p > 3^s`.
* `residue_allN`, `residue_mesh` (**`cor:residueQU`**): with `LB = p^{-1/s} L > 0`,
  `δ(P_{[N]}) ≥ (LB/p) N^{-1/s}` and `h/δ ≤ √s p²/LB` for every `N ≥ 2` (quasi-uniform);
  `jit_exists_iff`: a check vector with `ℓ_jit(Λ_v) > 0` exists iff `p > 2^s` (`small_vec`: for `p < 2^s`
  every `Λ_v` contains a nonzero `e ∈ {-1,0,1}^s`).
* `residue_korobov` (headline form): Faure places, `θ = 1`, Korobov vector, `p > 2^s`: `(0,s)`, the
  separation of every `P_{sK-1}`, the all-`N` separation and the bounded mesh ratio; `resSeq_faure_apply`
  (the generator matrices in the Palomar statement's `resGen` form).
-/

namespace GeoSeq

open Finset Polynomial

variable {p s : ℕ}

/-! ## `ρ = ⌊p^{1/s}⌋` -/

lemma korRho_pow_le (hs : 1 ≤ s) : korRho p s ^ s ≤ p := by
  have h1 : ((korRho p s : ℕ) : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / s) := Nat.floor_le (by positivity)
  have : ((korRho p s : ℝ)) ^ s ≤ ((p : ℝ) ^ ((1 : ℝ) / s)) ^ s :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) h1 s
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)] at this
  exact_mod_cast this

lemma lt_korRho_succ_pow (hs : 1 ≤ s) : p < (korRho p s + 1) ^ s := by
  have h1 : (p : ℝ) ^ ((1 : ℝ) / s) < (korRho p s : ℝ) + 1 := Nat.lt_floor_add_one _
  have : ((p : ℝ) ^ ((1 : ℝ) / s)) ^ s < ((korRho p s : ℝ) + 1) ^ s :=
    pow_lt_pow_left₀ h1 (by positivity) (by omega)
  rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)] at this
  exact_mod_cast this

lemma korRho_pos (hp : 1 ≤ p) (hs : 1 ≤ s) : 1 ≤ korRho p s := by
  by_contra h
  have h0 : korRho p s = 0 := by omega
  have := lt_korRho_succ_pow (p := p) hs
  rw [h0, zero_add, one_pow] at this
  omega

lemma korRho_pow_lt [Fact p.Prime] (hs : 2 ≤ s) : korRho p s ^ s < p := by
  have hpr : p.Prime := Fact.out
  rcases (korRho_pow_le (p := p) (s := s) (by omega)).lt_or_eq with h | h
  · exact h
  exfalso
  have hdvd : korRho p s ∣ p :=
    ⟨korRho p s ^ (s - 1), by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ s)]; exact h.symm⟩
  rcases hpr.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · rw [h1, one_pow] at h; exact hpr.one_lt.ne h
  · rw [h1] at h
    have : p ^ 1 < p ^ s := Nat.pow_lt_pow_right hpr.one_lt (by omega)
    rw [pow_one] at this; omega

lemma korRho_two_le_iff [Fact p.Prime] (hs : 2 ≤ s) : 2 ≤ korRho p s ↔ 2 ^ s < p := by
  constructor
  · intro h
    exact lt_of_le_of_lt (Nat.pow_le_pow_left h s) (korRho_pow_lt hs)
  · intro h
    by_contra h'
    have h1 := lt_korRho_succ_pow (p := p) (s := s) (by omega)
    have h2 : (korRho p s + 1) ^ s ≤ 2 ^ s := Nat.pow_le_pow_left (by omega) s
    omega

lemma korRho_three_le_iff [Fact p.Prime] (hs : 2 ≤ s) : 3 ≤ korRho p s ↔ 3 ^ s < p := by
  constructor
  · intro h
    exact lt_of_le_of_lt (Nat.pow_le_pow_left h s) (korRho_pow_lt hs)
  · intro h
    by_contra h'
    have h1 := lt_korRho_succ_pow (p := p) (s := s) (by omega)
    have h2 : (korRho p s + 1) ^ s ≤ 3 ^ s := Nat.pow_le_pow_left (by omega) s
    omega

lemma korobov_eq (c : Fin s) :
    korobov p s c = if (c : ℕ) + 1 < s then ((korRho p s ^ ((c : ℕ) + 1) : ℕ) : ZMod p) else -1 :=
  rfl

/-- The Korobov vector is a check vector: all entries are nonzero in `𝔽_p`. -/
lemma korobov_ne_zero [Fact p.Prime] (hs : 2 ≤ s) (c : Fin s) : korobov p s c ≠ 0 := by
  have hpr : p.Prime := Fact.out
  rw [korobov_eq]
  split_ifs with h
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have hρ := korRho_pos (p := p) hpr.one_lt.le (by omega : 1 ≤ s)
    have h1 : korRho p s ^ ((c : ℕ) + 1) ≤ korRho p s ^ s := Nat.pow_le_pow_right hρ (by omega)
    have h2 := Nat.le_of_dvd (pow_pos hρ _) hd
    have := korRho_pow_lt (p := p) hs
    omega
  · exact neg_ne_zero.mpr one_ne_zero

/-! ## Balanced digits -/

lemma balanced_zero (ρ : ℤ) (hρ : 0 < ρ) : ∀ (n : ℕ) (d : ℕ → ℤ), (∀ j < n, |d j| < ρ) →
    ∑ j ∈ range n, ρ ^ j * d j = 0 → ∀ j < n, d j = 0
  | 0 => fun _ _ _ j hj => absurd hj (Nat.not_lt_zero j)
  | n + 1 => by
    intro d hd hsum j hj
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, one_mul, pow_succ] at hsum
    have hfac : ∑ i ∈ range n, ρ ^ i * ρ * d (i + 1) = ρ * ∑ i ∈ range n, ρ ^ i * d (i + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfac] at hsum
    have h0 : d 0 = 0 := Int.eq_zero_of_abs_lt_dvd ⟨-∑ i ∈ range n, ρ ^ i * d (i + 1), by linarith⟩
      (hd 0 (by omega))
    have hrest : ∑ i ∈ range n, ρ ^ i * d (i + 1) = 0 := by
      rw [h0, add_zero] at hsum
      exact (mul_eq_zero.mp hsum).resolve_left hρ.ne'
    have ih := balanced_zero ρ hρ n (fun i => d (i + 1)) (fun i hi => hd (i + 1) (by omega)) hrest
    rcases j with _ | j
    · exact h0
    · exact ih j (by omega)

lemma balanced_bound (ρ : ℤ) (hρ : 1 ≤ ρ) (n : ℕ) (d : ℕ → ℤ) (hd : ∀ j < n, |d j| ≤ ρ - 1) :
    |∑ j ∈ range n, ρ ^ j * d j| ≤ ρ ^ n - 1 := by
  calc |∑ j ∈ range n, ρ ^ j * d j| ≤ ∑ j ∈ range n, |ρ ^ j * d j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, ρ ^ j * (ρ - 1) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_pos (pow_pos (by omega) j)]
        exact mul_le_mul_of_nonneg_left (hd j (Finset.mem_range.mp hj)) (pow_pos (by omega) j).le
    _ = ρ ^ n - 1 := by rw [← Finset.sum_mul, geom_sum_mul]

/-! ## `cor:korobov` -/

/-- The integer lemma of `cor:korobov`: a vector of `Λ_v` (Korobov `v`) with all `|b_c| ≤ ρ - 1` is `0`. -/
theorem korobov_lat [Fact p.Prime] (hs : 2 ≤ s) (b : Fin s → ℤ) (hlat : InLat (korobov p s) b)
    (hb : ∀ c, |b c| ≤ (korRho p s : ℤ) - 1) : b = 0 := by
  have hpr : p.Prime := Fact.out
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  set ρ : ℕ := korRho p (t + 1) with hρdef
  have hρ1 : 1 ≤ ρ := korRho_pos hpr.one_lt.le (by omega)
  set B : ℕ → ℤ := fun j => if h : j < t + 1 then b ⟨j, h⟩ else 0 with hB
  set κ : ℕ → ℤ := fun j => if j + 1 < t + 1 then (ρ : ℤ) ^ (j + 1) else -1 with hκ
  have hBb : ∀ c : Fin (t + 1), B c = b c := fun c => by simp only [hB, dif_pos c.isLt]
  have hBbd : ∀ j, |B j| ≤ (ρ : ℤ) - 1 := fun j => by
    by_cases h : j < t + 1
    · simp only [hB, h, dite_true]; exact hb _
    · simp only [hB, h, dite_false, abs_zero]; omega
  -- the lattice relation as an integer congruence
  set T : ℤ := ∑ j ∈ range (t + 1), κ j * B j with hT
  have hTp : ((T : ℤ) : ZMod p) = 0 := by
    unfold InLat at hlat
    rw [hT, Int.cast_sum, ← Fin.sum_univ_eq_sum_range (fun j => ((κ j * B j : ℤ) : ZMod p))]
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hlat
    rw [hBb, korobov_eq, Int.cast_mul]
    simp only [hκ]
    split_ifs <;> push_cast <;> rfl
  have hdvd : (p : ℤ) ∣ T := (ZMod.intCast_zmod_eq_zero_iff_dvd T p).mp hTp
  -- `T` in balanced base `ρ`
  set d : ℕ → ℤ := fun j => if j = 0 then -B t else B (j - 1) with hd
  have hTd : T = ∑ j ∈ range (t + 1), (ρ : ℤ) ^ j * d j := by
    rw [hT, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [hκ, hd, lt_irrefl, if_false, Nat.succ_ne_zero, Nat.add_sub_cancel, pow_zero, one_mul,
      if_true]
    have : ∀ j ∈ range t, (if j + 1 < t + 1 then (ρ : ℤ) ^ (j + 1) else -1) * B j =
        (ρ : ℤ) ^ (j + 1) * B j := fun j hj => by
      rw [if_pos (by simp at hj; omega)]
    rw [Finset.sum_congr rfl this]
    ring
  have hdbd : ∀ j < t + 1, |d j| ≤ (ρ : ℤ) - 1 := fun j _ => by
    simp only [hd]; split_ifs
    · rw [abs_neg]; exact hBbd t
    · exact hBbd _
  have hTbd : |T| < p := by
    rw [hTd]
    have h1 := balanced_bound (ρ : ℤ) (by exact_mod_cast hρ1) (t + 1) d hdbd
    have h2 : ρ ^ (t + 1) < p := korRho_pow_lt (by omega)
    have h3 : ((ρ : ℤ)) ^ (t + 1) < p := by exact_mod_cast h2
    omega
  have hT0 : T = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hTbd
  have hdz := balanced_zero (ρ : ℤ) (by exact_mod_cast hρ1) (t + 1) d
    (fun j hj => by have := hdbd j hj; omega) (hTd ▸ hT0)
  funext c
  rw [Pi.zero_apply, ← hBb]
  by_cases hc : (c : ℕ) = t
  · have := hdz 0 (by omega)
    simp only [hd, if_true] at this
    rw [hc]; omega
  · have := hdz ((c : ℕ) + 1) (by omega)
    simp only [hd, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at this
    exact this

/-- **`cor:korobov`**: `ℓ_jit(Λ_v) ≥ ρ - 1` for the Korobov vector: every nonzero lattice vector has
`‖(|b| - 𝟏)_+‖_2 ≥ ρ - 1`. -/
theorem korobov_jit [Fact p.Prime] (hs : 2 ≤ s) (b : Fin s → ℤ) (hb : b ≠ 0)
    (hlat : InLat (korobov p s) b) : (korRho p s : ℝ) - 1 ≤ jitNorm b := by
  obtain ⟨c, hc⟩ : ∃ c, (korRho p s : ℤ) - 1 < |b c| := by
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hb (korobov_lat hs b hlat h)
  have hc' : (korRho p s : ℝ) ≤ |(b c : ℝ)| := by
    have : (korRho p s : ℤ) ≤ |b c| := by omega
    exact_mod_cast this
  unfold jitNorm
  calc (korRho p s : ℝ) - 1 ≤ max (|(b c : ℝ)| - 1) 0 := le_max_of_le_left (by linarith)
    _ = Real.sqrt ((max (|(b c : ℝ)| - 1) 0) ^ 2) := (Real.sqrt_sq (le_max_right _ _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun c => (max (|(b c : ℝ)| - 1) 0) ^ 2)
        (fun _ _ => sq_nonneg _) (mem_univ c))

theorem korobov_ljit [Fact p.Prime] (hs : 2 ≤ s) : (korRho p s : ℝ) - 1 ≤ ljit (korobov p s) :=
  le_ljit (by omega) _ _ (korobov_jit hs)

/-- **`cor:korobov`**: for the Korobov vector, any two distinct points among the first `N = p^{sK-1}` points
have toroidal distance `≥ (ρ - 1) p^{-1/s} N^{-1/s}`, i.e. `sep(P_{sK-1}) ≥ (ρ - 1) p^{-1/s}`, every `K ≥ 1`. -/
theorem korobov_sep [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (K : ℕ) (hK : 1 ≤ K) (x y : ℕ) (hx : x < p ^ (s * K - 1))
    (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) * ((p ^ (s * K - 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / s) ≤
      Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq a θ (korobov p s)) x)
        (seqPoint (zcode p) (resSeq a θ (korobov p s)) y) := by
  have h := residue_sepAtPrefix hs a ha θ hθ (korobov p s) (korobov_ne_zero hs) _
    (korobov_jit hs) K hK x y hx hy hxy
  rw [neg_div]
  push_cast
  calc ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))
      = (p : ℝ) ^ (-(1 / (s : ℝ))) * ((korRho p s : ℝ) - 1) *
          ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ))) := by ring
    _ ≤ _ := h

/-- `cor:korobov`, the paper's form `sep(P_{sK-1}) ≥ (ρ - 1) p^{-1/s}` (`SepAtPrefix`). -/
theorem korobov_sepAtPrefix [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p)
    (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0) (K : ℕ) (hK : 1 ≤ K) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) (resSeq a θ (korobov p s)))
      (((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ)))) := by
  intro x y hx hy hxy
  have h := residue_sepAtPrefix hs a ha θ hθ (korobov p s) (korobov_ne_zero hs) _
    (korobov_jit hs) K hK x y hx hy hxy
  calc ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) * ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ)))
      = (p : ℝ) ^ (-(1 / (s : ℝ))) * ((korRho p s : ℝ) - 1) *
          ((p : ℝ) ^ (s * K - 1)) ^ (-(1 / (s : ℝ))) := by ring
    _ ≤ _ := h

/-- **`cor:korobov`** (comparison forms): for `p > 2^s`,
`(ρ - 1) p^{-1/s} > max(1 - 2p^{-1/s}, (ρ-1)/(ρ+1))` and `> 1/3`; for `p > 3^s` also `> 1/2`. -/
theorem korobov_forms [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    1 - 2 * (p : ℝ) ^ (-(1 : ℝ) / s) < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) ∧
      ((korRho p s : ℝ) - 1) / ((korRho p s : ℝ) + 1) <
        ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) ∧
      1 / 3 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) ∧
      (3 ^ s < p → 1 / 2 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hρ2 : (2 : ℝ) ≤ korRho p s := by exact_mod_cast (korRho_two_le_iff hs).mpr hps
  set r := (p : ℝ) ^ ((1 : ℝ) / s) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  have hlt : r < (korRho p s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hinv : (p : ℝ) ^ (-(1 : ℝ) / s) = r⁻¹ := by
    rw [neg_div, Real.rpow_neg (by positivity)]
  rw [hinv]
  set ρ : ℝ := (korRho p s : ℝ) with hρ
  have hb : (ρ - 1) / (ρ + 1) < (ρ - 1) * r⁻¹ := by
    rw [← div_eq_mul_inv]
    exact div_lt_div_of_pos_left (by linarith) hrpos hlt
  refine ⟨?_, hb, ?_, fun h3 => ?_⟩
  · rw [← div_eq_mul_inv, ← div_eq_mul_inv, lt_div_iff₀ hrpos, sub_mul, div_mul_cancel₀ _ hrpos.ne']
    linarith
  · have : (1 : ℝ) / 3 ≤ (ρ - 1) / (ρ + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    linarith
  · have hρ3 : (3 : ℝ) ≤ ρ := by rw [hρ]; exact_mod_cast (korRho_three_le_iff hs).mpr h3
    have : (1 : ℝ) / 2 ≤ (ρ - 1) / (ρ + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    linarith

/-! ## `cor:residueQU` -/

/-- **`cor:residueQU`** (separation for every `N`): with `LB = p^{-1/s} L`, `L ≤ ℓ_jit(Λ_v)`,
`δ(P_{[N]}) ≥ (LB/p) N^{-1/s}` for every `N ≥ 2`. -/
theorem residue_allN [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) :
    SepAllN s (seqPoint (zcode p) (resSeq a θ v)) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L / p) :=
  prefix_sep_sN1 p s (Fact.out : p.Prime).two_le hs _ _
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hL0)
    fun K hK => residue_sepAtPrefix hs a ha θ hθ v hv L hL K hK

/-- **`cor:residueQU`** (mesh ratio): with `LB = p^{-1/s} L > 0`, `h(P_{[N]}) ≤ √s p²/LB · δ(P_{[N]})` for
every `N ≥ 2` (`δ = 2 · sepRad`, toroidal): the residue sequence is quasi-uniform. -/
theorem residue_mesh [Fact p.Prime] (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a)
    (θ : ZMod p) (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (L : ℝ) (hL0 : 0 < L)
    (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (resSeq a θ v))) ≤
      Real.sqrt s * (p : ℝ) ^ 2 / ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
          (prefixSet N (seqPoint (zcode p) (resSeq a θ v)))) :=
  prefix_mesh_sN1 (zcode p) _ (Fact.out : p.Prime).two_le hs (resSeq_t0 (zcode p) a ha θ hθ v hv) _
    (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _) hL0)
    (fun K hK => residue_sepAtPrefix hs a ha θ hθ v hv L hL K hK) N hN

/-- `cor:residueQU`, converse: for `p < 2^s` every check vector's lattice contains a nonzero
`e ∈ {-1,0,1}^s` (two of the `2^s` subset sums `∑_{c∈A} v_c` agree modulo `p`). -/
lemma small_vec [NeZero p] (hp : p < 2 ^ s) (v : Fin s → ZMod p) :
    ∃ e : Fin s → ℤ, e ≠ 0 ∧ (∀ c, |e c| ≤ 1) ∧ InLat v e := by
  have hcard : Fintype.card (ZMod p) < Fintype.card (Finset (Fin s)) := by
    rw [ZMod.card, Fintype.card_finset, Fintype.card_fin]
    exact hp
  obtain ⟨A, B, hAB, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun A : Finset (Fin s) => ∑ c ∈ A, v c) hcard
  refine ⟨fun c => (if c ∈ A then 1 else 0) - (if c ∈ B then 1 else 0), ?_, ?_, ?_⟩
  · intro h
    apply hAB
    ext c
    have := congrFun h c
    by_cases hA : c ∈ A <;> by_cases hB : c ∈ B <;> simp_all
  · intro c
    by_cases hA : c ∈ A <;> by_cases hB : c ∈ B <;> simp [hA, hB]
  · unfold InLat
    have : ∀ c, v c * (((if c ∈ A then (1 : ℤ) else 0) - (if c ∈ B then 1 else 0) : ℤ) : ZMod p) =
        (if c ∈ A then v c else 0) - (if c ∈ B then v c else 0) := fun c => by
      by_cases hA : c ∈ A <;> by_cases hB : c ∈ B <;> simp [hA, hB]
    simp only [this]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.univ_inter]
    exact sub_eq_zero.mpr heq

lemma jitNorm_small {e : Fin s → ℤ} (he : ∀ c, |e c| ≤ 1) : jitNorm e = 0 := by
  unfold jitNorm
  rw [Finset.sum_eq_zero fun c _ => ?_, Real.sqrt_zero]
  have : |(e c : ℝ)| ≤ 1 := by exact_mod_cast he c
  rw [max_eq_right (by linarith)]; norm_num

/-- **`cor:residueQU`**: a check vector with `ℓ_jit(Λ_v) > 0` exists if and only if `p > 2^s` (and then the
Korobov vector is one). -/
theorem jit_exists_iff [Fact p.Prime] (hs : 2 ≤ s) :
    (∃ v : Fin s → ZMod p, (∀ c, v c ≠ 0) ∧ 0 < ljit v) ↔ 2 ^ s < p := by
  have hpr : p.Prime := Fact.out
  constructor
  · rintro ⟨v, -, hpos⟩
    by_contra h
    rcases (not_lt.mp h).lt_or_eq with h1 | h1
    · obtain ⟨e, he0, he1, hlat⟩ := small_vec h1 v
      have := ljit_le v e he0 hlat
      rw [jitNorm_small he1] at this
      linarith
    · have h2 : 2 ∣ p := h1 ▸ dvd_pow_self 2 (by omega)
      rcases hpr.eq_one_or_self_of_dvd 2 h2 with h3 | h3
      · omega
      · have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
        omega
  · intro h
    refine ⟨korobov p s, korobov_ne_zero hs, lt_of_lt_of_le ?_ (korobov_ljit hs)⟩
    have : (2 : ℝ) ≤ korRho p s := by exact_mod_cast (korRho_two_le_iff hs).mpr h
    linarith

/-! ## The headline form: Faure places, `θ = 1`, Korobov check vector -/

lemma faurePlace_injective (hsp : s ≤ p) : Function.Injective (faurePlace p : Fin s → ZMod p) := by
  intro c c' h
  unfold faurePlace at h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact Fin.ext h

/-- The generator matrices of `𝓡_v` with the Faure places and `θ = 1`:
`C_c[n][i] = v_c^{-1} [t^n] (c + t)^i · w_c(c + t)^{-(n+1)}` (the Palomar statement's `resGen`). -/
theorem resSeq_faure_apply [Fact p.Prime] (v : Fin s → ZMod p) (c : Fin s) (n i : ℕ) :
    resSeq (faurePlace p) 1 v c n i = (v c)⁻¹ * PowerSeries.coeff n
      ((taylor (faurePlace p c) (X ^ i) : PowerSeries (ZMod p)) *
        ((taylor (faurePlace p c) (wCo (faurePlace p) c) : PowerSeries (ZMod p))⁻¹) ^ (n + 1)) := by
  rw [resSeq_apply, one_pow, mul_one]

/-- **`thm:residue` + `cor:korobov` + `cor:residueQU`** for the paper's explicit sequence (Faure places
`a_c = c`, `θ = 1`, Korobov check vector), every `s ≥ 2` and prime `p > 2^s`: a digital `(0,s)`-sequence;
any two distinct points among the first `N = p^{sK-1}` points have toroidal distance
`≥ (ρ - 1) p^{-1/s} N^{-1/s}`; `δ(P_{[N]}) ≥ (LB/p) N^{-1/s}` with `LB = (ρ - 1) p^{-1/s} > 0` for every
`N ≥ 2`; and the mesh ratio is `≤ √s p²/LB` for every `N ≥ 2` (quasi-uniform). -/
theorem residue_korobov [Fact p.Prime] (hs : 2 ≤ s) (hps : 2 ^ s < p) :
    IsSeq0 (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) ∧
      (∀ K : ℕ, 1 ≤ K → ∀ x y : ℕ, x < p ^ (s * K - 1) → y < p ^ (s * K - 1) → x ≠ y →
        ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 : ℝ) / s) *
            ((p ^ (s * K - 1) : ℕ) : ℝ) ^ (-(1 : ℝ) / s) ≤
          Z3NetDGS.torDist2 (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) x)
            (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)) y)) ∧
      0 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) ∧
      SepAllN s (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)))
        (((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) / p) ∧
      (∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)))) ≤
          Real.sqrt s * (p : ℝ) ^ 2 / (((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ)))) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (resSeq (faurePlace p) 1 (korobov p s)))))) := by
  have hpr : p.Prime := Fact.out
  have hsp : s ≤ p := (Nat.lt_two_pow_self).le.trans hps.le
  have ha := faurePlace_injective (p := p) hsp
  have hρ2 : (2 : ℝ) ≤ korRho p s := by exact_mod_cast (korRho_two_le_iff hs).mpr hps
  have hLB : 0 < ((korRho p s : ℝ) - 1) * (p : ℝ) ^ (-(1 / (s : ℝ))) :=
    mul_pos (by linarith) (Real.rpow_pos_of_pos (by exact_mod_cast hpr.pos) _)
  have hv := korobov_ne_zero (p := p) hs
  have hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat (korobov p s) b → (korRho p s : ℝ) - 1 ≤ jitNorm b :=
    korobov_jit hs
  refine ⟨resSeq_t0 (zcode p) _ ha 1 one_ne_zero _ hv,
    fun K hK x y hx hy hxy => korobov_sep hs _ ha 1 one_ne_zero K hK x y hx hy hxy, hLB, ?_, ?_⟩
  · have := residue_allN hs _ ha 1 one_ne_zero _ hv _ (by linarith) hL
    rwa [mul_comm ((p : ℝ) ^ (-(1 / (s : ℝ))))] at this
  · intro N hN
    have := residue_mesh hs _ ha 1 one_ne_zero _ hv _ (by linarith) hL N hN
    rwa [mul_comm ((p : ℝ) ^ (-(1 / (s : ℝ))))] at this

end GeoSeq
