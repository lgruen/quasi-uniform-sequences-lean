/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V98Defs

@[expose] public section

/-!
# GeoSeq stage V10-2 (part 1): the change of variable in a residue (`lem:reschange`), every commutative ring

Laurent-series-free form. A Laurent series with finite principal part is `F = x^{-n-1} G` with `G` a power series,
and `Res_x(F dx) = [x^n] G`. For the substitution `x = u(t) = t μ(t)`, `μ` a unit with inverse `ν`,
`F(u) u' = t^{-n-1} G(u) u' ν^{n+1}`, so `Res_t(F(u) u' dt) = [t^n] G(u) u' ν^{n+1}`. Thus `lem:reschange` is

  `[x^n] G = [t^n] G(u(t)) · u'(t) · ν(t)^{n+1}`  for every power series `G` and every `n`   (`reschange`).

* `coeff_pow_derivative`: the char-free core, `[t^m] ν^m = [t^{m-1}] ν^{m-1} ν'` (`m ≥ 1`), for EVERY power series
  `ν` over EVERY commutative ring — proved for the generic series over `ℤ[ν_0, ν_1, …]` (a domain of characteristic
  zero, where `m·[t^m]ν^m = [t^{m-1}](ν^m)' = m·[t^{m-1}]ν^{m-1}ν'` can be cancelled) and specialised by
  `PowerSeries.map` (the universal-coefficient argument of the paper's proof, without passing to `ℚ`).
* `res_basis`: `Res_t(u^{-j-1} u' dt) = [t^j] u' ν^{j+1} = [j = 0]` (the residue of `Z^k Z'` in the paper's proof,
  `k = -j-1 < 0`; for `k ≥ 0` the series has no negative powers).
* **`reschange`**: the change of variable for every power series `G`, every `n`.
-/

namespace GeoSeq

open PowerSeries

section Core

/-- The generic power series `∑_i ν_i t^i` over `ℤ[ν_0, ν_1, …]`. -/
noncomputable def genPS : PowerSeries (MvPolynomial ℕ ℤ) := PowerSeries.mk fun i => MvPolynomial.X i

lemma coeff_pow_derivative_gen (m : ℕ) :
    coeff (m + 1) (genPS ^ (m + 1)) = coeff m (genPS ^ m * d⁄dX genPS) := by
  have h := coeff_derivative (genPS ^ (m + 1)) m
  rw [derivative_pow, Nat.add_sub_cancel, mul_assoc] at h
  have h2 : coeff m ((((m + 1 : ℕ) : PowerSeries (MvPolynomial ℕ ℤ))) * (genPS ^ m * d⁄dX genPS)) =
      ((m + 1 : ℕ) : MvPolynomial ℕ ℤ) * coeff m (genPS ^ m * d⁄dX genPS) := by
    rw [← map_natCast (C (R := MvPolynomial ℕ ℤ)), coeff_C_mul]
  rw [h2] at h
  have hne : ((m + 1 : ℕ) : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  apply mul_left_cancel₀ hne
  rw [h]; push_cast; ring

/-- **The char-free core of `lem:reschange`**: for every power series `ν` over every commutative ring and every
`m`, `[t^{m+1}] ν^{m+1} = [t^m] ν^m ν'`. (Over `ℚ` this is `(ν^{m+1})' = (m+1) ν^m ν'`; in characteristic `p` with
`p ∣ m + 1` that argument divides by zero, and the identity is transported from the generic series over `ℤ`.) -/
theorem coeff_pow_derivative {R : Type*} [CommRing R] (ν : PowerSeries R) (m : ℕ) :
    coeff (m + 1) (ν ^ (m + 1)) = coeff m (ν ^ m * d⁄dX ν) := by
  let f : MvPolynomial ℕ ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) fun i => coeff i ν
  have hmap : PowerSeries.map f genPS = ν := by
    ext i; simp [genPS, f, coeff_map]
  have hder : PowerSeries.map f (d⁄dX genPS) = d⁄dX (PowerSeries.map f genPS) := by
    ext i; simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]
  have h := congrArg f (coeff_pow_derivative_gen m)
  have e1 : f (coeff (m + 1) (genPS ^ (m + 1))) = coeff (m + 1) (ν ^ (m + 1)) := by
    rw [← coeff_map, map_pow, hmap]
  have e2 : f (coeff m (genPS ^ m * d⁄dX genPS)) = coeff m (ν ^ m * d⁄dX ν) := by
    rw [← coeff_map, map_mul, map_pow, hder, hmap]
  rw [← e1, ← e2, h]

end Core

section Change
variable {R : Type*} [CommRing R]

/-- `Res_t(u^{-j-1} u' dt) = [j = 0]` for `u = t μ`, `μ ν = 1`: the coefficient of `t^j` in `u' ν^{j+1}`. -/
theorem res_basis (μ ν : PowerSeries R) (hμν : μ * ν = 1) (j : ℕ) :
    coeff j (d⁄dX (X * μ) * ν ^ (j + 1)) = if j = 0 then 1 else 0 := by
  have hu : d⁄dX (X * μ) = μ + X * d⁄dX μ := by
    rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul]; ring
  -- `μ' = -ν' μ²` (from `μ ν = 1`)
  have hd : d⁄dX μ * ν = -(μ * d⁄dX ν) := by
    have := congrArg (d⁄dX) hμν
    rw [Derivation.leibniz, derivative_one, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have hbase : d⁄dX (X * μ) * ν ^ (j + 1) = ν ^ j * (μ * ν) - X * (μ * d⁄dX ν) * ν ^ j := by
    rw [hu, pow_succ]; linear_combination (X * ν ^ j) * hd
  rw [hbase, hμν, mul_one]
  rcases j with _ | m
  · simp
  · rw [ite_eq_right_iff.mpr (fun h => absurd h (Nat.succ_ne_zero m)), pow_succ ν m, show X * (μ * d⁄dX ν) * (ν ^ m * ν) =
      X * (ν ^ m * d⁄dX ν) * (μ * ν) by ring, hμν, mul_one, map_sub, coeff_succ_X_mul,
      ← pow_succ, coeff_pow_derivative ν m, sub_self]

/-- The polynomial part: `[t^n] (∑_{k ≤ n} G_k u^k) u' ν^{n+1} = G_n`. -/
lemma reschange_trunc (μ ν : PowerSeries R) (hμν : μ * ν = 1) (G : PowerSeries R) (n : ℕ) :
    coeff n ((Polynomial.aeval (X * μ) (trunc (n + 1) G) : PowerSeries R) * d⁄dX (X * μ) * ν ^ (n + 1)) =
      coeff n G := by
  rw [Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt G n)]
  simp only [coeff_trunc, Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single n]
  · rw [ite_eq_left_iff.mpr (fun hn => absurd (Nat.lt_succ_self n) hn), Algebra.smul_def, show algebraMap R (PowerSeries R) (coeff n G) = C (coeff n G)
      from rfl, mul_assoc, mul_assoc, coeff_C_mul, mul_pow, show X ^ n * μ ^ n * (d⁄dX (X * μ) * ν ^ (n + 1)) =
      X ^ n * (d⁄dX (X * μ) * ν ^ (0 + 1)) * (μ * ν) ^ n by ring, hμν, one_pow, mul_one, coeff_X_pow_mul',
      ite_eq_left_iff.mpr (fun hn => absurd le_rfl hn), Nat.sub_self, res_basis μ ν hμν 0, ite_eq_left_iff.mpr (fun hn => absurd rfl hn), mul_one]
  · intro k hk hkn
    have hk' : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn
    rw [ite_eq_left_iff.mpr (fun hn => absurd (Finset.mem_range.mp hk) hn), Algebra.smul_def, show algebraMap R (PowerSeries R) (coeff k G) =
      C (coeff k G) from rfl, mul_assoc, mul_assoc, coeff_C_mul, mul_pow,
      show X ^ k * μ ^ k * (d⁄dX (X * μ) * ν ^ (n + 1)) = X ^ k * (d⁄dX (X * μ) * ν ^ (n - k + 1)) * (μ * ν) ^ k by
        rw [show n + 1 = (n - k + 1) + k by omega, pow_add]; ring,
      hμν, one_pow, mul_one, coeff_X_pow_mul', ite_eq_left_iff.mpr (fun hn => absurd hk'.le hn), res_basis μ ν hμν (n - k),
      ite_eq_right_iff.mpr (fun h => absurd h (by omega)), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

/-- **`lem:reschange`** (change of variable in a residue), over every commutative ring, Laurent-series-free form: for
`u = t μ` with `μ ν = 1` and every power series `G` and `n`, `Res_x(x^{-n-1} G dx) = Res_t(u^{-n-1} G(u) u' dt)`, i.e.
`[x^n] G = [t^n] G(u) · u' · ν^{n+1}`. -/
theorem reschange (μ ν : PowerSeries R) (hμν : μ * ν = 1) (G : PowerSeries R) (n : ℕ) :
    coeff n G = coeff n (G.subst (X * μ) * d⁄dX (X * μ) * ν ^ (n + 1)) := by
  have hu : HasSubst (X * μ) := HasSubst.of_constantCoeff_zero' (by simp)
  have hsplit := eq_X_pow_mul_shift_add_trunc (n + 1) G
  set H : PowerSeries R := mk fun i ↦ coeff (i + (n + 1)) G
  conv_rhs => rw [hsplit]
  rw [subst_add hu, subst_mul hu, subst_pow hu, subst_X hu, subst_coe hu, add_mul, add_mul, map_add,
    reschange_trunc μ ν hμν G n, mul_pow, mul_assoc, mul_assoc, mul_assoc, coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
    zero_add]

end Change

end GeoSeq
