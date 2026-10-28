/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V96Defs
public import GeoSeq.V7Defs

@[expose] public section

/-!
# GeoSeq stage V9-7 (paper V4, `sec:joint`, `lem:shift`): definitions

* **Self-similar scrambles in residue form** (`lem:corrS`): local multipliers `φ_c = N_c / U_c` (polynomials, units at
  `a_c`); digit `n` of coordinate `c` is `Res_{a_c}(V φ_c (θ/w)^{n+1} dz) = θ^{n+1} Res_{a_c}(V N_c / (U_c w^{n+1}) dz)`
  (`ssResGen`). The paper's self-similar scrambles are of this form by `lem:resform`(b) (stage V9-8, not formalized);
  the residue sequence (`φ_c = 1/v_c`) and the staggered residue sequence (`φ_c = μ_c/(z - a_{c⋆})`) are instances.
* **The correction coefficients** (`lem:corrS`): `1/φ_c = v_c ∑_d χ_{c,d} (w/θ)^d` at `a_c`, in the truncated form
  `CorrTrunc` (`(z - a_c)^K ∣ U_c - v_c N_c ∑_{d<K} χ_{c,d} (w/θ)^d`, equivalent to `1/φ_c - v_c ∑_{d<K} χ_{c,d}(w/θ)^d =
  O(w^K)` since `w/(z - a_c)` is a unit at `a_c`); the corrected skeleton relation for the points `CorrRel`; the
  partial sums `Ψ_c(j) = ∑_{d=1}^j χ_{c,d}` (`psiSum`).
* `jitNormB`, `ljitB` (`thm:corrected`): `‖(|b| - (1+B)𝟏)_+‖_2` and its minimum over `Λ_v \ {0}`.
-/

namespace GeoSeq

open Finset Polynomial

section SS
variable {F : Type*} [Field F] {s : ℕ}

/-- **A self-similar scramble in residue form** with places `a`, scale `θ` and local multipliers `φ_c = N_c/U_c`:
`C_c[n][k] = θ^{n+1} Res_{a_c}(z^k N_c / ((z - a_c)^{n+1} U_c w_c^{n+1}) dz)`. -/
noncomputable def ssResGen (a : Fin s → F) (θ : F) (N U : Fin s → F[X]) : Gen s F :=
  fun c n k => θ ^ (n + 1) * locRes (a c) (n + 1) (X ^ k * N c) (U c * wCo a c ^ (n + 1))

/-- **The correction coefficients up to order `K`** (`lem:corrS`): `1/φ_c = v_c ∑_{d<K} χ_{c,d} (w/θ)^d + O(w^K)` at
`a_c`, i.e. `(z - a_c)^K ∣ U_c - v_c N_c ∑_{d<K} χ_{c,d} (θ^{-1} w)^d` for every `c`. -/
def CorrTrunc (a : Fin s → F) (θ : F) (N U : Fin s → F[X]) (v : Fin s → F) (χ : Fin s → ℕ → F) (K : ℕ) : Prop :=
  ∀ c, (X - C (a c)) ^ K ∣ U c - C (v c) * N c * ∑ d ∈ range K, C (χ c d) * (C θ⁻¹ * wPoly a) ^ d

/-- `Ψ_c(j) = ∑_{d=1}^{j} χ_{c,d}` (`Ψ_c(0) = 0`). -/
def psiSum (χ : Fin s → ℕ → F) (c : Fin s) (j : ℕ) : F := ∑ d ∈ Finset.Ico 1 (j + 1), χ c d

/-- **The corrected skeleton relation on `P_{sK-1}`** (`lem:corrS`, `thm:corrected`): every point with index
`x < q^{sK-1}` satisfies `∑_c v_c [y_{c,K-1}(x) + ∑_{d=1}^{K-1} χ_{c,d} y_{c,K-1-d}(x)] = 0`. -/
def CorrRel {q : ℕ} [NeZero q] (D : DigitCode F q) (C : Gen s F) (v : Fin s → F) (χ : Fin s → ℕ → F) (K : ℕ) :
    Prop :=
  ∀ x, x < q ^ (s * K - 1) → ∑ c, v c * (seqDigit D C x c (K - 1) +
    ∑ d ∈ Finset.Ico 1 K, χ c d * seqDigit D C x c (K - 1 - d)) = 0

end SS

section Jit
variable {s : ℕ}

/-- `‖(|b| - (1+B)𝟏)_+‖_2` (`thm:corrected`). -/
noncomputable def jitNormB (B : ℕ) (b : Fin s → ℤ) : ℝ :=
  Real.sqrt (∑ c, (max (|(b c : ℝ)| - 1 - B) 0) ^ 2)

/-- `ℓ_jit^{(B)}(Λ_v) = min_{0 ≠ b ∈ Λ_v} ‖(|b| - (1+B)𝟏)_+‖_2`, as an infimum. -/
noncomputable def ljitB {p : ℕ} (B : ℕ) (v : Fin s → ZMod p) : ℝ :=
  ⨅ b : {b : Fin s → ℤ // b ≠ 0 ∧ InLat v b}, jitNormB B b.1

end Jit

end GeoSeq
