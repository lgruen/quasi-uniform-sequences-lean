/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_2Defs

@[expose] public section

/-!
# Statements: stage V10_2 (paper V4, stage V10-2)

The change of variable in a residue (`lem:reschange`, every commutative ring, via the char-free core `[t^m] nu^m = [t^(m-1)] nu^(m-1) (d/dt nu)`), `lem:resform`(b) (self-similar scrambles as written in `def:selfsim` <=> local multipliers, `g <-> phi` mutually inverse, local roots exist and are unique), and bridges: `prop:onerel`, `cor:residuerows`, `lem:residue-t0`, `def:residuestar`, `lem:corrS`, `prop:joint` (i), (ii) for `def:selfsim` as written.
PROVED (`GeoSeq/V10_2Corr.lean`, `GeoSeq/V10_2Form.lean`, `GeoSeq/V10_2Res.lean`, `GeoSeq/V10_2SS.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_2`
(definitions in `GeoSeq/V10_2Defs.lean`). Paper: V4 (`paper/sections/A-machinery.tex, 04-law.tex, 05-residue.tex, 07-count.tex, 08-antipode.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-2). Configuration:
`comparatorGeoSeqV10_2.json`.
-/

namespace GeoSeq

section G0
open PowerSeries

/-- **The char-free core of `lem:reschange`**: for every power series `ν` over every commutative ring and every
`m`, `[t^{m+1}] ν^{m+1} = [t^m] ν^m ν'`. (Over `ℚ` this is `(ν^{m+1})' = (m+1) ν^m ν'`; in characteristic `p` with
`p ∣ m + 1` that argument divides by zero, and the identity is transported from the generic series over `ℤ`.) -/
theorem coeff_pow_derivative {R : Type*} [CommRing R] (ν : PowerSeries R) (m : ℕ) :
    coeff (m + 1) (ν ^ (m + 1)) = coeff m (ν ^ m * d⁄dX ν) := by
  sorry

end G0

section G1
open PowerSeries
variable {R : Type*} [CommRing R]

/-- `Res_t(u^{-j-1} u' dt) = [j = 0]` for `u = t μ`, `μ ν = 1`: the coefficient of `t^j` in `u' ν^{j+1}`. -/
theorem res_basis (μ ν : PowerSeries R) (hμν : μ * ν = 1) (j : ℕ) :
    coeff j (d⁄dX (X * μ) * ν ^ (j + 1)) = if j = 0 then 1 else 0 := by
  sorry

/-- **`lem:reschange`** (change of variable in a residue), over every commutative ring, Laurent-series-free form: for
`u = t μ` with `μ ν = 1` and every power series `G` and `n`, `Res_x(x^{-n-1} G dx) = Res_t(u^{-n-1} G(u) u' dt)`, i.e.
`[x^n] G = [t^n] G(u) · u' · ν^{n+1}`. -/
theorem reschange (μ ν : PowerSeries R) (hμν : μ * ν = 1) (G : PowerSeries R) (n : ℕ) :
    coeff n G = coeff n (G.subst (X * μ) * d⁄dX (X * μ) * ν ^ (n + 1)) := by
  sorry

end G1

section G2
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
local notation "PX" => (PowerSeries.X : PowerSeries F)
variable (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F)

/-- `u(zθ_c - a_c) = x`: the scaled local root inverts `u = w/θ` at `a_c`. -/
theorem locU_subst (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (c : Fin s) :
    ((locU a θ c : F[X]) : PowerSeries F).subst (zθ c - PowerSeries.C (a c)) = PX := by
  sorry

/-- **`lem:resform`(b), `⇐`**: for the scaled local roots `zθ` and any local multipliers `φ_c` (series in
`t = z - a_c`), the self-similar scramble with multipliers `g_c = ssMul a zθ φ c = θ φ_c(z_c(θx)) z_c'(θx)` has
digits `[x^n] g_c V(z_c(θx)) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz)` (`frDigit a (ssL a θ φ)`, `ssL_digit`). The proof is
the change of variable `lem:reschange` (`reschange`, every characteristic) with `x = u(t) = w(a_c + t)/θ` read
backwards: `t = zθ_c(x) - a_c = x κ(x)`. -/
theorem ssMul_digit (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ)
    (φ : Fin s → PowerSeries F) (c : Fin s) (n : ℕ) (V : F[X]) :
    PowerSeries.coeff n (ssMul a zθ φ c * Polynomial.aeval (zθ c) V) = frDigit a (ssL a θ φ) c n V := by
  sorry

/-- `φ ↦ g ↦ φ`: `ssMul ∘ locMul = id` on multipliers (`lem:resform`(b), the two maps are mutually inverse). -/
theorem ssMul_locMul (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) :
    ssMul a zθ (locMul a θ g) = g := by
  sorry

/-- `g ↦ φ ↦ g`: `locMul ∘ ssMul = id` (`lem:resform`(b)); uses that `zθ_c - a_c` is also a LEFT inverse of `u`. -/
theorem locMul_ssMul (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ)
    (φ : Fin s → PowerSeries F) : locMul a θ (ssMul a zθ φ) = φ := by
  sorry

/-- The local multipliers of unit multipliers are units: `φ_c(a_c) = g_c(0) θ^{-1} w_c(a_c)`. -/
theorem constantCoeff_locMul (g : Fin s → PowerSeries F) (c : Fin s) :
    PowerSeries.constantCoeff (locMul a θ g c) =
      PowerSeries.constantCoeff (g c) * (θ⁻¹ * (wCo a c).eval (a c)) := by
  sorry

/-- The multipliers of unit local multipliers are units: `g_c(0) = φ_c(a_c) · [x] zθ_c`. -/
theorem constantCoeff_ssMul (φ : Fin s → PowerSeries F) (hz : IsLocRoots a θ zθ) (c : Fin s) :
    PowerSeries.constantCoeff (ssMul a zθ φ c) =
      PowerSeries.constantCoeff (φ c) * PowerSeries.coeff 1 (zθ c) := by
  sorry

/-- **Existence of the scaled local roots** (`def:selfsim`; the paper's `z_c(x)`, `w(z_c(x)) = x`, at `θx`). -/
theorem locRoots_exists (ha : Function.Injective a) (hθ : θ ≠ 0) : ∃ zθ, IsLocRoots a θ zθ := by
  sorry

/-- **Uniqueness of the scaled local roots.** -/
theorem locRoots_unique (ha : Function.Injective a) (hθ : θ ≠ 0) (z₁ z₂ : Fin s → PowerSeries F)
    (h₁ : IsLocRoots a θ z₁) (h₂ : IsLocRoots a θ z₂) : z₁ = z₂ := by
  sorry

end G2

section G3
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F)

/-- Entry `C_c[n][k]` of `scrGen a L` is digit `n` of coordinate `c` at the index polynomial `z^k`. -/
theorem scrGen_eq_frDigit (L : Fin s → ℕ → ℕ → F) (c : Fin s) (n k : ℕ) :
    scrGen a L c n k = frDigit a L c n (X ^ k) := by
  sorry

theorem frDigit_congr {L₁ L₂ : Fin s → ℕ → ℕ → F} (h : scrGen a L₁ = scrGen a L₂) :
    frDigit a L₁ = frDigit a L₂ := by
  sorry

/-- **`lem:resform`(b), `⇐`, generator matrices**: the residue form `scrGen a (ssL a θ φ)` is the self-similar
scramble with the multipliers `g = ssMul a zθ φ` (`def:selfsim`: `C_c[n][k] = [x^n] g_c z_c(θx)^k`). -/
theorem ssL_eq_ssGen (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (φ : Fin s → PowerSeries F) :
    scrGen a (ssL a θ φ) = ssGen (ssMul a zθ φ) zθ := by
  sorry

/-- **`lem:resform`(b), `⇒`, generator matrices**: the self-similar scramble with multipliers `g` is the residue
form with the local multipliers `φ = locMul a θ g`. -/
theorem ssGen_eq_ssL (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) :
    ssGen g zθ = scrGen a (ssL a θ (locMul a θ g)) := by
  sorry

/-- **`def:selfsim` ⇒ residue form, digit by digit**: a self-similar scramble (as written) has the digits
`y_{c,n}(V) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz)` of `ssL a θ φ`, `φ = locMul a θ g`. -/
theorem selfsim_frDigit (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) : frDigit a L = frDigit a (ssL a θ (locMul a θ g)) := by
  sorry

/-- `def:selfsim` ⇒ the generator matrices of the residue form with `φ = locMul a θ g`. -/
theorem selfsim_scrGen (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) : scrGen a L = scrGen a (ssL a θ (locMul a θ g)) := by
  sorry

/-- The local multipliers of a self-similar scramble are units. -/
theorem selfsim_locMul_unit (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (c : Fin s) :
    PowerSeries.constantCoeff (locMul a θ g c) ≠ 0 := by
  sorry

/-- **`lem:resform`(b)** (as stated): a scramble of the frame is self-similar with scale `θ` (`def:selfsim`, for
some unit multipliers `g_c`) if and only if there are unit local multipliers `φ_c` (series in `t = z - a_c`) with
`y_{c,n}(V) = Res_{a_c}(V φ_c (θ/w)^{n+1} dz) = θ^{n+1} [t^n] V(a_c + t) φ_c(t) w_c(a_c + t)^{-n-1}` for all `c, n, V`.
The correspondence is `φ = locMul a θ g`, `g = ssMul a zθ φ` (`selfsim_frDigit`, `ssL_selfsim`, mutually inverse by
`ssMul_locMul`, `locMul_ssMul`). -/
theorem resform_b (ha : Function.Injective a) (hθ : θ ≠ 0) (L : Fin s → ℕ → ℕ → F) :
    (∃ g, IsSelfSim a θ g L) ↔ ∃ φ : Fin s → PowerSeries F, (∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) ∧
      ∀ c n V, frDigit a L c n V = θ ^ (n + 1) * PowerSeries.coeff n (((taylor (a c) V : F[X]) : PowerSeries F) *
        (φ c * (((taylor (a c) (wCo a c) : F[X]) : PowerSeries F)⁻¹) ^ (n + 1))) := by
  sorry

/-- The scramble `ssL a θ φ` with unit local multipliers is self-similar (`def:selfsim` as written) with the
multipliers `ssMul a zθ φ`. -/
theorem ssL_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (φ : Fin s → PowerSeries F) (hφ : ∀ c, PowerSeries.constantCoeff (φ c) ≠ 0) :
    IsSelfSim a θ (ssMul a zθ φ) (ssL a θ φ) := by
  sorry

/-- **`lem:residue-t0`, self-similarity clause (`def:selfsim` as written)**: the residue sequence `𝓡_v` is the
self-similar scramble with scale `θ` and the explicit multipliers `g_c = v_c^{-1} · d/dx z_c(θx)`
(`= θ v_c^{-1} z_c'(θx)`; local multipliers `φ_c = 1/v_c`). -/
theorem resSeq_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (v : Fin s → F) (hv : ∀ c, v c ≠ 0) :
    IsSelfSim a θ (fun c => PowerSeries.C (v c)⁻¹ * PowerSeries.derivative (zθ c)) (resL a θ v) := by
  sorry

/-- **The staggered residue sequence is self-similar (`def:selfsim` as written)**: `𝓡^⋆` (`resStarL`, staggered place
`c⋆`, `μ⋆ ≠ 0`, weights `k_c ≠ 0`) is the residue form with local multipliers `φ_{c⋆} = μ⋆ w_{c⋆}/θ`,
`φ_c = μ_c/(z - a_{c⋆})`, `μ_c = -μ⋆/k_c` (`def:residuestar`), hence self-similar with multipliers `ssMul a zθ φ`. -/
theorem resStar_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (cs : Fin s) (μs : F) (hμ : μs ≠ 0) (k : Fin s → F) (hk : ∀ c, c ≠ cs → k c ≠ 0) :
    ∃ φ : Fin s → PowerSeries F, IsSelfSim a θ (ssMul a zθ φ) (resStarL a θ cs μs k) := by
  sorry

end G3

section G4
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

theorem relSpace_congr (a : Fin s → F) {L₁ L₂ : Fin s → ℕ → ℕ → F} (h : frDigit a L₁ = frDigit a L₂) (T m : ℕ) :
    relSpace a L₁ T m = relSpace a L₂ T m := by
  sorry

end G4

section G5
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F)

/-- The relation spaces of a self-similar scramble (`def:selfsim`) are those of its residue form. -/
theorem selfsim_relSpace (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (T m : ℕ) :
    relSpace a L T m = relSpace a (ssL a θ (locMul a θ g)) T m := by
  sorry

/-- **`prop:onerel`(i) (polynomial part) and (ii), for `def:selfsim` as written.** If a self-similar scramble with
scale `θ` and unit multipliers `g_c` satisfies the level-independent relation `∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i} = 0` on
`P_{sT+i}` for every `T ≥ T₀ ≥ J`, then there is a polynomial `A ≠ 0`, `deg A < s - i`, with `φ_c ϑ_c(w/θ) = A` at
every place, `φ_c = θ^{-1} g_c(w/θ) w'` (`locMul`). -/
theorem onerel_poly_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (J T₀ i : ℕ) (hJ : J ≤ T₀)
    (ϑ : Fin s → ℕ → F) (hsupp : ∀ c i, J < i → ϑ c i = 0) (hϑ0 : ϑ ≠ 0)
    (hrel : ∀ T, T₀ ≤ T → liEmbed J T ϑ ∈ relSpace a L T (s * T + i)) :
    ∃ A : F[X], A ≠ 0 ∧ A.degree < ((s - i : ℕ) : WithBot ℕ) ∧
      ∀ c, locMul a θ g c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F) =
        ((taylor (a c) A : F[X]) : PowerSeries F) := by
  sorry

/-- **`prop:onerel`(iii), skeleton part, for `def:selfsim` as written.** A self-similar scramble satisfying a
skeleton relation `∑_c v_c y_{c,T} = 0` on `P_{s(T+1)-1}` at every level `T ≥ T₀` (`v ≠ 0`) has every `v_c ≠ 0`,
constant local multipliers `φ_c = α/v_c`, and IS the residue sequence `𝓡_{v/α}` (same generator matrices). -/
theorem onerel_skel_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (T₀ : ℕ) (v : Fin s → F) (hv : v ≠ 0)
    (hrel : ∀ T, T₀ ≤ T → skelVec T v ∈ relSpace a L T (s * (T + 1) - 1)) :
    ∃ α : F, α ≠ 0 ∧ (∀ c, v c ≠ 0 ∧ locMul a θ g c = PowerSeries.C (α / v c)) ∧
      scrGen a L = resSeq a θ (fun c => v c / α) := by
  sorry

/-- **`cor:residuerows`, self-similar clause, for `def:selfsim` as written.** A self-similar scramble whose rows are
residue rows up to scalars (`y_{c,n} = μ_{c,n} ŷ_{c,n}`) at every level `n ≥ n₀` IS the residue sequence `𝓡_v` with
`v_c = 1/φ_c(a_c)`. -/
theorem residuerows_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (n₀ : ℕ)
    (hrow : ∀ n, n₀ ≤ n → ∃ μ : Fin s → F, ∀ c V, frDigit a L c n V = μ c * resDig a c n V) :
    scrGen a L = resSeq a θ (fun c => (PowerSeries.constantCoeff (locMul a θ g c))⁻¹) := by
  sorry

/-- **`prop:onerel`(iii), staggered part, for `def:selfsim` as written.** A self-similar scramble satisfying
`y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` at every level `T ≥ T₀ ≥ 1` (`s ≥ 2`) has every `k_c ≠ 0` and IS the
staggered residue sequence `𝓡^⋆` with `μ⋆ = λθ` and weights `k` (`def:residuestar`). -/
theorem onerel_stag_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (hs : 2 ≤ s) (T₀ : ℕ) (hT₀ : 1 ≤ T₀) (cs : Fin s)
    (k : Fin s → F) (hrel : ∀ T, T₀ ≤ T → stagVec cs k T ∈ relSpace a L T (s * T)) :
    (∀ c, c ≠ cs → k c ≠ 0) ∧ ∃ lam : F, lam ≠ 0 ∧ scrGen a L = resStar a θ cs (lam * θ) k := by
  sorry

end G5

section G6
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **Rows below `K` of a residue form are those of the truncated rational residue form** `ssResGen a θ N 1`,
`N = truncN a φ K`. -/
theorem ssResGen_truncN (a : Fin s → F) (ha : Function.Injective a) (θ : F) (φ : Fin s → PowerSeries F) (K : ℕ)
    (c : Fin s) (n k : ℕ) (hn : n < K) :
    ssResGen a θ (truncN a φ K) (fun _ => 1) c n k = scrGen a (ssL a θ φ) c n k := by
  sorry

/-- `CorrRel` at level `K` reads only the rows `< K`. -/
theorem corrRel_congr {q : ℕ} [NeZero q] (D : DigitCode F q) (C₁ C₂ : Gen s F) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (K : ℕ) (hK : 1 ≤ K) (h : ∀ c n k, n < K → C₁ c n k = C₂ c n k) :
    CorrRel D C₁ v χ K ↔ CorrRel D C₂ v χ K := by
  sorry

/-- The carry entries at level `K` (geometric digit `K + i`) read only the rows `≤ K + i`. -/
theorem carry_congr (C₁ C₂ : Gen s F) (K i l : ℕ) (c c' : Fin s) (d : F)
    (h : ∀ c n k, n ≤ K + i → C₁ c n k = C₂ c n k) :
    IsCarryEntry C₁ K i l c c' d ↔ IsCarryEntry C₂ K i l c c' d := by
  sorry

/-- **Power-series correction coefficients give the rational ones of the truncation**:
`CorrTruncPS a θ φ v χ K ⇒ CorrTrunc a θ (truncN a φ K) 1 v χ K`. -/
theorem corrTrunc_of_PS (a : Fin s → F) (θ : F) (φ : Fin s → PowerSeries F) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (K : ℕ) (h : CorrTruncPS a θ φ v χ K) : CorrTrunc a θ (truncN a φ K) (fun _ => 1) v χ K := by
  sorry

end G6

section G7
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
local notation "PX" => (PowerSeries.X : PowerSeries F)
variable (a : Fin s → F) (θ : F) (zθ : Fin s → PowerSeries F)

/-- `v_c = 1/φ_c(a_c)` (the paper's definition in `lem:corrS`). -/
theorem corrV_eq (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) (c : Fin s) :
    corrV zθ g c = (PowerSeries.constantCoeff (locMul a θ g c))⁻¹ := by
  sorry

/-- `χ_{c,0} = 1`. -/
theorem corrCoef_zero (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F)
    (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (c : Fin s) : corrCoef zθ g c 0 = 1 := by
  sorry

/-- **The correction coefficients of `lem:corrS` are `v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)`**: with `corrV`,
`corrCoef`, `1/φ_c = v_c ∑_{d<K} χ_{c,d} (w/θ)^d + O(w^K)` at `a_c` for every `K` (`φ = locMul a θ g`). -/
theorem corrTruncPS_corrCoef (ha : Function.Injective a) (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ)
    (g : Fin s → PowerSeries F) (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (K : ℕ) :
    CorrTruncPS a θ (locMul a θ g) (corrV zθ g) (corrCoef zθ g) K := by
  sorry

/-- **The correction data are free parameters of self-similar scrambles**: for every `v` with `v_c ≠ 0` and every
`χ` with `χ_{c,0} = 1` there are unit multipliers `g_c = zθ_c' / (v_c ∑_d χ_{c,d} x^d)` whose self-similar scramble
(the residue form `ssL a θ (locMul a θ g)`, `def:selfsim`) has exactly these `v`, `χ` (`corrV`, `corrCoef`). -/
theorem corr_free (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (ha : Function.Injective a) (v : Fin s → F)
    (hv : ∀ c, v c ≠ 0) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) :
    ∃ g : Fin s → PowerSeries F, IsSelfSim a θ g (ssL a θ (locMul a θ g)) ∧ corrV zθ g = v ∧
      corrCoef zθ g = χ := by
  sorry

/-- **Uniqueness**: the correction data `(v, χ)` determine the multipliers of a self-similar scramble. -/
theorem corr_inj (hθ : θ ≠ 0) (hz : IsLocRoots a θ zθ) (g g' : Fin s → PowerSeries F)
    (hg : ∀ c, PowerSeries.constantCoeff (g c) ≠ 0) (hg' : ∀ c, PowerSeries.constantCoeff (g' c) ≠ 0)
    (hv : corrV zθ g = corrV zθ g') (hχ : corrCoef zθ g = corrCoef zθ g') : g = g' := by
  sorry

end G7

section G8
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable (a : Fin s → F) (θ : F)

/-- **`lem:corrS` for `def:selfsim` as written, any correction data**: if `v`, `χ` (`χ_{c,0} = 1`) are correction
coefficients of the local multipliers `φ = locMul a θ g` up to order `K` (`CorrTruncPS`), every point of `P_{sK-1}`
satisfies `∑_c v_c [y_{c,K-1} + ∑_{d=1}^{K-1} χ_{c,d} y_{c,K-1-d}] = 0`. -/
theorem selfsim_corr_of {q : ℕ} [NeZero q] (D : DigitCode F q) (hs : 2 ≤ s) (ha : Function.Injective a)
    (hθ : θ ≠ 0) (g : Fin s → PowerSeries F) (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L)
    (v : Fin s → F) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTruncPS a θ (locMul a θ g) v χ K) : CorrRel D (scrGen a L) v χ K := by
  sorry

/-- **`lem:corrS` for `def:selfsim` as written** (unconditional): every self-similar scramble with scale `θ`,
unit multipliers `g_c` and scaled local roots `zθ` satisfies, for every `K ≥ 1`, the corrected skeleton relation on
`P_{sK-1}` with `v_c = 1/φ_c(a_c)` (`corrV_eq`) and the correction coefficients `χ_{c,d}` of the expansion
`1/φ_c = v_c ∑_d χ_{c,d} (w/θ)^d`, i.e. `v_c ∑_d χ_{c,d} x^d = zθ_c'(x)/g_c(x)` (`corrCoef`). -/
theorem selfsim_corrS {q : ℕ} [NeZero q] (D : DigitCode F q) (hs : 2 ≤ s) (ha : Function.Injective a)
    (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F) (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (K : ℕ) (hK : 1 ≤ K) :
    CorrRel D (scrGen a L) (corrV zθ g) (corrCoef zθ g) K := by
  sorry

/-- **`prop:joint`(i) for `def:selfsim` as written**: at every full level `K ≥ 1`, for every step `e` and carry
lengths `l_c ∈ [0, K]`, the changes `σ_c = ∑_{c'} e_{c'} D(l_{c'})[c][c']` of the geometric digits satisfy
`∑_c v_c σ_c = -∑_c e_c v_c Ψ_c(l_c)` (`v = corrV`, `χ = corrCoef`, `Ψ_c(j) = ∑_{d=1}^j χ_{c,d}`). -/
theorem selfsim_joint_step (hs : 2 ≤ s) (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (g : Fin s → PowerSeries F) (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L)
    (K : ℕ) (hK : 1 ≤ K) (e : Fin s → ℤ) (lc : Fin s → ℕ) (hl : ∀ c, lc c ≤ K) (Dr : Fin s → Fin s → F)
    (hD : ∀ c c', IsCarryEntry (scrGen a L) K 0 (lc c') c c' (Dr c c')) :
    ∑ c, corrV zθ g c * ∑ c', (e c' : F) * Dr c c' =
      -∑ c, (e c : F) * (corrV zθ g c * psiSum (corrCoef zθ g) c (lc c)) := by
  sorry

/-- **`prop:joint`(ii) for `def:selfsim` as written**: two self-similar scrambles (scale `θ`, the same local roots)
whose multipliers differ only in coordinate `c`, with the same `v_c` and the same correction coefficients
`χ_{c,d}`, `d < l`, have at every full level `K ≥ l ≥ 1` the same cross responses `X^{(l)}_{c₁←c}` and the same
`O^{(l)}_c + Ψ_c(l)` (carry length `l` in coordinate `c`). -/
theorem selfsim_joint_ii (hs : 2 ≤ s) (ha : Function.Injective a) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hz : IsLocRoots a θ zθ) (g g' : Fin s → PowerSeries F) (L L' : Fin s → ℕ → ℕ → F)
    (hL : IsSelfSim a θ g L) (hL' : IsSelfSim a θ g' L') (c : Fin s) (hg' : ∀ c', c' ≠ c → g' c' = g c')
    (hv : corrV zθ g' c = corrV zθ g c) (K : ℕ) (hK : 1 ≤ K) (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K)
    (hχ : ∀ d, d < l → corrCoef zθ g' c d = corrCoef zθ g c d) (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (scrGen a L) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (scrGen a L') K 0 l c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧
      Dnew c + psiSum (corrCoef zθ g') c l = Dold c + psiSum (corrCoef zθ g) c l := by
  sorry

end G8

end GeoSeq
