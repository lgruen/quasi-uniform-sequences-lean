/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S10Defs

@[expose] public section

/-!
# Statements: geoseq stage S10 (structural results)

`prop:N1`, `prop:N2`, `prop:LI` (b)–(d) and the free part of (a), `prop:depthdir`, `lem:volume` (earlier
`cor:cover`), `prop:rank2`; legacy: `prop:composite`, `thm:dual`, `lem:H`. Compared theorems (statement with `sorry`; proofs in `GeoSeq/N1.lean`,
`Rational.lean`, `N2.lean`, `FrameLaw.lean`, `FrameLI.lean`, `Rank2.lean`, `Composite.lean`, `CompositeB.lean`,
`Dual.lean`, `DualThm.lean`, `DualBC.lean`, `LemH.lean`, restated by name; generated from the proof files'
signatures by script, with the section variables of each proof file).

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section

variable {R : Type*} [CommRing R] {s q : ℕ} [NeZero q]

/-! ## From `GeoSeq/N1.lean` -/

/-- If the prefix `P_m` is a `(0,m,s)`-net, every pattern of first digits, for every composition `d`
of `m`, is attained by exactly one index vector `V ∈ R^m`. -/
theorem box_existsUnique (D : DigitCode R q) (C : Gen s R) (m : ℕ)
    (hnet : BlockNet0 D C m 0) (d : Fin s → ℕ) (hd : ∑ c, d c = m) (T : Fin s → ℕ → R) :
    ∃! V : Fin m → R, ∀ c, ∀ n < d c, vecDigit C V c n = T c n := by
  sorry

end

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-! ## From `GeoSeq/N1.lean` -/

/-- **`prop:N1`, general form**: let `C` be a two-dimensional digital sequence over a finite field
whose coordinate `0` is lower triangular with nonzero diagonal, and whose prefixes `P_{2K}` and
`P_{2K+2}` are nets (`K ≥ 2`). Then it is impossible that the cross law of coordinate `0` is
finest-digit at both levels `K` and `K+1` and the own law of coordinate `1` is finest-digit at
level `K`. -/
theorem N1_general (D : DigitCode F q) (C : Gen 2 F) (K : ℕ) (hK : 2 ≤ K)
    (hnet : BlockNet0 D C (2 * K) 0) (hnet' : BlockNet0 D C (2 * (K + 1)) 0)
    (htri : ∀ n k, n < k → C 0 n k = 0) (hdiag : ∀ n, C 0 n n ≠ 0) :
    ¬ (LawFinest C K 0 1 ∧ LawFinest C (K + 1) 0 1 ∧ LawFinest C K 1 1) := by
  sorry

/-- **`prop:N1`** (no lattice law): for the Faure frame `a_0 = 0`, `a_1 = 1`, `K ≥ 2` and ANY scramble
`(L_0, L_1)` (lower triangular, nonzero diagonal) over any finite field, it is impossible that the cross
law of coordinate `0` is finest-digit at both levels `K` and `K+1` and the own law of coordinate `1` is
finest-digit at level `K`. -/
theorem N1 (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (K : ℕ) (hK : 2 ≤ K) :
    ¬ (LawFinest (scrGen ![0, 1] L) K 0 1 ∧ LawFinest (scrGen ![0, 1] L) (K + 1) 0 1 ∧
      LawFinest (scrGen ![0, 1] L) K 1 1) := by
  sorry

end

section

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-! ## From `GeoSeq/Rational.lean` -/

/-- `f` is rational iff its partial-sum series `f/(1-x)` is. -/
theorem isRat_partial (f : PS) : IsRatPS (f * PowerSeries.mk 1) ↔ IsRatPS f := by
  sorry

/-- An eventually periodic coefficient sequence gives a rational series. -/
theorem evPeriodic_isRat (a : ℕ → F) (h : EvPeriodic a) : IsRatPS (PowerSeries.mk a) := by
  sorry

/-- **The local roots are irrational** (proof of `prop:N2`): if `w` is monic of degree `≥ 2` and
`θ ≠ 0`, no power series `z` with `w(z) = θx` is rational. -/
theorem no_rat_root (w : F[X]) (hw : w.Monic) (hs : 2 ≤ w.natDegree) (θ : F) (hθ : θ ≠ 0)
    (z : PS) (hz : Polynomial.aeval z w = PowerSeries.C θ * X) : ¬ IsRatPS z := by
  sorry

end

section

variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

/-! ## From `GeoSeq/N2.lean` -/

/-- **`prop:N2`(a)** (self-similar part): for a self-similar scramble of the Faure frame (`s = 2`, places
`0, 1`, scaled roots `z_0 + z_1 = 1`, `z_0 z_1 = -θx`, `θ ≠ 0`) over any finite field, the generating
functions of the own responses `D(l)[1][1]` and of the cross responses `D(l)[0][1]` are not both rational. -/
theorem N2a [Fintype F] [DecidableEq F] (θ : F) (hθ : θ ≠ 0) (z0 z1 g0 g1 : PS)
    (hz0 : constantCoeff z0 = 0) (hsum : z0 + z1 = 1) (hprod : z0 * z1 = -(C θ * X))
    (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0) (o x : ℕ → F)
    (ho : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 1 1 (o l))
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 0 1 (x l)) :
    ¬ (IsRatPS (PowerSeries.mk o) ∧ IsRatPS (PowerSeries.mk x)) := by
  sorry

/-- `prop:N2`(a), periodic form: the two response sequences are not both eventually periodic. -/
theorem N2a_periodic [Fintype F] [DecidableEq F] (θ : F) (hθ : θ ≠ 0) (z0 z1 g0 g1 : PS)
    (hz0 : constantCoeff z0 = 0) (hsum : z0 + z1 = 1) (hprod : z0 * z1 = -(C θ * X))
    (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0) (o x : ℕ → F)
    (ho : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 1 1 (o l))
    (hx : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen ![g0, g1] ![z0, z1]) K 0 l 0 1 (x l)) :
    ¬ (EvPeriodic o ∧ EvPeriodic x) := by
  sorry

/-- **`prop:N2`(b)**: for a self-similar scramble of any frame with `s ≥ 3`, two cross responses
`c₁ ← c'` and `c₂ ← c'` of the same column (`c₁ ≠ c₂`, both `≠ c'`) do not both have rational generating
functions `∑_l D(l)[c_i][c'] x^l`. -/
theorem N2b [Fintype F] [DecidableEq F] {s : ℕ} (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s)
    (θ : F) (hθ : θ ≠ 0) (g zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (c₁ c₂ c' : Fin s) (h12 : c₁ ≠ c₂) (h1 : c₁ ≠ c') (h2 : c₂ ≠ c') (x₁ x₂ : ℕ → F)
    (hx₁ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₁ c' (x₁ l))
    (hx₂ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₂ c' (x₂ l)) :
    ¬ (IsRatPS (PowerSeries.mk x₁) ∧ IsRatPS (PowerSeries.mk x₂)) := by
  sorry

/-- `prop:N2`(b), periodic form: the two cross-response sequences are not both eventually periodic. -/
theorem N2b_periodic [Fintype F] [DecidableEq F] {s : ℕ} (w : F[X]) (hw : w.Monic)
    (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0) (g zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (c₁ c₂ c' : Fin s) (h12 : c₁ ≠ c₂) (h1 : c₁ ≠ c') (h2 : c₂ ≠ c') (x₁ x₂ : ℕ → F)
    (hx₁ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₁ c' (x₁ l))
    (hx₂ : ∀ K l, 1 ≤ l → l ≤ K → IsCarryEntry (ssGen g zθ) K 0 l c₂ c' (x₂ l)) :
    ¬ (EvPeriodic x₁ ∧ EvPeriodic x₂) := by
  sorry

end

section

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

/-! ## From `GeoSeq/FrameLaw.lean` -/

/-- **`w(Z) - θx = ∏_c (Z - z_c(θx))`** over `F[[x]]`. -/
theorem frame_factor (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hs : 1 ≤ s) :
    w.map PowerSeries.C - Polynomial.C (PowerSeries.C θ * X) =
      ∏ c, (Polynomial.X - Polynomial.C (zθ c)) := by
  sorry

/-- `w = ∏_c (Z - a_c)` over `F`. -/
theorem frame_factor_F (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (zθ : Fin s → PS)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hs : 1 ≤ s) :
    w = ∏ c, (Polynomial.X - Polynomial.C (ssPlace zθ c)) := by
  sorry

end

section

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

/-! ## From `GeoSeq/FrameLI.lean` -/

/-- `ψ(0) = 1`. -/
theorem freeSer_const (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (c' : Fin s) : constantCoeff (freeSer g zθ c') = 1 := by
  sorry

/-- Directional coefficient change: if `ψ` and `ψ'` agree below `x^l`, then
`[x^l] Eψ/(1-x) - [x^l] Eψ'/(1-x) = E(0) (ψ_l - ψ'_l)`. -/
theorem coeff_dir (E ψ ψ' : PS) (l : ℕ) (h : ∀ n < l, coeff n ψ = coeff n ψ') :
    coeff l (E * ψ * PowerSeries.mk 1) - coeff l (E * ψ' * PowerSeries.mk 1) =
      constantCoeff E * (coeff l ψ - coeff l ψ') := by
  sorry

/-- **`prop:LI`(c)** (every frame, normalisation `ϖ = dz`): for a self-similar scramble with free series
`ψ = freeSer g zθ c'` of column `c'`, the one-digit law `D(l) = [x^l]𝒟/(1-x)` has
`𝒟[c'][c'] = O_{c'} = 1 - ŵ_{c'}(z_{c'}) ψ` with `ŵ_{c'}(z) = ∏_{c≠c'} (z - a_c)/w'(a_{c'})`, and for
`c ≠ c'`, `𝒟[c][c'] = x X_{c←c'} = -κ_{c←c'} x χ_{cc'}(z_{c'}) ψ` with `χ_{cc'}(z) = (a_{c'} - a_c)/(z - a_c)`. The V3 second form of `κ` (`λ`-form) is `LI_c_lambda` (stage V0). -/
theorem LI_c (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0)
    (g zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (G : Matrix (Fin s) (Fin s) PS) (hMG : frameM g zθ * G = 1) (c' : Fin s) :
    (∀ l, lawD g zθ G 0 l c' c' =
      coeff l ((1 - (∏ c ∈ univ.erase c', (zθ c' - C (ssPlace zθ c))) * C (placeDer zθ c')⁻¹ *
        freeSer g zθ c') * PowerSeries.mk 1)) ∧
    (∀ c, c ≠ c' → ∀ l, lawD g zθ G 0 l c c' =
      coeff l (X * (-C (kap θ g zθ c c') *
        (C (ssPlace zθ c' - ssPlace zθ c) * (zθ c' - C (ssPlace zθ c))⁻¹) * freeSer g zθ c') *
          PowerSeries.mk 1)) := by
  sorry

/-- **`prop:depthdir`** (depth direction): let two self-similar scrambles of the same frame differ only in
the multiplier of column `c'`, with the same `g_{c'}(0)`, and let their free series agree below `x^l`.
Then the own response `O^{(l)}` changes by `-Δψ_l` and every cross response `X^{(l+1)}_{c←c'}` by
`-κ_{c←c'} Δψ_l`: the column moves along the fixed direction `(1, (κ_{c←c'})_{c≠c'})`, and the offset depends
only on the earlier coefficients of `ψ` (paper: `ψ̄_l = -θ^l ψ_{c',l}`, our `ψ` is `ψ_{c'}(θx)`). -/
theorem depthdir (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0)
    (zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (g g' : Fin s → PS) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hg' : ∀ c, constantCoeff (g' c) ≠ 0) (G G' : Matrix (Fin s) (Fin s) PS)
    (hMG : frameM g zθ * G = 1) (hMG' : frameM g' zθ * G' = 1) (c' : Fin s)
    (hother : ∀ c, c ≠ c' → g c = g' c) (h0 : constantCoeff (g c') = constantCoeff (g' c')) (l : ℕ)
    (hagree : ∀ n < l, coeff n (freeSer g zθ c') = coeff n (freeSer g' zθ c')) :
    lawD g zθ G 0 l c' c' - lawD g' zθ G' 0 l c' c' =
        -(coeff l (freeSer g zθ c') - coeff l (freeSer g' zθ c')) ∧
      ∀ c, c ≠ c' → lawD g zθ G 0 (l + 1) c c' - lawD g' zθ G' 0 (l + 1) c c' =
        -(kap θ g zθ c c' * (coeff l (freeSer g zθ c') - coeff l (freeSer g' zθ c'))) := by
  sorry

/-- **Freeness** (`prop:LI`(a), `prop:depthdir`): every unit series `ψ` with `ψ(0) = 1` and every value
`γ ≠ 0` of `g_{c'}(0)` occur: the multiplier `g_{c'} = γ w'(a_{c'}) / (ψ ∏_{c≠c'} (z_{c'} - z_c))` has
`g_{c'}(0) = γ` and free series `ψ`. -/
theorem freeSer_free (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s)
    (γ : F) (hγ : γ ≠ 0) (ψ : PS) (hψ : constantCoeff ψ = 1) :
    constantCoeff (Function.update g c' (C (γ * placeDer zθ c') *
        (ψ * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹) c') = γ ∧
      freeSer (Function.update g c' (C (γ * placeDer zθ c') *
        (ψ * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹)) zθ c' = ψ := by
  sorry

/-- **Row dependence** (`prop:depthdir`): if two multipliers of column `c'` have the same constant term
and their free series agree up to `x^n`, then row `n` of the generator matrix `C_{c'}` is the same. -/
theorem freeSer_row (g g' zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (hg' : ∀ c, constantCoeff (g' c) ≠ 0) (c' : Fin s)
    (h0 : constantCoeff (g c') = constantCoeff (g' c')) (n : ℕ)
    (hagree : ∀ m ≤ n, coeff m (freeSer g zθ c') = coeff m (freeSer g' zθ c')) (k : ℕ) :
    ssGen g zθ c' n k = ssGen g' zθ c' n k := by
  sorry

/-- **`prop:LI`(d)** (Faure frame, `s = 2`, places `0, 1`, normalisation `ϖ_1 = dz/z`, `ϖ_0 = dz/(z-1)`):
with `γ = z_1²` (`= (1 - z_0)²`), `ψ_1 = g_1(0) k_1 / z_1`, `ψ_0 = g_0(0) k_0 / z_1` (`k_c = 1/(ρ g_c)`),
`κ_{0←1} = θ g_0(0)/g_1(0)`, `κ_{1←0} = θ g_1(0)/g_0(0)`: the one-digit law `D(l) = [x^l]𝒟/(1-x)` has
`𝒟[0][1] = x X_{0←1}`, `X_{0←1} = -κ_{0←1} ψ_1`, `𝒟[1][1] = O_1 = 1 - γ ψ_1 = 1 + γ X_{0←1}/κ_{0←1}`, and
symmetrically for column `0`; `κ_{0←1} κ_{1←0} = θ²`, `X_{0←1}(0) = -κ_{0←1}` (as `ψ_1(0) = 1`). -/
theorem LI_d (θ : F) (z0 z1 g0 g1 k0 k1 : PS) (hz0 : constantCoeff z0 = 0) (hsum : z0 + z1 = 1)
    (hprod : z0 * z1 = -(C θ * X)) (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0)
    (hk0 : k0 * ((z1 - z0) * g0) = 1) (hk1 : k1 * ((z1 - z0) * g1) = 1) :
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 1 =
        coeff l (X * (-C (θ * constantCoeff g0 / constantCoeff g1) *
          (C (constantCoeff g1) * k1 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 =
        coeff l ((1 - z1 ^ 2 * (C (constantCoeff g1) * k1 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        coeff l (X * (-C (θ * constantCoeff g1 / constantCoeff g0) *
          (C (constantCoeff g0) * k0 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 0 =
        coeff l ((1 - z1 ^ 2 * (C (constantCoeff g0) * k0 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (θ * constantCoeff g0 / constantCoeff g1) * (θ * constantCoeff g1 / constantCoeff g0) = θ ^ 2 ∧
    constantCoeff (C (constantCoeff g1) * k1 * z1⁻¹) = 1 ∧
    constantCoeff (C (constantCoeff g0) * k0 * z1⁻¹) = 1 ∧
    (1 - z1 ^ 2 * (C (constantCoeff g1) * k1 * z1⁻¹) =
      1 + C (θ * constantCoeff g0 / constantCoeff g1)⁻¹ * z1 ^ 2 *
        (-C (θ * constantCoeff g0 / constantCoeff g1) * (C (constantCoeff g1) * k1 * z1⁻¹)) ∨
      θ = 0) := by
  sorry

end

section

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

/-! ## From `GeoSeq/Rank2.lean` -/

/-- **`lem:volume`** (earlier `cor:cover`; covering in `F^{s-1}`; the V3 product-window form is
`cover_prod`, stage V0): if every line `β + F α`, `α ≠ 0`, meets `W`, then the
projection of `W` along `α` onto `F^s / Fα` is onto, and `|W| ≥ q^{s-1}`. -/
theorem cover (α : Fin s → F) (hα : α ≠ 0) (W : Finset (Fin s → F))
    (hW : ∀ β : Fin s → F, ∃ t : F, β + t • α ∈ W) :
    (∀ y : (Fin s → F) ⧸ (Submodule.span F {α}), ∃ v ∈ W, Submodule.Quotient.mk v = y) ∧
      Fintype.card F ^ (s - 1) ≤ W.card := by
  sorry

end

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-! ## From `GeoSeq/Rank2.lean` -/

/-- **The law at level `K` is linear in the cells**: for any digital sequence whose prefix `P_{sK}` is a
net, there is a coefficient matrix with `r_c = y_{c,K} = ∑_{c'', j<K} coef c c'' j · y_{c'',j}`. -/
theorem law_coef_exists {s : ℕ} (D : DigitCode F q) (C : Gen s F) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) :
    ∃ coef : Fin s → Fin s → ℕ → F, ∀ V : Fin (s * K) → F, ∀ c,
      vecDigit C V c K = ∑ c'', ∑ j ∈ range K, coef c c'' j * vecDigit C V c'' j := by
  sorry

/-- **`prop:rank2`** (rank of the cross responses): let `C` be a digital sequence over a finite field in
dimension `s = n + 1` whose prefix `P_{sK}` is a `(0,sK,s)`-net, `K ≥ s - 1`, and let `coef` express the
geometric digits through the cell digits. Then for every coordinate `c'`, the minor of the cross rows
`(coef c c' ·)_{c ≠ c'}` on the `s - 1` finest digits `y_{c',K-s+1}, …, y_{c',K-1}` is nonzero. -/
theorem rank2 {n : ℕ} (D : DigitCode F q) (C : Gen (n + 1) F) (K : ℕ) (hK : n ≤ K)
    (hnet : BlockNet0 D C ((n + 1) * K) 0) (coef : Fin (n + 1) → Fin (n + 1) → ℕ → F)
    (hcoef : ∀ V : Fin ((n + 1) * K) → F, ∀ c,
      vecDigit C V c K = ∑ c'', ∑ j ∈ range K, coef c c'' j * vecDigit C V c'' j)
    (c' : Fin (n + 1)) : (crossFin coef K c').det ≠ 0 := by
  sorry

/-- **`prop:rank2`, "in particular"**: the `s - 1` cross rows `j ↦ coef c j` (`c ≠ c'`, `j < K`) of column
`c'` are linearly independent, i.e. the cross matrix `X_{c'}` has rank `s - 1`; in dimension three
(`n = 2`) the two cross rows of a column are not proportional. -/
theorem rank2_indep {n : ℕ} (D : DigitCode F q) (C : Gen (n + 1) F) (K : ℕ) (hK : n ≤ K)
    (hnet : BlockNet0 D C ((n + 1) * K) 0) (coef : Fin (n + 1) → Fin (n + 1) → ℕ → F)
    (hcoef : ∀ V : Fin ((n + 1) * K) → F, ∀ c,
      vecDigit C V c K = ∑ c'', ∑ j ∈ range K, coef c c'' j * vecDigit C V c'' j)
    (c' : Fin (n + 1)) :
    LinearIndependent F (fun i : Fin n => fun j : Fin K => coef (c'.succAbove i) c' j) := by
  sorry

end

section

/-! ## From `GeoSeq/Composite.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:composite`(a)**: for the untwisted family (`ϱ = 1`), `u_d + u_{s-d} = θ/s` whenever `ζ^s = 1`,
`ζ^d ≠ 1`, `d ≤ s`. -/
theorem composite_a {F : Type*} [Field F] (s : ℕ) (θ ζ : F) (hs : (s : F) ≠ 0) (hζ : ζ ^ s = 1)
    (d : ℕ) (hd : d ≤ s) (hζd : ζ ^ d ≠ 1) :
    twU s θ 1 ζ d + twU s θ 1 ζ (s - d) = θ / s := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** `prop:composite`(a) for `s = 4`: `u_1 - 2u_2 + u_3 = 0` (`ζ` a primitive fourth root of unity,
characteristic `≠ 2`). -/
theorem composite_a4 {F : Type*} [Field F] (θ ζ : F) (h2 : (2 : F) ≠ 0) (hζ : ζ ^ 2 = -1) :
    twU 4 θ 1 ζ 1 - 2 * twU 4 θ 1 ζ 2 + twU 4 θ 1 ζ 3 = 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:composite`(c)**: let `ξ ∈ ℤ^{s-1}` with `ξ ≢ 0 (mod p)` and `∑_d ξ_d u_d = 0` in `𝔽_p`, and let
`W = W_o × ∏_d W_d ⊆ 𝔽_p^s` with every element of `W_d` represented by an integer in `[-b_d, b_d]`. If
every line `β + 𝔽_p (1, u)` meets `W`, then `2 ∑_d |ξ_d| b_d ≥ p - 1`. -/
theorem composite_c (p : ℕ) [Fact p.Prime] (m : ℕ) (ξ : Fin m → ℤ) (hξ : ∃ d, (ξ d : ZMod p) ≠ 0)
    (u : Fin m → ZMod p) (hrel : ∑ d, (ξ d : ZMod p) * u d = 0)
    (Wo : Set (ZMod p)) (Wd : Fin m → Set (ZMod p)) (b : Fin m → ℕ)
    (hWd : ∀ d, ∀ x ∈ Wd d, ∃ k : ℤ, |k| ≤ b d ∧ (k : ZMod p) = x)
    (hline : ∀ (βo : ZMod p) (β : Fin m → ZMod p), ∃ t : ZMod p,
      βo + t ∈ Wo ∧ ∀ d, β d + t * u d ∈ Wd d) :
    p ≤ 2 * ∑ d, (ξ d).natAbs * b d + 1 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:composite`, "in particular"** (`s = 4`, `ϱ = 1`, `p ≡ 1 (mod 4)`): every product window meeting
all lines of direction `α = (1, u_1, u_2, u_3)` has `b_1 + 2b_2 + b_3 ≥ (p-1)/2`, so its cross windows
have total half-width `≥ (p-1)/4`. -/
theorem composite_s4 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (θ ζ : ZMod p) (hζ : ζ ^ 2 = -1)
    (Wo : Set (ZMod p)) (Wd : Fin 3 → Set (ZMod p)) (b : Fin 3 → ℕ)
    (hWd : ∀ d, ∀ x ∈ Wd d, ∃ k : ℤ, |k| ≤ b d ∧ (k : ZMod p) = x)
    (hline : ∀ (βo : ZMod p) (β : Fin 3 → ZMod p), ∃ t : ZMod p,
      βo + t ∈ Wo ∧ ∀ d, β d + t * twU 4 θ 1 ζ (d + 1) ∈ Wd d) :
    p - 1 ≤ 2 * (b 0 + 2 * b 1 + b 2) ∧ p - 1 ≤ 4 * (b 0 + b 1 + b 2) := by
  sorry

end

section

/-! ## From `GeoSeq/CompositeB.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`prop:composite`(b)**: for composite `s > 1` and every twist exponent `k` there is a nonzero
`ξ ∈ ℤ^{s-1}` (depending only on `s` and `k`) such that for every prime `p ≡ 1 (mod s)`, every primitive
`s`-th root of unity `ζ ∈ 𝔽_p` and every `θ`, the directions `u_d = θ ζ^{kd} / (s (1 - ζ^d))` of the twisted
symmetric Kummer family satisfy `∑_d ξ_d u_d = 0`; and `ξ ≢ 0 (mod p)` as soon as `p > max_d |ξ_d|`. -/
theorem composite_b (s : ℕ) (hs : 1 < s) (hcomp : ¬ s.Prime) (k : ℕ) :
    ∃ ξ : Fin (s - 1) → ℤ, ξ ≠ 0 ∧
      (∀ (p : ℕ) [Fact p.Prime], p % s = 1 → ∀ ζ : ZMod p, IsPrimitiveRoot ζ s → ∀ θ : ZMod p,
        ∑ d : Fin (s - 1), (ξ d : ZMod p) * twU s θ (ζ ^ k) ζ ((d : ℕ) + 1) = 0) ∧
      (∀ p : ℕ, (∀ d, (ξ d).natAbs < p) → ∃ d, (ξ d : ZMod p) ≠ 0) := by
  sorry

end

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {s q : ℕ} [NeZero q]

/-! ## From `GeoSeq/Dual.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** Kernel test for every `m` ⟹ `(0,s)`-sequence. -/
theorem isSeq0_of_kernel (D : DigitCode F q) (C : Gen s F)
    (hker : ∀ m : ℕ, ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ V : Fin m → F,
      (∀ c, ∀ n < d c, vecDigit C V c n = 0) → V = 0) : IsSeq0 D C := by
  sorry

end

section

variable {F : Type*} [Field F]

/-! ## From `GeoSeq/DualThm.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The kernel test for `eq:dual`** (`s = 3`, any field): under the three conditions every index
vector whose first `d_c` digits vanish in every coordinate, `∑ d_c = m`, is zero. -/
theorem dual_kernel (a ξ : Fin 3 → F) (ha : Function.Injective a) (hξ : Function.Injective ξ)
    (hdet : (a 1 - a 0) * (ξ 2 - ξ 0) - (a 2 - a 0) * (ξ 1 - ξ 0) ≠ 0)
    (m : ℕ) (d : Fin 3 → ℕ) (hd : ∑ c, d c = m) (V : Fin m → F)
    (hV : ∀ c, ∀ n < d c, vecDigit (dualGen a ξ) V c n = 0) : V = 0 := by
  sorry

end

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-! ## From `GeoSeq/DualThm.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:dual`(a), failures**: if the places are not distinct, or the parameters are not distinct, or
the points `(a_c, ξ_c)` are collinear, then already the prefix `P_2` or `P_3` is not a net. -/
theorem dual_fail (D : DigitCode F q) (a ξ : Fin 3 → F)
    (h : ¬ (Function.Injective a ∧ Function.Injective ξ ∧
      Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] ≠ 0)) :
    ¬ BlockNet0 D (dualGen a ξ) 2 0 ∨ ¬ BlockNet0 D (dualGen a ξ) 3 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:dual`(a)**: the dual-number Faure matrices `eq:dual` (`s = 3`, any finite field) form a
digital `(0,3)`-sequence iff the places `a_c` are distinct, the parameters `ξ_c` are distinct, and the
points `(a_c, ξ_c)` are not collinear (`det(1, a_c, ξ_c) ≠ 0`). Every failure occurs at `m ≤ 3`
(`dual_fail`). -/
theorem dual_a (D : DigitCode F q) (a ξ : Fin 3 → F) :
    IsSeq0 D (dualGen a ξ) ↔ Function.Injective a ∧ Function.Injective ξ ∧
      Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] ≠ 0 := by
  sorry

end

section

/-! ## From `GeoSeq/DualBC.lean` -/

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** Over `𝔽_3`, distinct places and parameters force `det(1, a_c, ξ_c) = 0` (kernel `decide`). -/
theorem dual_p3 : ∀ a0 a1 a2 x0 x1 x2 : ZMod 3, a0 ≠ a1 → a0 ≠ a2 → a1 ≠ a2 →
    x0 ≠ x1 → x0 ≠ x2 → x1 ≠ x2 → (a1 - a0) * (x2 - x0) - (a2 - a0) * (x1 - x0) = 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:dual`(b), example**: for a prime `p ≥ 5` and `a_2 ∉ {0, 1, 2}`, the parameters `a = (0, 1, a_2)`,
`ξ = (0, 1, 2)` are admissible (`det = 2 - a_2`). -/
theorem dual_b_example (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a2 : ZMod p) (h0 : a2 ≠ 0) (h1 : a2 ≠ 1)
    (h2 : a2 ≠ 2) :
    Function.Injective (![0, 1, a2] : Fin 3 → ZMod p) ∧
      Function.Injective (![0, 1, 2] : Fin 3 → ZMod p) ∧
      Matrix.det !![1, (![0, 1, a2] : Fin 3 → ZMod p) 0, (![0, 1, 2] : Fin 3 → ZMod p) 0;
        1, (![0, 1, a2] : Fin 3 → ZMod p) 1, (![0, 1, 2] : Fin 3 → ZMod p) 1;
        1, (![0, 1, a2] : Fin 3 → ZMod p) 2, (![0, 1, 2] : Fin 3 → ZMod p) 2] ≠ 0 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:dual`(b)**: for an odd prime `p`, there are distinct places, distinct parameters and
non-collinear points `(a_c, ξ_c) ∈ 𝔽_p²` iff `p ≥ 5`. -/
theorem dual_b (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (∃ a ξ : Fin 3 → ZMod p, Function.Injective a ∧ Function.Injective ξ ∧
      Matrix.det !![1, a 0, ξ 0; 1, a 1, ξ 1; 1, a 2, ξ 2] ≠ 0) ↔ 5 ≤ p := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:dual`(c)**: if `a_0 ≠ a_1` and `2 ≠ 0`, the projection `(C_0, C_1)` of `eq:dual` is not of the
form `(L_0 P_{b_0} G, L_1 P_{b_1} G)` with `L_c` lower triangular and `G` upper triangular with nonzero
diagonal: no sequence of `thm:dual` lies in the Faure orbit. -/
theorem dual_c {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (a ξ : Fin 3 → F) (ha : a 0 ≠ a 1) :
    ¬ ∃ (L0 L1 G : ℕ → ℕ → F) (b0 b1 : F),
      (∀ n k, n < k → L0 n k = 0) ∧ (∀ n k, n < k → L1 n k = 0) ∧
      (∀ n k, k < n → G n k = 0) ∧ (∀ n, G n n ≠ 0) ∧
      (∀ n k, dualGen a ξ 0 n k =
        ∑ j ∈ range (n + 1), ∑ i ∈ range (k + 1), L0 n j * pas b0 j i * G i k) ∧
      (∀ n k, dualGen a ξ 1 n k =
        ∑ j ∈ range (n + 1), ∑ i ∈ range (k + 1), L1 n j * pas b1 j i * G i k) := by
  sorry

end

section

/-! ## From `GeoSeq/LemH.lean` -/

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:H`, integer core**: let `p ≥ 11` be prime, `1 ≤ k`, `10k ≤ p`, `k² + 2 < 2p`. If the axis, diagonal
and antidiagonal certificate terms (numerators, `l_0 = l_1 = l`) of a symmetric law with responses
`O = O^{(l)}`, `X = X^{(l)}` are at least `(p - k)²`, then `-(k-1) ≤ Ō ≤ 0` and `|X̄| ≤ -Ō`. -/
theorem lemH_core (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (k : ℕ) (hk1 : 1 ≤ k) (hk : 10 * k ≤ p)
    (hk2 : k ^ 2 + 2 < 2 * p) (O X : ZMod p)
    (hax : ((p : ℤ) - k) ^ 2 ≤ (gapNum1 p 1 O : ℤ) ^ 2 + (gapNum1 p 0 X : ℤ) ^ 2)
    (hdi : ((p : ℤ) - k) ^ 2 ≤ 2 * (gapNum1 p 1 (O + X) : ℤ) ^ 2)
    (han : ((p : ℤ) - k) ^ 2 ≤ 2 * (gapNum1 p 1 (O - X) : ℤ) ^ 2) :
    -((k : ℤ) - 1) ≤ O.valMinAbs ∧ O.valMinAbs ≤ 0 ∧ |X.valMinAbs| ≤ -O.valMinAbs := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:H`** (symmetric barrier): let `p ≥ 11` be prime, `1 ≤ k`, `10k ≤ p` and `k² < 2p - 2`. If a
symmetric law (`O_0^{(l)} = O_1^{(l)} = O^{(l)}`, `X_{0←1}^{(l)} = X_{1←0}^{(l)} = X^{(l)}`) has certificate value
`LB_1 ≥ 1 - k/p` at level `K` (`lem:cert` with `j = 1`: every step term is `≥ 1 - k/p`), then for every
`1 ≤ l ≤ K`: `-(k-1) ≤ O^{(l)} ≤ 0` and `|X^{(l)}| ≤ -O^{(l)}` (centred representatives). -/
theorem lemH (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (k : ℕ) (hk1 : 1 ≤ k) (hk : 10 * k ≤ p)
    (hk2 : k ^ 2 + 2 < 2 * p) (K : ℕ) (Ol Xl : ℕ → ZMod p)
    (hcert : ∀ (e : Fin 2 → ℤ) (l : Fin 2 → ℕ), IsStep K e l →
      ((p : ℝ) - k) / p ≤ certTerm (zcode p) 1 e (certSigmaP (symLaw Ol Xl) 1 e l))
    (l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    -((k : ℤ) - 1) ≤ (Ol l).valMinAbs ∧ (Ol l).valMinAbs ≤ 0 ∧
      |(Xl l).valMinAbs| ≤ -(Ol l).valMinAbs := by
  sorry

end

end GeoSeq
