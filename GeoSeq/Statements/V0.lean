/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V0Defs
public import GeoSeq.SteerDefs

@[expose] public section

/-!
# Statements: stage V0 (small statements changed by the V3 paper)

PROVED (`GeoSeq/V0.lean`); generated verbatim from the proof file's signatures.

* `LI_a_lambda`, `LI_c_lambda` (`prop:LI`(a), (c), the `λ`-form of V3): `ψ_c = λ_c/(g_c w'(z_c))` with
  `λ_c = g_c(0) w'(a_c) ≠ 0`, and `κ_{c←c'} = θ λ_c/(λ_{c'} w'(a_c) (a_{c'} - a_c))`.
* `cover_prod` (`lem:volume`, product-window form): if every line `β + F α` meets the product window
  `Wo^{(c')} × ∏_{c≠c'} W_{c←c'}`, then `|Wo^{(c')}| ∏_{c≠c'} |W_{c←c'}| ≥ q^{s-1}`.
* `freeze_c` (`prop:freeze`(c)): under (b), `O_0 = 1 - z_1²`.
* `HB17_qu` (`cor:HB17`, "quasi-uniform"): mesh ratio `h/δ ≤ √2 p/(1 - 17/p)` along all `N ≥ 2`.
-/

namespace GeoSeq

open Finset PowerSeries

section LI

variable {F : Type*} [Field F] {s : ℕ}

/-- `w'(a_c) ≠ 0` for distinct places. -/
theorem placeDer_ne_zero (zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ))
    (c : Fin s) : placeDer zθ c ≠ 0 := by
  sorry

/-- **`prop:LI`(a), `λ`-form** (normalisation `ϖ̂ = 1`): the free series of column `c'` is
`ψ_{c'} = λ_{c'}/(g_{c'} w'(z_{c'}))`, i.e. `λ_{c'} φ_{c'} = g_{c'} w'(z_{c'})` with `φ = 1/ψ`, and
`λ_{c'} = g_{c'}(0) w'(a_{c'}) ∈ F^*`. -/
theorem LI_a_lambda (g zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (c' : Fin s) :
    freeSer g zθ c' = C (lam g zθ c') * (g c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹ ∧
      lam g zθ c' ≠ 0 := by
  sorry

/-- **`prop:LI`(c), second form of the depth-zero cross** (V3):
`κ_{c←c'} = θ g_c(0)/(g_{c'}(0) w'(a_{c'}) (a_{c'} - a_c)) = θ λ_c/(λ_{c'} w'(a_c) (a_{c'} - a_c))`. -/
theorem LI_c_lambda (θ : F) (g zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (c c' : Fin s) (hcc : c ≠ c') :
    kap θ g zθ c c' =
      θ * lam g zθ c / (lam g zθ c' * placeDer zθ c * (ssPlace zθ c' - ssPlace zθ c)) := by
  sorry

end LI

section Volume

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

/-- **`lem:volume`, product-window form**: if every line `β + F α` (`α ≠ 0`) meets the column window
`W^{(c')} = Wo^{(c')} × ∏_{c≠c'} W_{c←c'}` (coordinate `c'` in `Wo`, coordinate `c ≠ c'` in `Wx c`), then
`|Wo^{(c')}| ∏_{c≠c'} |W_{c←c'}| ≥ q^{s-1}`. -/
theorem cover_prod (α : Fin s → F) (hα : α ≠ 0) (c' : Fin s) (Wo : Finset F) (Wx : Fin s → Finset F)
    (hW : ∀ β : Fin s → F, ∃ t : F, β + t • α ∈ Fintype.piFinset (Function.update Wx c' Wo)) :
    Fintype.card F ^ (s - 1) ≤ Wo.card * ∏ c ∈ univ.erase c', (Wx c).card := by
  sorry

end Volume

section Freeze

variable {F : Type*} [Field F]

/-- **`prop:freeze`(c)**: for a self-similar scramble of the Faure frame, if (b) holds
(`g_0 = g_0(0)/(ρ z_1)`), then `O_0 = 1 - z_1²`: `D(l)[0][0] = [x^l] (1 - z_1²)/(1 - x)` for every `l`. -/
theorem freeze_c (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (hk0 : k0 * ((z1 - z0) * g0) = 1)
    (hb : g0 = C (constantCoeff g0) * ((z1 - z0) * z1)⁻¹) (l : ℕ) :
    lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 0 =
      coeff l ((1 - z1 ^ 2) * PowerSeries.mk 1) := by
  sorry

end Freeze

/-- **`cor:HB17`, quasi-uniform**: every sequence of `cor:HB17` (prime `p > 3677`, `e = 1`,
`b = ⌊p/68⌋`, responses in the windows) has mesh ratio `h(P_{[N]}) ≤ √2 p/(1 - 17/p) · δ(P_{[N]})`
for every `N ≥ 2` (`h` Euclidean covering radius, `δ = 2 · sepRad` toroidal separation). -/
theorem HB17_qu (p : ℕ) [Fact p.Prime] (hp : 3677 < p) (g : Fin 2 → PowerSeries (ZMod p))
    (hg1 : constantCoeff (g 1) ≠ 0)
    (hnorm : hbK01 p (p / 68) 1 * constantCoeff (g 1) = hbTheta p (p / 68) 1 * constantCoeff (g 0))
    (hW : RespIn (ssGen g (faureZ p (hbTheta p (p / 68) 1))) (hbWo p (p / 68) 1) (hbWx p (p / 68) 1))
    (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))))) ≤
      Real.sqrt 2 * p / (1 - 17 / (p : ℝ)) *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
          (prefixSet N (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1)))))) := by
  sorry

end GeoSeq
