/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage V0: definitions for the V3 re-sync

* `lam g zθ c` = `λ_c = g_c(0) w'(a_c)` (`prop:LI`(a) with the normalisation `ϖ̂ = 1`, the case `s ≥ 3`
  of the V3 paper): the constant of the free series, `λ_c φ_c = g_c w'(z_c)`, `ψ_c = 1/φ_c`.
-/

namespace GeoSeq

open Finset PowerSeries

/-- `λ_c = g_c(0) w'(a_c)` (`prop:LI`(a), normalisation `ϖ̂ = 1`). -/
noncomputable def lam {F : Type*} [Field F] {s : ℕ} (g zθ : Fin s → PowerSeries F) (c : Fin s) : F :=
  constantCoeff (g c) * placeDer zθ c

end GeoSeq
