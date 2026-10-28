/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V4Defs

@[expose] public section

/-!
# GeoSeq stage V4: the single-prime designs of `thm:LF`(b) — data and kernel checks

Data from `archive/lex_witnesses/smallp/s3_p11.cfg` and `s4_p37.cfg` (places, `θ`, `λ`, upper
crosses, windows; `app:LFdata`, "The single-prime designs"). `edValid` (crosses, condition (i), `def:lex`,
`Γ < p`, the covering of every column by enumeration of `𝔽_p^j`) is checked by `decide +kernel`.
-/

namespace GeoSeq

/-- The `p = 11` design is valid (`decide +kernel`) and `Γ = 10`. -/
theorem edP11_valid : edValid 11 edP11 ∧ edCost edP11 = 10 := by
  decide +kernel

/-- The `p = 37` design is valid (`decide +kernel`; column `3` by enumeration of `𝔽_37^3`) and `Γ = 36`. -/
theorem edP37_valid : edValid 37 edP37 ∧ edCost edP37 = 36 := by
  decide +kernel

end GeoSeq
