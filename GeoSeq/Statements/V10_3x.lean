/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/

module
public import GeoSeq.V10_3Fields

@[expose] public section

/-!
# Statements: stage V10_3x (paper V4, stage V10-3)

Prime-power bases beyond `tab:primepower` (stage V10-3): improved rows (the same q with another irreducible f) and new rows (s = 2: q = 32, 64, 81, 121, 125, 128; s = 3: q = 128, 169; s = 4: q = 49, 121, 125; s = 5: q = 121, 169) of `prop:primepower` by kernel evaluation, and the coverage of these bases.
PROVED (`GeoSeq/V10_3CovX.lean`, `GeoSeq/V10_3RowsX.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_3x`
(definitions in `GeoSeq/V10_3Fields.lean`). Paper: V4 (`paper/sections/10-frames.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-3). Configuration:
`comparatorGeoSeqV10_3x.json`.
-/

namespace GeoSeq

section G0
open Finset

/-- `s2_q25b`: the digit increments of the power-basis code of `GF25b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q25b : ∀ y : GF25b, digInc PF.code y ∈ PF.pbDelta 5 1 ![3, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q25b`** (`s = 2`, `q = 25`, `f = x^2+3`, weights `(10)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF25b` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 8/25` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (8/25²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q25b (a : Fin 2 → GF25b) (ha : Function.Injective a) (θ : GF25b) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF25b) (hμ : μs ≠ 0) (k : Fin 2 → GF25b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 10] : Fin 1 → GF25b) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (8 / 25) := by
  sorry

/-- `s2_q27b`: the digit increments of the power-basis code of `GF27b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q27b : ∀ y : GF27b, digInc PF.code y ∈ PF.pbDelta 3 2 ![1, 2, 1] := by
  sorry

/-- **`prop:primepower`, row `s2_q27b`** (`s = 2`, `q = 27`, `f = x^3+x^2+2x+1`, weights `(15)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF27b` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 5/27` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (5/27²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q27b (a : Fin 2 → GF27b) (ha : Function.Injective a) (θ : GF27b) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF27b) (hμ : μs ≠ 0) (k : Fin 2 → GF27b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 15] : Fin 1 → GF27b) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (5 / 27) := by
  sorry

/-- `s2_q49b`: the digit increments of the power-basis code of `GF49b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q49b : ∀ y : GF49b, digInc PF.code y ∈ PF.pbDelta 7 1 ![2, 2] := by
  sorry

/-- **`prop:primepower`, row `s2_q49b`** (`s = 2`, `q = 49`, `f = x^2+2x+2`, weights `(21)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF49b` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 19/49` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (19/49²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q49b (a : Fin 2 → GF49b) (ha : Function.Injective a) (θ : GF49b) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF49b) (hμ : μs ≠ 0) (k : Fin 2 → GF49b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 21] : Fin 1 → GF49b) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (19 / 49) := by
  sorry

/-- `s3_q25c`: the digit increments of the power-basis code of `GF25c` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q25c : ∀ y : GF25c, digInc PF.code y ∈ PF.pbDelta 5 1 ![2, 1] := by
  sorry

/-- **`prop:primepower`, row `s3_q25c`** (`s = 3`, `q = 25`, `f = x^2+x+2`, weights `(9, 12)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF25c` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 2/25` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (2/25²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q25c (a : Fin 3 → GF25c) (ha : Function.Injective a) (θ : GF25c) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF25c) (hμ : μs ≠ 0) (k : Fin 3 → GF25c) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 9, PF.dec 12] : Fin 2 → GF25c) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (2 / 25) := by
  sorry

/-- `s3_q81b`: the digit increments of the power-basis code of `GF81b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q81b : ∀ y : GF81b, digInc PF.code y ∈ PF.pbDelta 3 3 ![2, 1, 1, 2] := by
  sorry

/-- **`prop:primepower`, row `s3_q81b`** (`s = 3`, `q = 81`, `f = x^4+2x^3+x^2+x+2`, weights `(3, 9)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF81b` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 2/81` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (2/81²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q81b (a : Fin 3 → GF81b) (ha : Function.Injective a) (θ : GF81b) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF81b) (hμ : μs ≠ 0) (k : Fin 3 → GF81b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 3, PF.dec 9] : Fin 2 → GF81b) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (2 / 81) := by
  sorry

/-- `s3_q121b`: the digit increments of the power-basis code of `GF121b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q121b : ∀ y : GF121b, digInc PF.code y ∈ PF.pbDelta 11 1 ![5, 2] := by
  sorry

/-- **`prop:primepower`, row `s3_q121b`** (`s = 3`, `q = 121`, `f = x^2+2x+5`, weights `(22, 54)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF121b` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 20/121` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (20/121²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q121b (a : Fin 3 → GF121b) (ha : Function.Injective a) (θ : GF121b) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF121b) (hμ : μs ≠ 0) (k : Fin 3 → GF121b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 22, PF.dec 54] : Fin 2 → GF121b) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (20 / 121) := by
  sorry

/-- `s3_q125b`: the digit increments of the power-basis code of `GF125b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q125b : ∀ y : GF125b, digInc PF.code y ∈ PF.pbDelta 5 2 ![4, 0, 4] := by
  sorry

/-- **`prop:primepower`, row `s3_q125b`** (`s = 3`, `q = 125`, `f = x^3+4x^2+4`, weights `(45, 66)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF125b` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 14/125` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (14/125²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q125b (a : Fin 3 → GF125b) (ha : Function.Injective a) (θ : GF125b) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF125b) (hμ : μs ≠ 0) (k : Fin 3 → GF125b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 45, PF.dec 66] : Fin 2 → GF125b) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (14 / 125) := by
  sorry

/-- `s2_q32`: the digit increments of the power-basis code of `GF32` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q32 : ∀ y : GF32, digInc PF.code y ∈ PF.pbDelta 2 4 ![1, 1, 1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q32`** (`s = 2`, `q = 32`, `f = x^5+x^3+x^2+x+1`, weights `(23)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF32` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 7/32` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (7/32²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q32 (a : Fin 2 → GF32) (ha : Function.Injective a) (θ : GF32) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF32) (hμ : μs ≠ 0) (k : Fin 2 → GF32) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 23] : Fin 1 → GF32) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (7 / 32) := by
  sorry

/-- `s2_q64b`: the digit increments of the power-basis code of `GF64b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q64b : ∀ y : GF64b, digInc PF.code y ∈ PF.pbDelta 2 5 ![1, 1, 0, 1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q64b`** (`s = 2`, `q = 64`, `f = x^6+x^4+x^3+x+1`, weights `(45)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF64b` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 13/64` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (13/64²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q64b (a : Fin 2 → GF64b) (ha : Function.Injective a) (θ : GF64b) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF64b) (hμ : μs ≠ 0) (k : Fin 2 → GF64b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 45] : Fin 1 → GF64b) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (13 / 64) := by
  sorry

/-- `s2_q81c`: the digit increments of the power-basis code of `GF81c` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q81c : ∀ y : GF81c, digInc PF.code y ∈ PF.pbDelta 3 3 ![1, 1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q81c`** (`s = 2`, `q = 81`, `f = x^4+x^2+x+1`, weights `(31)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF81c` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 17/81` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (17/81²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q81c (a : Fin 2 → GF81c) (ha : Function.Injective a) (θ : GF81c) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF81c) (hμ : μs ≠ 0) (k : Fin 2 → GF81c) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 31] : Fin 1 → GF81c) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (17 / 81) := by
  sorry

/-- `s2_q121c`: the digit increments of the power-basis code of `GF121c` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q121c : ∀ y : GF121c, digInc PF.code y ∈ PF.pbDelta 11 1 ![9, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q121c`** (`s = 2`, `q = 121`, `f = x^2+9`, weights `(55)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF121c` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 53/121` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (53/121²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q121c (a : Fin 2 → GF121c) (ha : Function.Injective a) (θ : GF121c) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF121c) (hμ : μs ≠ 0) (k : Fin 2 → GF121c) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 55] : Fin 1 → GF121c) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (53 / 121) := by
  sorry

/-- `s2_q125c`: the digit increments of the power-basis code of `GF125c` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q125c : ∀ y : GF125c, digInc PF.code y ∈ PF.pbDelta 5 2 ![3, 3, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q125c`** (`s = 2`, `q = 125`, `f = x^3+3x+3`, weights `(51)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF125c` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 44/125` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (44/125²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q125c (a : Fin 2 → GF125c) (ha : Function.Injective a) (θ : GF125c) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF125c) (hμ : μs ≠ 0) (k : Fin 2 → GF125c) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 51] : Fin 1 → GF125c) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (44 / 125) := by
  sorry

/-- `s2_q128`: the digit increments of the power-basis code of `GF128` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q128 : ∀ y : GF128, digInc PF.code y ∈ PF.pbDelta 2 6 ![1, 1, 1, 1, 1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q128`** (`s = 2`, `q = 128`, `f = x^7+x^5+x^4+x^3+x^2+x+1`, weights `(95)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF128` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 31/128` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (31/128²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q128 (a : Fin 2 → GF128) (ha : Function.Injective a) (θ : GF128) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF128) (hμ : μs ≠ 0) (k : Fin 2 → GF128) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 95] : Fin 1 → GF128) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (31 / 128) := by
  sorry

/-- `s3_q128`: the digit increments of the power-basis code of `GF128` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q128 : ∀ y : GF128, digInc PF.code y ∈ PF.pbDelta 2 6 ![1, 1, 1, 1, 1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q128`** (`s = 3`, `q = 128`, `f = x^7+x^5+x^4+x^3+x^2+x+1`, weights `(56, 95)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF128` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 7/128` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (7/128²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q128 (a : Fin 3 → GF128) (ha : Function.Injective a) (θ : GF128) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF128) (hμ : μs ≠ 0) (k : Fin 3 → GF128) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 56, PF.dec 95] : Fin 2 → GF128) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (7 / 128) := by
  sorry

/-- `s3_q169`: the digit increments of the power-basis code of `GF169` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q169 : ∀ y : GF169, digInc PF.code y ∈ PF.pbDelta 13 1 ![9, 4] := by
  sorry

/-- **`prop:primepower`, row `s3_q169`** (`s = 3`, `q = 169`, `f = x^2+4x+9`, weights `(51, 89)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF169` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 35/169` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (35/169²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q169 (a : Fin 3 → GF169) (ha : Function.Injective a) (θ : GF169) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF169) (hμ : μs ≠ 0) (k : Fin 3 → GF169) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 51, PF.dec 89] : Fin 2 → GF169) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (35 / 169) := by
  sorry

/-- `s4_q49`: the digit increments of the power-basis code of `GF49` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s4_q49 : ∀ y : GF49, digInc PF.code y ∈ PF.pbDelta 7 1 ![1, 0] := by
  sorry

/-- **`prop:primepower`, row `s4_q49`** (`s = 4`, `q = 49`, `f = x^2+1`, weights `(7, 16, 19)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF49` with the power-basis code is a digital `(0,4)`-sequence with `sep(P_{4K}) ≥ 1/49` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/49²) N^{-1/4}`, and quasi-uniform. -/
theorem primepower_s4_q49 (a : Fin 4 → GF49) (ha : Function.Injective a) (θ : GF49) (hθ : θ ≠ 0) (cs : Fin 4)
    (μs : GF49) (hμ : μs ≠ 0) (k : Fin 4 → GF49) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 7, PF.dec 16, PF.dec 19] : Fin 3 → GF49) i) :
    PPConcl PF.code 4 (resStar a θ cs μs k) (1 / 49) := by
  sorry

/-- `s4_q121d`: the digit increments of the power-basis code of `GF121d` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s4_q121d : ∀ y : GF121d, digInc PF.code y ∈ PF.pbDelta 11 1 ![8, 1] := by
  sorry

/-- **`prop:primepower`, row `s4_q121d`** (`s = 4`, `q = 121`, `f = x^2+x+8`, weights `(21, 31, 49)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF121d` with the power-basis code is a digital `(0,4)`-sequence with `sep(P_{4K}) ≥ 7/121` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (7/121²) N^{-1/4}`, and quasi-uniform. -/
theorem primepower_s4_q121d (a : Fin 4 → GF121d) (ha : Function.Injective a) (θ : GF121d) (hθ : θ ≠ 0) (cs : Fin 4)
    (μs : GF121d) (hμ : μs ≠ 0) (k : Fin 4 → GF121d) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 21, PF.dec 31, PF.dec 49] : Fin 3 → GF121d) i) :
    PPConcl PF.code 4 (resStar a θ cs μs k) (7 / 121) := by
  sorry

/-- `s4_q125`: the digit increments of the power-basis code of `GF125` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s4_q125 : ∀ y : GF125, digInc PF.code y ∈ PF.pbDelta 5 2 ![1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s4_q125`** (`s = 4`, `q = 125`, `f = x^3+x+1`, weights `(2, 5, 10)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF125` with the power-basis code is a digital `(0,4)`-sequence with `sep(P_{4K}) ≥ 1/125` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/125²) N^{-1/4}`, and quasi-uniform. -/
theorem primepower_s4_q125 (a : Fin 4 → GF125) (ha : Function.Injective a) (θ : GF125) (hθ : θ ≠ 0) (cs : Fin 4)
    (μs : GF125) (hμ : μs ≠ 0) (k : Fin 4 → GF125) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 2, PF.dec 5, PF.dec 10] : Fin 3 → GF125) i) :
    PPConcl PF.code 4 (resStar a θ cs μs k) (1 / 125) := by
  sorry

/-- `s5_q121`: the digit increments of the power-basis code of `GF121` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s5_q121 : ∀ y : GF121, digInc PF.code y ∈ PF.pbDelta 11 1 ![1, 0] := by
  sorry

/-- **`prop:primepower`, row `s5_q121`** (`s = 5`, `q = 121`, `f = x^2+1`, weights `(13, 28, 36, 47)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF121` with the power-basis code is a digital `(0,5)`-sequence with `sep(P_{5K}) ≥ 1/121` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/121²) N^{-1/5}`, and quasi-uniform. -/
theorem primepower_s5_q121 (a : Fin 5 → GF121) (ha : Function.Injective a) (θ : GF121) (hθ : θ ≠ 0) (cs : Fin 5)
    (μs : GF121) (hμ : μs ≠ 0) (k : Fin 5 → GF121) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 13, PF.dec 28, PF.dec 36, PF.dec 47] : Fin 4 → GF121) i) :
    PPConcl PF.code 5 (resStar a θ cs μs k) (1 / 121) := by
  sorry

/-- `s5_q169b`: the digit increments of the power-basis code of `GF169b` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s5_q169b : ∀ y : GF169b, digInc PF.code y ∈ PF.pbDelta 13 1 ![2, 0] := by
  sorry

/-- **`prop:primepower`, row `s5_q169b`** (`s = 5`, `q = 169`, `f = x^2+2`, weights `(17, 58, 63, 83)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF169b` with the power-basis code is a digital `(0,5)`-sequence with `sep(P_{5K}) ≥ 2/169` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (2/169²) N^{-1/5}`, and quasi-uniform. -/
theorem primepower_s5_q169b (a : Fin 5 → GF169b) (ha : Function.Injective a) (θ : GF169b) (hθ : θ ≠ 0) (cs : Fin 5)
    (μs : GF169b) (hμ : μs ≠ 0) (k : Fin 5 → GF169b) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 17, PF.dec 58, PF.dec 63, PF.dec 83] : Fin 4 → GF169b) i) :
    PPConcl PF.code 5 (resStar a θ cs μs k) (2 / 169) := by
  sorry

end G0

section G1

/-- **Prime-power bases beyond the paper** (new rows of `prop:primepower`, exact search + kernel certificates):
explicit digital `(0,s)`-sequences with a positive bound at every full level, quasi-uniform, for `s = 2`:
`q = 32, 64, 81, 121, 125, 128`; `s = 3`: `q = 128, 169`; `s = 4`: `q = 49, 121, 125`; `s = 5`: `q = 121, 169`. -/
theorem coverage_pp_new :
    (∃ C : Gen 2 GF32, Covered PF.code 2 C (levFull 2)) ∧
    (∃ C : Gen 2 GF64b, Covered PF.code 2 C (levFull 2)) ∧
    (∃ C : Gen 2 GF81c, Covered PF.code 2 C (levFull 2)) ∧
    (∃ C : Gen 2 GF121c, Covered PF.code 2 C (levFull 2)) ∧
    (∃ C : Gen 2 GF125c, Covered PF.code 2 C (levFull 2)) ∧
    (∃ C : Gen 2 GF128, Covered PF.code 2 C (levFull 2)) ∧
    (∃ C : Gen 3 GF128, Covered PF.code 3 C (levFull 3)) ∧
    (∃ C : Gen 3 GF169, Covered PF.code 3 C (levFull 3)) ∧
    (∃ C : Gen 4 GF49, Covered PF.code 4 C (levFull 4)) ∧
    (∃ C : Gen 4 GF121d, Covered PF.code 4 C (levFull 4)) ∧
    (∃ C : Gen 4 GF125, Covered PF.code 4 C (levFull 4)) ∧
    (∃ C : Gen 5 GF121, Covered PF.code 5 C (levFull 5)) ∧
    (∃ C : Gen 5 GF169b, Covered PF.code 5 C (levFull 5)) := by
  sorry

end G1

end GeoSeq
