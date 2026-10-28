/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs
public import Z3Net.FDefs

@[expose] public section

/-!
# Statements: nets, sequences and separation (`sec:prelim`), GeoSeq stage S0

* `lem:t0` (`t0`): a frame (distinct places) with arbitrary lower-triangular scrambles is a
  `(0,s)`-sequence. PROVED in stage S1 (`GeoSeq/T0.lean`, via geo `lem:nie`, `lem:hermite`,
  `lowerTri_kill`).
* Stage S1: sequences ↔ nets (`blockNet0_iff`, `isSeq0_iff_trunc`, `block_shift`;
  `GeoSeq/SeqNet.lean`); self-similar scrambles are scrambled frames (`ss_eq_scr`, `ssScr_diag`,
  `ss_t0`; `GeoSeq/SSFrame.lean`). PROVED.
* `lem:prefix`, separation half (`prefix_sep`). PROVED (`GeoSeq/Prefix.lean`).

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset

/-- **`lem:t0`** (frames have `t = 0`): for distinct places `a_c ∈ 𝔽_q` and lower-triangular
scrambles `L_c` with nonzero diagonal, `C_c = L_c P_{a_c}` is a `(0,s)`-sequence in base `q`. -/
theorem t0 {R : Type*} [Field R] [Fintype R] [DecidableEq R] {q s : ℕ} [NeZero q]
    (D : DigitCode R q) (a : Fin s → R) (ha : Function.Injective a)
    (L : Fin s → ℕ → ℕ → R) (hL : ∀ c n, L c n n ≠ 0) :
    IsSeq0 D (scrGen a L) := by
  sorry

/-- **`lem:prefix`** (separation half): full-level separation `LB` for all `K ≥ 1` gives
`δ(P_{[N]}) ≥ (LB/q) · N^{-1/s}` for all `N ≥ 2`. -/
theorem prefix_sep (q s : ℕ) (hq : 2 ≤ q) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ) (LB : ℝ)
    (hLB : 0 ≤ LB) (h : ∀ K : ℕ, 1 ≤ K → SepAtLevel q s K pt LB) :
    SepAllN s pt (LB / q) := by
  sorry


/-! ## Stage S1: sequences and nets (`sec:prelim`) -/

section SeqNet

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **Blocks and prefixes** (`sec:prelim`): block `k` of `q^m` points is a `(0,m,s)`-net iff the
truncated generator matrices form a `(0,m,s)`-net (geo `lem:nie` form `Z3NetF.IsNet0E`). -/
theorem blockNet0_iff (D : DigitCode R q) (C : Gen s R) (m k : ℕ) :
    BlockNet0 D C m k ↔ Z3NetF.IsNet0E D.enc (truncGen C m) := by
  sorry

/-- **`IsSeq0` ↔ prefixes are nets** (`sec:prelim`): a digital sequence is a `(0,s)`-sequence iff for
every `m` the truncated generator matrices form a `(0,m,s)`-net (geo `Z3NetF.IsNet0E`); every block
is a digital shift of the prefix (`block_shift`) and has the same box minors. -/
theorem isSeq0_iff_trunc (D : DigitCode R q) (C : Gen s R) :
    IsSeq0 D C ↔ ∀ m : ℕ, Z3NetF.IsNet0E D.enc (truncGen C m) := by
  sorry

/-- **Blocks are digital shifts of the prefix** (`sec:prelim`): for `v < q^m`, digit `n` of
coordinate `c` of `y(k q^m + v)` is digit `n` of `y(v)` plus digit `n` of the point `k` of the
column-shifted sequence `shiftCols C m` (a constant of the block). -/
theorem block_shift (D : DigitCode R q) (C : Gen s R) (m k v : ℕ) (hv : v < q ^ m) (c : Fin s)
    (n : ℕ) :
    seqDigit D C (k * q ^ m + v) c n = seqDigit D C v c n + seqDigit D (shiftCols C m) k c n := by
  sorry

end SeqNet

/-! ## Stage S1: self-similar scrambles are scrambled frames (`def:selfsim`, `lem:t0`) -/

section SSFrame

open PowerSeries

variable {R : Type*} [CommRing R] {s : ℕ}

/-- **Self-similar scrambles are scrambled frames** (`def:selfsim`, `lem:t0`):
`ssGen g zθ = scrGen (ssPlace zθ) (ssScr g zθ)`. -/
theorem ss_eq_scr (g zθ : Fin s → PowerSeries R) :
    ssGen g zθ = scrGen (ssPlace zθ) (ssScr g zθ) := by
  sorry

/-- The diagonal of the scramble of a self-similar scramble: `L_c[n][n] = g_c(0) ([x^1] z_c)^n`. -/
theorem ssScr_diag (g zθ : Fin s → PowerSeries R) (c : Fin s) (n : ℕ) :
    ssScr g zθ c n n = constantCoeff (g c) * coeff 1 (zθ c) ^ n := by
  sorry

/-- **Self-similar scrambles have `t = 0`** (`lem:t0`): distinct places `z_c(0)`, `g_c(0) ≠ 0` and
`[x^1] z_c ≠ 0`. -/
theorem ss_t0 {K : Type*} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [NeZero q]
    (D : DigitCode K q) (g zθ : Fin s → PowerSeries K)
    (hplace : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hz : ∀ c, coeff 1 (zθ c) ≠ 0) : IsSeq0 D (ssGen g zθ) := by
  sorry

end SSFrame

end GeoSeq
