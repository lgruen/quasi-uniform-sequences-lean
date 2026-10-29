/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1SignDefs

@[expose] public section

/-!
# Statements: stage V10_1 (paper V4, stage V10-1)

Side clauses (stage V10-1): the `limsup` clauses of `cor:layer`(a) and `cor:density` (covering by admissible ranges), `prop:joint`(ii) for a general local multiplier, equality in `thm:block`(c) for `s = 4, 5` (the binding axis step, every prime), `rem:randomize` (a) digital shifts, (b) index scrambles, (c) reorderings keeping a level family, `rem:residuefull` (inclusion bound), the offset-map phrasing of `cor:N1`; the sign-class bound and the block designs with the smaller free diagonal (`s = 4`: `1 - 4/p`, `p >= 11`; `s = 5`: `1 - 8/p`, `p >= 67`, and `p >= 23` given the kernel evaluations).
PROVED (`GeoSeq/V10_1Blk.lean`, `GeoSeq/V10_1Dens.lean`, `GeoSeq/V10_1Diag4.lean`, `GeoSeq/V10_1Diag5.lean`, `GeoSeq/V10_1Joint.lean`, `GeoSeq/V10_1Misc.lean`, `GeoSeq/V10_1Rand.lean`, `GeoSeq/V10_1Shift.lean`, `GeoSeq/V10_1Sign.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_1`
(definitions in `GeoSeq/V10_1SignDefs.lean`). Paper: V4 (`paper/sections/07-count.tex, 08-antipode.tex, A-machinery.tex, 06-block.tex, 03-fail.tex, 05-residue.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-1). Configuration:
`comparatorGeoSeqV10_1.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial

/-- **Covering by admissible ranges of one length** (`cor:layer`(a), proof): if a weight `g ≤ B` on the levels obeys
the count `∑_{T ∈ [K₀, K₀+R]} g T ≤ J + R + 1` on every range admissible for depth `J` (`K₀ ≥ J`,
`K₀ > (s-1)R + s - 2`), then for every `R` and `X`, with `T₁ = J + (s-1)R + s + 1`,
`∑_{T < X} g T ≤ B T₁ + (⌊X/(R+1)⌋ + 1)(J + R + 1)`. -/
theorem dens_ranges_bound (g : ℕ → ℕ) (B s J : ℕ) (hB : ∀ T, g T ≤ B)
    (h : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1)
    (R X : ℕ) :
    ∑ T ∈ range X, g T ≤ B * (J + (s - 1) * R + s + 1) + (X / (R + 1) + 1) * (J + R + 1) := by
  sorry

/-- `cor:layer`(a), density form, for a general weight: `∑_{T ∈ [1,X]} g T ≤ (1 + ε) X` for all large `X`. -/
theorem dens_ranges_eps (g : ℕ → ℕ) (B s J : ℕ) (hB : ∀ T, g T ≤ B)
    (h : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) ≤ (1 + ε) * X := by
  sorry

/-- `cor:layer`(a), `limsup` form, for a general weight: `limsup_{X → ∞} (∑_{T ∈ [1,X]} g T)/X ≤ 1`. -/
theorem dens_ranges_limsup (g : ℕ → ℕ) (B s J : ℕ) (hB : ∀ T, g T ≤ B)
    (h : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1) :
    Filter.limsup (fun X : ℕ => ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) / X) Filter.atTop ≤ 1 := by
  sorry

end G0

section G1
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **`cor:layer`(a), density clause**: the set `E` of levels `T` at which all `s` geometric digits of `P_{sT}` are
designed by exact relations of depth at most `J` has upper density at most `1/s`: `s |E ∩ [1,X]| ≤ (1 + ε) X` for all
large `X`, and `limsup_{X → ∞} |E ∩ [1,X]|/X ≤ 1/s` (any field, distinct places, any scramble, `s ≥ 1`). -/
theorem layer_a_density (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (J : ℕ) [DecidablePred (AllDesigned a L J)] :
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (s : ℝ) * ((Icc 1 X).filter (AllDesigned a L J)).card ≤ (1 + ε) * X) ∧
    Filter.limsup (fun X : ℕ => (((Icc 1 X).filter (AllDesigned a L J)).card : ℝ) / X) Filter.atTop ≤
      1 / s := by
  sorry

/-- **`cor:density`, `limsup` clause**: with `E` (all geometric digits of `P_{sT}` designed with depth `≤ J`) and `S`
(a skeleton relation on `P_{s(T+1)-1}`), `|S ∩ [1,X]| + (s-1)|E ∩ [1,X]| ≤ (1 + ε) X` for all large `X`, and
`limsup_{X → ∞} (|S ∩ [1,X]| + (s-1)|E ∩ [1,X]|)/X ≤ 1` (any field, distinct places, any scramble, `s ≥ 1`). -/
theorem density_limsup (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (J : ℕ) [DecidablePred (AllDesigned a L J)] [DecidablePred (HasSkel a L)] :
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Icc 1 X).filter (HasSkel a L)).card : ℝ) + (s - 1 : ℕ) * ((Icc 1 X).filter (AllDesigned a L J)).card ≤
        (1 + ε) * X) ∧
    Filter.limsup (fun X : ℕ => ((((Icc 1 X).filter (HasSkel a L)).card : ℝ) +
      (s - 1 : ℕ) * ((Icc 1 X).filter (AllDesigned a L J)).card) / X) Filter.atTop ≤ 1 := by
  sorry

/-- **`cor:density`, "in particular"**: if the densities `d_S` of `S` and `d_E` of `E` exist (as limits of
`|S ∩ [1,X]|/X` and `|E ∩ [1,X]|/X`), then `d_S + (s-1) d_E ≤ 1`. -/
theorem density_dens (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (J : ℕ) [DecidablePred (AllDesigned a L J)] [DecidablePred (HasSkel a L)] (dS dE : ℝ)
    (hS : Filter.Tendsto (fun X : ℕ => (((Icc 1 X).filter (HasSkel a L)).card : ℝ) / X) Filter.atTop (nhds dS))
    (hE : Filter.Tendsto (fun X : ℕ => (((Icc 1 X).filter (AllDesigned a L J)).card : ℝ) / X) Filter.atTop
      (nhds dE)) :
    dS + (s - 1 : ℕ) * dE ≤ 1 := by
  sorry

/-- **`cor:density`, last clause**: a skeleton relation at every level of an admissible range `I = [K₀, K₀ + R]`
leaves room for at most `J/(s-1)` design levels in it: `(s-1) |E ∩ I| ≤ J`. -/
theorem density_skel_range (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (hL : IsScramble L) (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀)
    [DecidablePred (AllDesigned a L J)] [DecidablePred (HasSkel a L)]
    (hS : ∀ T, K₀ ≤ T → T ≤ K₀ + R → HasSkel a L T) :
    (s - 1) * ((Icc K₀ (K₀ + R)).filter (AllDesigned a L J)).card ≤ J := by
  sorry

end G1

section G2
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- A simple pole: `Res_a(H / ((z - a) U) dz) = H(a)/U(a)`. -/
theorem locRes_one_eval (a : F) (H U : F[X]) : locRes a 1 H U = H.eval a * (U.eval a)⁻¹ := by
  sorry

/-- If `Res_a(H / ((z - a)^{n+1} U W^{n+1}) dz) = 0` for all `n < M` (`U(a), W(a) ≠ 0`), then `(z - a)^M ∣ H`. -/
theorem dvd_of_locRes_low (a : F) (H U W : F[X]) (hU : U.eval a ≠ 0) (hW : W.eval a ≠ 0) :
    ∀ M : ℕ, (∀ n < M, locRes a (n + 1) H (U * W ^ (n + 1)) = 0) → (X - C a) ^ M ∣ H := by
  sorry

/-- **`prop:joint`(ii), general multiplier**: two self-similar scrambles in residue form that differ only in the
local multiplier of coordinate `c`, with `φ'_c ≡ φ_c (mod (z - a_c)^l)` (i.e. `(z - a_c)^l ∣ N'_c U_c - N_c U'_c`),
and correction coefficients `χ`, `χ'` up to order `K + 1` for the same `v` (`v_c ≠ 0`). Then at every full level
`K ≥ l ≥ 1` the cross responses `X^{(l)}_{c'←c}` (carry length `l` in coordinate `c`) coincide and
`O^{(l)}_c + Ψ_c(l)` coincides. -/
theorem joint_transfer_gen (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U N' U' : Fin s → F[X]) (c : Fin s) (hN' : ∀ c', c' ≠ c → N' c' = N c')
    (hU' : ∀ c', c' ≠ c → U' c' = U c') (hU : ∀ c, (U c).eval (a c) ≠ 0) (hUc : (U' c).eval (a c) ≠ 0)
    (hNc : (N' c).eval (a c) ≠ 0) (v : Fin s → F) (hv : v c ≠ 0) (χ χ' : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (hχ0' : ∀ c, χ' c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTrunc a θ N U v χ (K + 1)) (htr' : CorrTrunc a θ N' U' v χ' (K + 1)) (l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) (hcong : (X - C (a c)) ^ l ∣ N' c * U c - N c * U' c) (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (ssResGen a θ N U) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (ssResGen a θ N' U') K 0 l c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧ Dnew c + psiSum χ' c l = Dold c + psiSum χ c l := by
  sorry

/-- Same `v_c` and the same correction coefficients `χ_{c,d}`, `d < l`, give `φ'_c ≡ φ_c (mod (z - a_c)^l)`. -/
theorem cong_of_corrTrunc (a : Fin s → F) (θ : F) (N U N' U' : Fin s → F[X]) (c : Fin s) (v : Fin s → F)
    (χ χ' : Fin s → ℕ → F) (K l : ℕ) (hlK : l ≤ K + 1) (htr : CorrTrunc a θ N U v χ (K + 1))
    (htr' : CorrTrunc a θ N' U' v χ' (K + 1)) (hχ : ∀ d, d < l → χ' c d = χ c d) :
    (X - C (a c)) ^ l ∣ N' c * U c - N c * U' c := by
  sorry

/-- **`prop:joint`(ii)** (as stated): for every column `c` and depth `l`, `O^{(l)}_c + Ψ_c(l)` and the cross responses
`X^{(l)}_{c'←c}` depend only on `v_c`, `χ_{c,1}, …, χ_{c,l-1}`, `θ` and the local multipliers of the other
coordinates: two self-similar scrambles in residue form that differ only in the multiplier of coordinate `c`, with
the same `v` and correction coefficients agreeing below `l` in coordinate `c`, have the same crosses and the same
`O^{(l)}_c + Ψ_c(l)` at every full level `K ≥ l ≥ 1`. -/
theorem joint_ii (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U N' U' : Fin s → F[X]) (c : Fin s) (hN' : ∀ c', c' ≠ c → N' c' = N c')
    (hU' : ∀ c', c' ≠ c → U' c' = U c') (hU : ∀ c, (U c).eval (a c) ≠ 0) (hUc : (U' c).eval (a c) ≠ 0)
    (hNc : (N' c).eval (a c) ≠ 0) (v : Fin s → F) (hv : v c ≠ 0) (χ χ' : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (hχ0' : ∀ c, χ' c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTrunc a θ N U v χ (K + 1)) (htr' : CorrTrunc a θ N' U' v χ' (K + 1)) (l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) (hχ : ∀ d, d < l → χ' c d = χ c d) (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (ssResGen a θ N U) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (ssResGen a θ N' U') K 0 l c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧ Dnew c + psiSum χ' c l = Dold c + psiSum χ c l := by
  sorry

end G2

section G3
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- `f_1(0, t) = 0` for a non-moving coordinate with `|t| ≤ 1`. -/
theorem gap_zero_small (t : ℤ) (ht : |t| ≤ 1) : gapNum1 p 0 (t : ZMod p) = 0 := by
  sorry

/-- **The binding configuration** (`thm:block`(c), equality): for a design with partial sums `M^{(j)}` (`hM`), the
axis step `e = 𝟏_c` with carry lengths `1` is a step at every level `K ≥ 1`, and if `M^{(0)}[c][c] = -α` with
`α < p` and `|M^{(0)}[i][c]| ≤ 1` for `i ≠ c`, its term `(∑_i f_1(e_i, σ_i)²)^{1/2}` equals `(p - α - 1)/p`. -/
theorem axis_term {s : ℕ} (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c) (c : Fin s) (α : ℕ)
    (hα : Mz 0 c c = -α) (hαp : α < p) (hcol : ∀ i, i ≠ c → |Mz 0 i c| ≤ 1) (K : ℕ) (hK : 1 ≤ K) :
    IsStep K (Pi.single c 1) (fun _ => 1) ∧
      Real.sqrt (∑ i, ((gapNum1 p ((Pi.single c (1 : ℤ) : Fin s → ℤ) i) (∑ c', (((Pi.single c (1 : ℤ) :
        Fin s → ℤ) c' : ℤ) : ZMod p) * ∑ n ∈ range (min ((fun _ => 1 : Fin s → ℕ) c') (s - 1)),
          blockF Fz n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - α - 1) / p := by
  sorry

/-- **`thm:block`(c), `s = 4`, equality** `LB(F) = 1 - 6/p` at EVERY prime `p ≥ 7`: every step has a term
`≥ 1 - 6/p` (stage V9-9: written range `p ≥ 29`, kernel evaluations `7 ≤ p ≤ 23`), and the axis step along the place
`0` with carry length `1` has the term exactly `1 - 6/p`. -/
theorem blk4_LB_eq (hp : 7 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 6) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 6) / p := by
  sorry

/-- **`thm:block`(c), `s = 5`, the upper bound** `LB(F) ≤ 1 - 17/p` at every prime `p ≥ 18`: the axis step along the
place `0` with carry length `1` has the term exactly `1 - 17/p`. -/
theorem blk5_LB_attained (hp : 18 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p := by
  sorry

/-- **`thm:block`(c), `s = 5`, equality on the written range**: `LB(F) = 1 - 17/p` for every prime `p ≥ 84`. -/
theorem blk5_LB_eq_proof (hp : 84 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p := by
  sorry

/-- **`thm:block`(c), `s = 5`, equality** `LB(F) = 1 - 17/p` at every prime `p ≥ 19`, given the kernel evaluations
`Blk5CA` of stage V9-9 (`blk5_chk19` … `blk5_chk83`, compared separately; the unconditional form is
`blk5_LB_eq` in `GeoSeq/V10_1Blk5U.lean`). -/
theorem blk5_LB_eq_of (hca : Blk5CA) (hp : 19 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 17) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5F n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 17) / p := by
  sorry

end G3

section G4
open Finset Polynomial
variable {s : ℕ}

/-- Close pairs at arbitrary levels give close pairs at the levels of a family with gaps `≤ Δ`
(`rem:randomize`(c)). -/
theorem close_lev {p : ℕ} (hp : 1 ≤ p) (pt : ℕ → Fin s → ℝ) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, Lev m ∧ v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
  sorry

/-- **`rem:randomize`(c), general level family**: if a sequence has close pairs (as in `thm:nonqu`), then every
reordering `σ` that permutes the prefix `{0, …, p^m - 1}` for every `m` of a level family with bounded gaps gives a
sequence that is not quasi-uniform. -/
theorem not_qu_comp_lev {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (Lev : ℕ → Prop) (Δ : ℕ) (hgap : HasGap Lev Δ) (σ : ℕ → ℕ)
    (hσ : ∀ m, Lev m → ∀ v, v < p ^ m → ∃ v', v' < p ^ m ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (pt ∘ σ) := by
  sorry

theorem hasGap_full (hs : 1 ≤ s) : HasGap (levFull s) s := by
  sorry

/-- **`rem:randomize`(c)** (as stated): reorderings that keep every full level `P_{sK}` as a set do not restore
quasi-uniformity of a sequence with close pairs (every sequence covered by `thm:nonqu`, `nonqu`). -/
theorem not_qu_comp_full {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (σ : ℕ → ℕ)
    (hσ : ∀ K, 1 ≤ K → ∀ v, v < p ^ (s * K) → ∃ v', v' < p ^ (s * K) ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (pt ∘ σ) := by
  sorry

end G4

section G5
open Finset Polynomial
variable {F : Type*} [Field F]
variable {s : ℕ}

/-- **Back substitution**: an upper-triangular `U` with nonzero diagonal maps the polynomials of degree `< m` onto
themselves. -/
theorem uMul_surj (U : ℕ → ℕ → F) (hU : ∀ k, U k k ≠ 0) :
    ∀ m : ℕ, ∀ W : F[X], W.degree < (m : WithBot ℕ) → ∃ V : F[X], V.degree < (m : WithBot ℕ) ∧ uMul U V = W := by
  sorry

/-- The digits of the index scramble `C U` at `V` are the digits of `C` at `U V`. -/
theorem genY_idxScr (C : Gen s F) (U : ℕ → ℕ → F) (c : Fin s) (V : F[X]) (n : ℕ) :
    genY (idxScr C U) c V n = genY C c (uMul U V) n := by
  sorry

end G5

section G6
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- `ι(idxPoly(v)) = v`. -/
theorem polyIdx_idxPolyP (v : ℕ) : polyIdx p (idxPolyP p v) = v := by
  sorry

/-- The index scramble is the reordering `v ↦ ι(U · idxPoly(v))` of the original sequence. -/
theorem seqPoint_idxScr (C : Gen s (ZMod p)) (U : ℕ → ℕ → ZMod p) (v : ℕ) :
    seqPoint (zcode p) (idxScr C U) v = seqPoint (zcode p) C (polyIdx p (uMul U (idxPolyP p v))) := by
  sorry

/-- **`rem:randomize`(b), index scrambles**: for `U` upper triangular with nonzero diagonal (one `U` for all
coordinates, Faure–Tezuka), every prefix `P_m` of `C U` is the same set as the prefix `P_m` of `C`. -/
theorem idxScr_prefix (C : Gen s (ZMod p)) (U : ℕ → ℕ → ZMod p) (hU : ∀ k, U k k ≠ 0) (m : ℕ) :
    (∀ v, v < p ^ m → ∃ v', v' < p ^ m ∧ seqPoint (zcode p) (idxScr C U) v' = seqPoint (zcode p) C v) ∧
    (∀ v', v' < p ^ m → ∃ v, v < p ^ m ∧ seqPoint (zcode p) (idxScr C U) v' = seqPoint (zcode p) C v) := by
  sorry

/-- **`rem:randomize`(b), index scrambles**: if the generator-matrix sequence `C` has close pairs (as every sequence
covered by `thm:nonqu`), its index scramble `C U` (`U` upper triangular, nonzero diagonal) is not quasi-uniform. -/
theorem idxScr_not_qu (hs : 1 ≤ s) (C : Gen s (ZMod p)) (U : ℕ → ℕ → ZMod p) (hU : ∀ k, U k k ≠ 0)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (seqPoint (zcode p) C v) (seqPoint (zcode p) C w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (seqPoint (zcode p) (idxScr C U)) := by
  sorry

end G6

section G7
open Finset Polynomial

/-- The carry with arbitrary tails: digits `x = ⋯ a (p-1)^{L-k-1} ⋯` and `x' = ⋯ (a+1) 0^{L-k-1} ⋯` (equal before
position `k`): `|y(x') - y(x)| ≤ 2 p^{-L}`. -/
theorem real_carry_le {p : ℕ} (hp : 2 ≤ p) (d d' : ℕ → ℕ) (hd : ∀ j, d j < p) (hd' : ∀ j, d' j < p)
    {k L : ℕ} (hkL : k < L) (h0 : ∀ j, j < k → d j = d' j) (h1 : d' k = d k + 1)
    (h2 : ∀ j, k < j → j < L → d j = p - 1 ∧ d' j = 0) :
    |∑' j, (d' j : ℝ) / (p : ℝ) ^ (j + 1) - ∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1)| ≤ 2 / (p : ℝ) ^ L := by
  sorry

end G7

section G8
open Finset Polynomial
variable {F : Type*} [Field F]

/-- The `b`-adic digits of `∑_{j<n} a_j b^j` (`deg a_j < deg b`) are the `a_j`. -/
theorem badicDigit_sum {b : F[X]} :
    ∀ (n : ℕ) (as : ℕ → F[X]), (∀ j, (as j).natDegree < b.natDegree) →
      ∀ Q, badicDigit b (∑ j ∈ range n, as j * b ^ j) Q = if Q < n then as Q else 0 := by
  sorry

/-- **Prescribed leading digits of a radical inverse**: for a `b`-adic radical inverse (digit map onto the digit
blocks) and any target digits `t`, some `W` of degree `< e λ` has the digits `t_n` at all positions `n < e λ`. -/
theorem radInv_prefix {Y : F[X] → ℕ → F} {b : F[X]} {π : F[X] → ℕ → F} (hb : 1 ≤ b.natDegree)
    (hrad : IsRadInv Y b π) (t : ℕ → F) (l : ℕ) (hl : 1 ≤ l) :
    ∃ W : F[X], W.natDegree < b.natDegree * l ∧ ∀ n, n < b.natDegree * l → Y W n = t n := by
  sorry

end G8

section G9
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`lem:carrypair` for digitally shifted sequences** (`rem:randomize`(a)): with the hypotheses of `lem:carrypair`
on the linear coordinates `Y` (only `g` with `π(g) = (1, …, 1)` is needed) and ANY digital shift `σ`, some `V_1` of
degree `< m` and `V_1 + D` (indices `< p^m`, distinct) have shifted points at Euclidean distance
`≤ √(s+3) p^{-L}`, `L = eλ`. -/
theorem shift_pair (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (σ : Fin s → ℕ → ZMod p) (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g : (ZMod p)[X]) (hg : g.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (D : (ZMod p)[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    ∃ V : (ZMod p)[X], polyIdx p V < p ^ m ∧ polyIdx p (V + D) < p ^ m ∧ polyIdx p V ≠ polyIdx p (V + D) ∧
      euclDist (linPt p (shiftY Y σ) (polyIdx p V)) (linPt p (shiftY Y σ) (polyIdx p (V + D))) ≤
        Real.sqrt (s + 3) / (p : ℝ) ^ ((b ch).natDegree * l) := by
  sorry

/-- The conditions (i)–(iii) of `lem:carrypair` for the difference `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}` of `thm:nonqu`
(`Q = p^w`), and `e λ_Q = L_Q = Q E (k+1)` (the computation inside `nonqu_pair`). -/
theorem nonquD_props (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g : (ZMod p)[X]) (hg : g.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (hs : 1 ≤ s) (w : ℕ) :
    nonquD b ch g ν k η (p ^ w) ≠ 0 ∧
      b ch ^ (p ^ w * (η + ν)) ∣ nonquD b ch g ν k η (p ^ w) -
        g * b ch ^ (p ^ w * η) * runS (b ch) (p ^ w * (η + ν) - p ^ w * η) ∧
      (∀ c, c ≠ ch → ∃ j, (b ch).natDegree * (p ^ w * (η + ν)) ≤ (b c).natDegree * j ∧
        b c ^ j ∣ nonquD b ch g ν k η (p ^ w)) ∧
      (nonquD b ch g ν k η (p ^ w)).natDegree < p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) ∧
      (b ch).natDegree * (p ^ w * (η + ν)) = p ^ w * lcmDeg b * (k + 1) := by
  sorry

/-- **`rem:randomize`(a)** (digital shifts): let the linear coordinates `Y` satisfy the hypotheses of `thm:nonqu`
(pairwise coprime bases of degree `≥ 1`, coordinate `ĉ` a `b_ĉ`-adic radical inverse, the others `b_c`-adic), and
let `σ_{c,n} ∈ 𝔽_p` be any digital shift. Then for every `ε > 0` some prefix `P_m` of the shifted sequence contains
two points at Euclidean distance `< ε p^{-m/s}`, and the shifted sequence is not quasi-uniform. -/
theorem shift_nonqu (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (σ : Fin s → ℕ → ZMod p) (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (linPt p (shiftY Y σ) v) (linPt p (shiftY Y σ) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPt p (shiftY Y σ)) := by
  sorry

end G9

section G10
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`rem:residuefull`** (inclusion bound): for the residue sequence (`s ≥ 2`, distinct places, `θ ≠ 0`, `v_c ≠ 0`),
every full level satisfies `sep(P_{sK}) ≥ ℓ_jit(Λ_v)/p`: any two distinct points of `P_{sK}` have toroidal distance
`≥ ℓ_jit(Λ_v) p^{-(K+1)}`. -/
theorem residue_full (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p) (hθ : θ ≠ 0)
    (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (K : ℕ) :
    SepAtLevel p s K (seqPoint (zcode p) (resSeq a θ v)) (ljit v / p) := by
  sorry

end G10

section G11
open Finset Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`cor:N1`, offset-map phrasing** ("in particular"): for the frame `a_0 = 0`, `a_1 = 1` and any scramble
`(L_0, L_1)` (nonzero diagonal) over a finite field, the offset map is not finest-digit (every carry response
`D(l)[c][c']`, `1 ≤ l ≤ K`, independent of `l`: a sheared lattice without jumps) at two consecutive levels
`K, K + 1 ≥ 2`. -/
theorem N1_offset (L : Fin 2 → ℕ → ℕ → F) (hL : ∀ c n, L c n n ≠ 0) (K : ℕ) (hK : 2 ≤ K) :
    ¬ ((∀ c c', LawFinest (scrGen ![0, 1] L) K c c') ∧ ∀ c c', LawFinest (scrGen ![0, 1] L) (K + 1) c c') := by
  sorry

end G11

section G12
open Finset Polynomial
variable {s : ℕ}

/-- `|σ_i| ≤ ∑_c B_{ic}` for every step. -/
theorem caSig_abs_le (Mz : ℕ → Fin s → Fin s → ℤ) (Bd : Fin s → Fin s → ℤ)
    (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (hs : 2 ≤ s) (e : Fin s → ℤ) (l : Fin s → ℕ)
    (he : ∀ c, -1 ≤ e c ∧ e c ≤ 1) (hl : ∀ c, 1 ≤ l c) (i : Fin s) : |stepSig Mz e l i| ≤ ∑ c, Bd i c := by
  sorry

/-- **The sign-class condition from one kernel evaluation**: if at one prime `P` with `S < P` and
`s S² + 2A + 3 < 2P` every step has a term `≥ 1 - (A+1)/P` (e.g. `caCheck_sound` at `P`), then `SignClass Mz A`. -/
theorem ca_signclass (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (Bd : Fin s → Fin s → ℤ) (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (S A : ℕ)
    (hS : ∀ i, ∑ c, Bd i c ≤ S) (P : ℕ) [Fact P.Prime] (hSP : S < P) (hbig : s * S ^ 2 + 2 * A + 3 < 2 * P)
    (hP : ∀ K e l, IsStep K e l → ((P : ℝ) - A - 1) / P ≤ Real.sqrt (∑ i, ((gapNum1 P (e i)
      (∑ c', (e c' : ZMod P) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / P) ^ 2)) :
    SignClass Mz A := by
  sorry

end G12

section G13
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- A coordinate that is not backward (`e = 0`, or `e t > 0`) has `f_1(e, t) p ≤ |t|` (`|t| < p`). -/
theorem gap_nonback_le (e t : ℤ) (he : e = 0 ∨ e = 1 ∨ e = -1) (hnb : ¬ (e ≠ 0 ∧ e * t ≤ 0)) (ht : |t| < p) :
    (gapNum1 p e (t : ZMod p) : ℤ) ≤ |t| := by
  sorry

end G13

section G14
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **The sign-class bound** (generalizes the diagonal-dominance argument `dom_LB`): under `SignClass Mz A`, for every
prime `p` with `S < p` (`S` bounds the row sums of `|M^{(j)}|`), `A ≤ S` and `(p - A - 1)² ≤ 2 (p - S - 1)²`, every step
has a term `≥ 1 - (A+1)/p`, i.e. `LB(F) ≥ 1 - (A+1)/p`. -/
theorem sc_LB (hs : 2 ≤ s) (Fz Mz : ℕ → Fin s → Fin s → ℤ)
    (hM : ∀ j, j + 2 ≤ s → ∀ i c, Mz j i c = ∑ n ∈ range (j + 1), Fz n i c)
    (Bd : Fin s → Fin s → ℤ) (hB : ∀ j, j + 2 ≤ s → ∀ i c, |Mz j i c| ≤ Bd i c) (S A : ℕ)
    (hS : ∀ i, ∑ c, Bd i c ≤ S) (hSp : S < p) (hAS : A ≤ S)
    (hq : ((p : ℤ) - A - 1) ^ 2 ≤ 2 * ((p : ℤ) - S - 1) ^ 2) (hcl : SignClass Mz A) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - A - 1) / p ≤ Real.sqrt (∑ i, ((gapNum1 p (e i)
      (∑ c', (e c' : ZMod p) * ∑ n ∈ range (min (l c') (s - 1)), blockF Fz n i c') : ℝ) / p) ^ 2) := by
  sorry

end G14

section G15
open Finset Polynomial

/-- The sign-class condition for `blk4dF` with `A = 3`, from the evaluation at `P = 137`. -/
theorem blk4d_signclass : SignClass blk4dM 3 := by
  sorry

end G15

section G16
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- `LB(F) ≥ 1 - 4/p` for `blk4dF` at every prime `p ≥ 11`. -/
theorem blk4d_LB (hp : 11 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 4) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c), `s = 4`, smaller diagonal: `LB(F) = 1 - 4/p`** at every prime `p ≥ 11`: every step has a term
`≥ 1 - 4/p`, and the axis step along the place `0` (carry length `1`) has the term exactly `1 - 4/p`. -/
theorem blk4d_LB_eq (hp : 11 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 4) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (4 - 1)), blockF blk4dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 4) / p := by
  sorry

/-- Identity (a) of `def:block` for `blk4dF` (the off-diagonal entries are those of `U*_4`). -/
theorem blk4d_hrel (hp : 5 ≤ p) (c i : Fin 4) (h : i ≠ c) :
    wCoCo (blk4a (p := p)) c i = -C (blk4v i) *
      ∑ n ∈ range (4 - 1), C (blockF blk4dF n i c) * blk4N c (4 - 1 - n) := by
  sorry

/-- **`thm:block`(c), `s = 4`, with the smaller free diagonal**: places `(0, 1, 1/2, 1/3)`, `v = (1, 1, 2, 3)`, the
design `blk4dF` (`U*_4` off the diagonal, `F_0[c][c] = -3`). For every prime `p ≥ 11` and `θ ≠ 0`: a digital
`(0,4)`-sequence, the geometric digits follow the design exactly at every full level `P_{16K}`, and
`sep(P_{16K}) ≥ 1 - 4/p` for every `K ≥ 1`. -/
theorem blk4d_block (hp : 11 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk4d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (4 * (4 * K)) →
        seqDigit (zcode p) (blk4d θ) x i (4 * K) =
          ∑ c, ∑ n ∈ range (4 - 1), blockF blk4dF n i c * seqDigit (zcode p) (blk4d θ) x c (4 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 4 (4 * K) (seqPoint (zcode p) (blk4d θ)) (((p : ℝ) - 4) / p) := by
  sorry

end G16

section G17
open Finset Polynomial

/-- The sign-class condition for `blk5dF` with `A = 7`, from the evaluation at `P = 1361`. -/
theorem blk5d_signclass : SignClass blk5dM 7 := by
  sorry

end G17

section G18
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- `LB(F) ≥ 1 - 8/p` for `blk5dF` at every prime `p ≥ 67` (sign-class argument). -/
theorem blk5d_LB_proof (hp : 67 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- The bound at one prime from one evaluation of the checker. -/
theorem blk5d_LB_chk (hchk : caCheck 5 blk5dOpts blk5St0 p 7 = true) (hp : 8 ≤ p) (K : ℕ) :
    ∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- The axis step along the place `0` (carry length `1`) has the term `1 - 8/p` (every prime `p ≥ 9`). -/
theorem blk5d_LB_attained (hp : 9 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 8) / p := by
  sorry

/-- `LB(F) ≥ 1 - 8/p` at every prime `p ≥ 23`, given the kernel evaluations `Blk5dCA` (`23 ≤ p ≤ 61`). -/
theorem blk5d_LB_of (hca : Blk5dCA) (hp : 23 ≤ p) (K : ℕ) : ∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
    Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) := by
  sorry

/-- **`thm:block`(c), `s = 5`, smaller diagonal: `LB(F) = 1 - 8/p`** at every prime `p ≥ 23`, given `Blk5dCA`. -/
theorem blk5d_LB_eq_of (hca : Blk5dCA) (hp : 23 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    (∀ e l, IsStep K e l → ((p : ℝ) - 8) / p ≤
      Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2)) ∧
    ∃ e l, IsStep K e l ∧ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
        ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2) = ((p : ℝ) - 8) / p := by
  sorry

/-- Identity (a) of `def:block` for `blk5dF` (the off-diagonal entries are those of `U*_5`). -/
theorem blk5d_hrel (hp : 5 ≤ p) (c i : Fin 5) (h : i ≠ c) :
    wCoCo (blk5a (p := p)) c i = -C (blk5v i) *
      ∑ n ∈ range (5 - 1), C (blockF blk5dF n i c) * blk5N c (5 - 1 - n) := by
  sorry

/-- The sequence part of `thm:block` for `blk5dF` from any bound `LB` on the steps. -/
theorem blk5d_block_gen (hp : 5 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) (LB : ℝ) (hLB1 : LB ≤ 1)
    (hLB : ∀ K e l, IsStep K e l → LB ≤ Real.sqrt (∑ i, ((gapNum1 p (e i) (∑ c', (e c' : ZMod p) *
      ∑ n ∈ range (min (l c') (5 - 1)), blockF blk5dF n i c') : ℝ) / p) ^ 2)) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) LB := by
  sorry

/-- **`thm:block`(c), `s = 5`, with the smaller free diagonal**, given `Blk5dCA`: places `(0, 1, 1/2, 1/3, 1/4)`,
`v = (1, 1, 2, 3, 4)`, the design `blk5dF` (`U*_5` off the diagonal, `F_0[c][c] = -7`). For every prime `p ≥ 23` and
`θ ≠ 0`: a digital `(0,5)`-sequence, the design relation at every `P_{25K}`, and `sep(P_{25K}) ≥ 1 - 8/p`. -/
theorem blk5d_block_of (hca : Blk5dCA) (hp : 23 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) (((p : ℝ) - 8) / p) := by
  sorry

/-- **`thm:block`(c), `s = 5`, smaller diagonal, written range**: for every prime `p ≥ 67` and `θ ≠ 0`, the sequence
part with `sep(P_{25K}) ≥ 1 - 8/p` (no kernel evaluation below `p = 67` needed). -/
theorem blk5d_block_proof (hp : 67 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0) :
    IsSeq0 (zcode p) (blk5d θ) ∧
      (∀ K, 1 ≤ K → ∀ i x, x < p ^ (5 * (5 * K)) →
        seqDigit (zcode p) (blk5d θ) x i (5 * K) =
          ∑ c, ∑ n ∈ range (5 - 1), blockF blk5dF n i c * seqDigit (zcode p) (blk5d θ) x c (5 * K - 1 - n)) ∧
      ∀ K, 1 ≤ K → SepAtLevel p 5 (5 * K) (seqPoint (zcode p) (blk5d θ)) (((p : ℝ) - 8) / p) := by
  sorry

end G18

end GeoSeq
