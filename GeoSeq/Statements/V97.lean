/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V97Defs

@[expose] public section

/-!
# Statements: stage V97 (paper V4)

Windows and corrected skeleton relations (`sec:joint`) and digital shifts of residue sequences: `lem:corrS` (rational local multipliers), `thm:corrected`, `prop:joint`(i)–(iii) ((ii) one factor), `lem:shift`(b).
PROVED (`GeoSeq/V97Corr.lean`, `GeoSeq/V97Joint.lean`, `GeoSeq/V97Sep.lean`, `GeoSeq/V97Shift.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V97`
(definitions in `GeoSeq/V97Defs.lean`). Paper: V4 (`paper/sections/08-antipode.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV97.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- A self-similar scramble in residue form (`N_c(a_c) ≠ 0`, `U_c(a_c) ≠ 0`, `θ ≠ 0`, distinct places) is a digital
`(0,s)`-sequence. -/
theorem ssResGen_t0 [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q] (D : DigitCode F q) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X]) (hN : ∀ c, (N c).eval (a c) ≠ 0)
    (hU : ∀ c, (U c).eval (a c) ≠ 0) : IsSeq0 D (ssResGen a θ N U) := by
  sorry

/-- **`lem:corrS`**: for a self-similar scramble in residue form with correction coefficients up to order `K`
(`CorrTrunc`, `χ_{c,0} = 1`, so `v_c = 1/φ_c(a_c)`), every `V` with `deg V < m`, `m + 1 ≤ sK`, satisfies
`∑_c v_c [y_{c,K-1}(V) + ∑_{d=1}^{K-1} χ_{c,d} y_{c,K-1-d}(V)] = 0`. -/
theorem ssRes_corr (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (hU : ∀ c, (U c).eval (a c) ≠ 0) (v : Fin s → F) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ)
    (hK : 1 ≤ K) (htr : CorrTrunc a θ N U v χ K) (f : ℕ → F) (m : ℕ) (hm : m + 1 ≤ s * K) :
    ∑ c, v c * (∑ j ∈ range m, ssResGen a θ N U c (K - 1) j * f j +
      ∑ d ∈ Finset.Ico 1 K, χ c d * ∑ j ∈ range m, ssResGen a θ N U c (K - 1 - d) j * f j) = 0 := by
  sorry

/-- **`lem:corrS`** for the points: the corrected skeleton relation holds on `P_{sK-1}`. -/
theorem ssRes_corr_seq {q : ℕ} [NeZero q] (D : DigitCode F q) (hs : 2 ≤ s) (a : Fin s → F)
    (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X]) (hU : ∀ c, (U c).eval (a c) ≠ 0)
    (v : Fin s → F) (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K)
    (htr : CorrTrunc a θ N U v χ K) : CorrRel D (ssResGen a θ N U) v χ K := by
  sorry

/-- **The elementary change of a local multiplier** (`prop:joint`(ii)): replacing `φ_c` by `φ_c (1 + ε w^j)` changes
digit `n` of coordinate `c` by `ε θ^j y_{c,n-j}` for `n ≥ j` and not at all for `n < j`. -/
theorem ssRes_modify (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (c : Fin s) (ε : F) (j : ℕ) (f : ℕ → F) (m n : ℕ) :
    ∑ k ∈ range m, ssResGen a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U c n k * f k =
      ∑ k ∈ range m, ssResGen a θ N U c n k * f k +
        if j ≤ n then ε * θ ^ j * ∑ k ∈ range m, ssResGen a θ N U c (n - j) k * f k else 0 := by
  sorry

/-- **The change of the correction coefficients** (`prop:joint`(ii)): if `χ` are the correction coefficients of
`(N, U)` up to order `j + 1` (`χ_{c,0} = 1`, `j ≥ 1`), then for `φ_c (1 + ε w^j)` the coefficients up to order `j + 1` are
those of `φ_c` with `χ_{c,j}` replaced by `χ_{c,j} - ε θ^j`. -/
theorem corrTrunc_modify (a : Fin s → F) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X]) (v : Fin s → F)
    (χ : Fin s → ℕ → F) (hχ0 : ∀ c, χ c 0 = 1) (j : ℕ) (hj : 1 ≤ j) (htr : CorrTrunc a θ N U v χ (j + 1))
    (c : Fin s) (ε : F) :
    CorrTrunc a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U v
      (Function.update χ c (Function.update (χ c) j (χ c j - ε * θ ^ j))) (j + 1) := by
  sorry

end G0

section G1
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- `ℓ_jit^{(B)}(Λ_v) ≥ ℓ_jit(Λ_v) - B √s` (`thm:corrected`): `(|b| - 𝟏)_+ ≤ (|b| - (1+B)𝟏)_+ + B 𝟏` coordinatewise,
and the triangle inequality. -/
theorem ljitB_ge (hs : 1 ≤ s) (B : ℕ) (v : Fin s → ZMod p) : ljit v - B * Real.sqrt s ≤ ljitB B v := by
  sorry

/-- **`thm:corrected`** (lattice form): let `C` be a digital `(0,s)`-sequence over `ℤ/pℤ` whose prefix `P_{sK-1}` satisfies
the corrected skeleton relation (`CorrRel`) and whose partial sums `Ψ_c(j)`, `1 ≤ j ≤ K-1`, are represented by integers
in `[0, B]`. Then any two distinct points of `P_{sK-1}` are at toroidal distance `≥ ℓ_jit^{(B)}(Λ_v) · p^{-K}`. -/
theorem corrected (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (v : Fin s → ZMod p)
    (χ : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) (B : ℕ) (hrel : CorrRel (zcode p) C v χ K)
    (hΨ : ∀ c j, 1 ≤ j → j ≤ K - 1 → ∃ r : ℤ, 0 ≤ r ∧ r ≤ B ∧ (r : ZMod p) = psiSum χ c j) (x y : ℕ)
    (hx : x < p ^ (s * K - 1)) (hy : y < p ^ (s * K - 1)) (hxy : x ≠ y) :
    ljitB B v ≤ (p : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint (zcode p) C x) (seqPoint (zcode p) C y) := by
  sorry

/-- **`thm:corrected`**: `sep(P_{sK-1}) ≥ p^{-1/s} ℓ_jit^{(B)}(Λ_v)`. -/
theorem corrected_sepAtPrefix (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (v : Fin s → ZMod p) (χ : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K) (B : ℕ)
    (hrel : CorrRel (zcode p) C v χ K)
    (hΨ : ∀ c j, 1 ≤ j → j ≤ K - 1 → ∃ r : ℤ, 0 ≤ r ∧ r ≤ B ∧ (r : ZMod p) = psiSum χ c j) :
    SepAtPrefix p s (s * K - 1) (seqPoint (zcode p) C) ((p : ℝ) ^ (-(1 / (s : ℝ))) * ljitB B v) := by
  sorry

end G1

section G2
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- A skeleton relation for the unshifted digits gives the affine relation `∑_c v_c n̂_c ≡ ∑_c v_c ς_{c,K-1}` for the
shifted fine cells. -/
theorem shift_skel_rel (C : Gen s (ZMod p)) (ς : Fin s → ℕ → ZMod p) (v : Fin s → ZMod p) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) (x : ℕ)
    (hx : x < p ^ (s * K - 1)) :
    ∑ c, v c * ((shCell (zcode p) C ς x c K : ℕ) : ZMod p) = ∑ c, v c * ς c (K - 1) := by
  sorry

/-- **The skeleton bound for shifted sequences** (`lem:shift`(b), separation): if `C` is a digital `(0,s)`-sequence over
`ℤ/pℤ` with the skeleton relation on `P_{sK-1}`, then every digitally shifted copy has `sep(P_{sK-1}) ≥ p^{-1/s} L` for
every `L ≤ ‖(|b| - 𝟏)_+‖_2` on `Λ_v \ {0}`. -/
theorem shift_skel_sep (hs : 2 ≤ s) (C : Gen s (ZMod p)) (hseq : IsSeq0 (zcode p) C) (ς : Fin s → ℕ → ZMod p)
    (v : Fin s → ZMod p) (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) (K : ℕ) (hK : 1 ≤ K)
    (hskel : ∀ x, x < p ^ (s * K - 1) → ∑ c, v c * seqDigit (zcode p) C x c (K - 1) = 0) :
    SepAtPrefix p s (s * K - 1) (shPoint (zcode p) C ς) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  sorry

/-- **`lem:shift`(b)** for the residue sequence `R_v = resSeq a θ v`: for every digital shift `ς` and every `K ≥ 1`,
the fine cells occupied by the shifted prefix `P_{sK-1}` are exactly the `n̂ ∈ [0, p^K)^s` with
`∑_c v_c n̂_c ≡ ∑_c v_c ς_{c,K-1}`, each holding one point, and `sep(P_{sK-1}) ≥ p^{-1/s} L` for every lower bound `L`
of `‖(|b| - 𝟏)_+‖_2` on `Λ_v \ {0}`. -/
theorem shift_residue (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (θ : ZMod p)
    (hθ : θ ≠ 0) (v : Fin s → ZMod p) (hv : ∀ c, v c ≠ 0) (ς : Fin s → ℕ → ZMod p) (K : ℕ) (hK : 1 ≤ K)
    (L : ℝ) (hL : ∀ b : Fin s → ℤ, b ≠ 0 → InLat v b → L ≤ jitNorm b) :
    (fun x c => shCell (zcode p) (resSeq a θ v) ς x c K) '' Set.Iio (p ^ (s * K - 1)) =
      {n : Fin s → ℕ | (∀ c, n c < p ^ K) ∧ ∑ c, v c * ((n c : ℕ) : ZMod p) = ∑ c, v c * ς c (K - 1)} ∧
    Set.InjOn (fun x c => shCell (zcode p) (resSeq a θ v) ς x c K) (Set.Iio (p ^ (s * K - 1))) ∧
    SepAtPrefix p s (s * K - 1) (shPoint (zcode p) (resSeq a θ v) ς) ((p : ℝ) ^ (-(1 / (s : ℝ))) * L) := by
  sorry

end G2

section G3
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- **`prop:joint`(i), column form**: at the full level `K`, if `χ` are the correction coefficients up to order `K + 1`,
the carry responses of column `c'` with carry length `l ∈ [1, K]` satisfy `∑_c v_c D(l)[c][c'] = -v_{c'} Ψ_{c'}(l)`. -/
theorem joint_col (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U : Fin s → F[X]) (hU : ∀ c, (U c).eval (a c) ≠ 0) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K) (htr : CorrTrunc a θ N U v χ (K + 1))
    (l : ℕ) (hlK : l ≤ K) (c' : Fin s) (Dl : Fin s → F)
    (hD : ∀ c, IsCarryEntry (ssResGen a θ N U) K 0 l c c' (Dl c)) :
    ∑ c, v c * Dl c = -(v c' * psiSum χ c' l) := by
  sorry

/-- **`prop:joint`(i)**: for every full level `K`, every step `e` and carry lengths `l_c ∈ [1, K]`, the changes
`σ_c = ∑_{c'} e_{c'} D(l_{c'})[c][c']` of the geometric digits satisfy `∑_c v_c σ_c = -∑_c e_c v_c Ψ_c(l_c)`. -/
theorem joint_step (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0)
    (N U : Fin s → F[X]) (hU : ∀ c, (U c).eval (a c) ≠ 0) (v : Fin s → F) (χ : Fin s → ℕ → F)
    (hχ0 : ∀ c, χ c 0 = 1) (K : ℕ) (hK : 1 ≤ K) (htr : CorrTrunc a θ N U v χ (K + 1))
    (e : Fin s → ℤ) (lc : Fin s → ℕ) (hl : ∀ c, lc c ≤ K) (Dr : Fin s → Fin s → F)
    (hD : ∀ c c', IsCarryEntry (ssResGen a θ N U) K 0 (lc c') c c' (Dr c c')) :
    ∑ c, v c * ∑ c', (e c' : F) * Dr c c' = -∑ c, (e c : F) * (v c * psiSum χ c (lc c)) := by
  sorry

/-- **`prop:joint`(ii)** (one factor): replace the local multiplier `φ_c = N_c/U_c` by `φ_c (1 + ε w^j)` with `j ≥ l`
(the other coordinates unchanged), and the correction coefficients `χ_{c,j}` by `χ_{c,j} - εθ^j` (`corrTrunc_modify`).
Then at every level `K ≥ l` the cross responses `X^{(l)}_{c'←c}` (carry length `l` in coordinate `c`) are unchanged and
`O^{(l)}_c + Ψ_c(l)` is unchanged. -/
theorem joint_transfer (a : Fin s → F) (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (N U : Fin s → F[X])
    (χ : Fin s → ℕ → F) (c : Fin s) (ε : F) (j K l : ℕ) (hl : 1 ≤ l) (hlj : l ≤ j) (hlK : l ≤ K)
    (Dold Dnew : Fin s → F)
    (hold : ∀ c₁, IsCarryEntry (ssResGen a θ N U) K 0 l c₁ c (Dold c₁))
    (hnew : ∀ c₁, IsCarryEntry (ssResGen a θ (Function.update N c (N c * (1 + C ε * wPoly a ^ j))) U) K 0 l
      c₁ c (Dnew c₁)) :
    (∀ c₁, c₁ ≠ c → Dnew c₁ = Dold c₁) ∧
    Dnew c + psiSum (Function.update χ c (Function.update (χ c) j (χ c j - ε * θ ^ j))) c l =
      Dold c + psiSum χ c l := by
  sorry

end G3

section G4
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`prop:joint`(iii), window part**: if every column satisfies the joint covering condition `Wo^{(c)} + [0, B] = 𝔽_p`
(every `ξ ∈ 𝔽_p` is `ω + t` with `ω ∈ Wo^{(c)}`, `0 ≤ t ≤ B`) and the cross windows are nonempty, then every window
bound satisfies `LB(W) ≤ √s B / p`. -/
theorem joint_window (hs : 1 ≤ s) (W : Fin s → Fin s → Set (ZMod p)) (B : ℕ)
    (hcov : ∀ c (ξ : ZMod p), ∃ ω ∈ W c c, ∃ t : ℕ, t ≤ B ∧ ω + (t : ZMod p) = ξ)
    (hne : ∀ c c', c ≠ c' → (W c c').Nonempty) (LB : ℝ) (hLB : WinLB p W LB) :
    LB ≤ Real.sqrt s * B / p := by
  sorry

/-- **`prop:joint`(iii), Minkowski part**: if `ℓ_jit^{(B)}(Λ_v) > 0`, then `B + 1 < ⌊p^{1/s}⌋`. -/
theorem joint_minkowski (hs : 1 ≤ s) (B : ℕ) (v : Fin s → ZMod p) (hpos : 0 < ljitB B v) :
    B + 1 < korRho p s := by
  sorry

/-- **`prop:joint`(iii)**: under the joint covering condition with correction window `[0, B]`, `LB(W) ≤ √s B / p`; if
moreover `ℓ_jit^{(B)}(Λ_v) > 0` (so that `thm:corrected` with this `B` certifies a positive bound), then
`B < p^{1/s} - 1` and `LB(W) < √s (p^{1/s} - 1) / p`. -/
theorem joint_iii (hs : 1 ≤ s) (W : Fin s → Fin s → Set (ZMod p)) (B : ℕ)
    (hcov : ∀ c (ξ : ZMod p), ∃ ω ∈ W c c, ∃ t : ℕ, t ≤ B ∧ ω + (t : ZMod p) = ξ)
    (hne : ∀ c c', c ≠ c' → (W c c').Nonempty) (LB : ℝ) (hLB : WinLB p W LB) :
    LB ≤ Real.sqrt s * B / p ∧
      ∀ v : Fin s → ZMod p, 0 < ljitB B v →
        (B : ℝ) < (p : ℝ) ^ ((1 : ℝ) / s) - 1 ∧ LB < Real.sqrt s * ((p : ℝ) ^ ((1 : ℝ) / s) - 1) / p := by
  sorry

end G4

end GeoSeq
