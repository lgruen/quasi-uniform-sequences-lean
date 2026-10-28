/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs

@[expose] public section

/-!
# Statements: stage V5 (`sec:antipode`, staggering by half a cell)

The staggered design (`sec:antipode`, `app:LFdata`): `thm:BS` (continuum windows, `ε_s`), `lem:W`, `lem:D`, `lem:R` (exact rational identities, the definition of `L`, the identities in `𝔽_p`), `def:BS` / `prop:P0` (a), (b) and its consequence, `thm:A3` with its design data and threshold, and `thm:HB` in the V3 wording.
PROVED (`GeoSeq/V5BS.lean`, `V5W.lean`, `V5Cover.lean`, `V5R.lean`, `V5Mono.lean`, `V5P0.lean`, `V5A3.lean`,
`V5HB.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v5_statements.py` (definitions in
`GeoSeq/V5Defs.lean`).
Paper: V3 (development version V3 of the paper, `06-antipode.tex`, `E-designs.tex`); label → Lean map in
the formalization notes of the research repository, review the statement-review notes of the research repository.
-/

namespace GeoSeq
open Finset PowerSeries
open scoped Polynomial

section G0
variable {s : ℕ}

/-- **`thm:BS`** (the staggered windows): let `s ≥ 2` and `a, ε > 0` with `(s-1)ε < a ≤ 1-ε` and
`(1-a-ε)² + (½-ε)² ≥ 1` (`a ≤ 1-ε` is the hypothesis `h3 : a + ε ≤ 1`). Then the staggered continuum windows
have `c*(W) ≥ 1`. -/
theorem BS (hs : 2 ≤ s) (cs : Fin s) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (h1 : ((s : ℝ) - 1) * ε < a)
    (h2 : 1 ≤ (1 - a - ε) ^ 2 + (1 / 2 - ε) ^ 2) (h3 : a + ε ≤ 1) : CtsLB (stagCts cs a ε) 1 := by
  sorry

/-- **`thm:BS`, existence**: for every `0 < ε < ε_s` there is `a > (s-1)ε` (with `a ≤ 1-ε`) satisfying the
hypotheses of `BS`; explicitly `a = (s-1)ε + G/2`, `G = (1-sε)² + (½-ε)² - 1 > 0`. -/
theorem BS_exists (s : ℕ) (hs : 2 ≤ s) (ε : ℝ) (hε : 0 < ε) (hεs : ε < epsS s) :
    ∃ a : ℝ, 0 < a ∧ ((s : ℝ) - 1) * ε < a ∧ a + ε ≤ 1 ∧ 1 ≤ (1 - a - ε) ^ 2 + (1 / 2 - ε) ^ 2 := by
  sorry

/-- `ε_s` is a root of `(1 - sε)² + (½ - ε)² = 1` (`thm:BS`). -/
theorem epsS_root (s : ℕ) : (1 - s * epsS s) ^ 2 + (1 / 2 - epsS s) ^ 2 = 1 := by
  sorry

/-- `ε_s` is the smaller root: every root `ε` of `(1-sε)² + (½-ε)² = 1` has `ε ≥ ε_s`. -/
theorem epsS_least (s : ℕ) (ε : ℝ) (h : (1 - s * ε) ^ 2 + (1 / 2 - ε) ^ 2 = 1) : epsS s ≤ ε := by
  sorry

/-- `ε_3 = (7 - √39)/20`, and `0.0377 < ε_3 < 0.0378` (`thm:BS`). -/
theorem epsS_three : epsS 3 = (7 - Real.sqrt 39) / 20 ∧ 377 / 10000 < epsS 3 ∧ epsS 3 < 378 / 10000 := by
  sorry

end G0

section G1
variable {s : ℕ}
variable {p : ℕ} [Fact p.Prime]

/-- **`lem:W`** (bound for staggered windows): let `s ≥ 2`, `p` an odd prime, integers `A ≥ 0`, `M_i ≥ 1`,
`M⋆ ≥ 1` and `M ≥ max_{i ∈ C} M_i`, with (D) `A ≥ (s-2)B_{C←C} + B_{C←⋆}` and (N)
`A + M + (s-2)B_{C←C} + B_{C←⋆} ≤ p`, `2B_{⋆←C} + 2M⋆ ≤ p - 3`. Then the staggered windows have
`LB(W) ≥ LB_W`, `LB_W² = min(T⋆, T_{C⋆}, T_2)` (`T_2` omitted for `s = 2`). -/
theorem lemW (hs : 2 ≤ s) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (M Bcc Bsc Bcs : ℕ)
    (hM1 : ∀ c, 1 ≤ Mv c) (hM : ∀ i, i ≠ cs → Mv i ≤ M)
    (hD : (s - 2) * Bcc + Bcs ≤ A) (hN1 : A + M + (s - 2) * Bcc + Bcs ≤ p)
    (hN2 : 2 * Bsc + 2 * Mv cs ≤ p - 3) :
    WinLB p (stagWin p cs A Mv Bcc Bsc Bcs) (lbW p s A M (Mv cs) Bcc Bsc Bcs) := by
  sorry

/-- **`lem:W`, last statement**: with `x = 1 - ((s-2)B_{C←C} + 2B_{C←⋆})/p`, `y = ½ - B_{⋆←C}/p` and
`A = (s-2)B_{C←C} + B_{C←⋆}`: if `x ≥ M/p`, `p(x² + y² - 1) ≥ 2xM + 2y(M⋆ + ½)` and `1 - (2A+M)/p ≥ 1/√2`, then
`LB_W = 1 - M⋆/p` (here only `M⋆ ≤ p` of the lemma's hypotheses is used). -/
theorem lemW_last (p s A M Mst Bcc Bsc Bcs : ℕ) (hp : 0 < p) (hMst : Mst ≤ p)
    (hA : A = (s - 2) * Bcc + Bcs)
    (hx : (M : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p)
    (hxy : 2 * (1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) * M + 2 * (1 / 2 - (Bsc : ℝ) / p) * (Mst + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) ^ 2 + (1 / 2 - (Bsc : ℝ) / p) ^ 2 - 1))
    (hz : 1 / Real.sqrt 2 ≤ 1 - (2 * (A : ℝ) + M) / p) :
    lbW p s A M Mst Bcc Bsc Bcs = 1 - (Mst : ℝ) / p := by
  sorry

/-- **`lem:W` with its last statement**: under (D), (N) and the three inequalities of the last statement,
the staggered windows have `LB(W) ≥ 1 - M⋆/p`. -/
theorem lemW_lb (hs : 2 ≤ s) (cs : Fin s) (A : ℕ) (Mv : Fin s → ℕ) (M Bcc Bsc Bcs : ℕ)
    (hM1 : ∀ c, 1 ≤ Mv c) (hM : ∀ i, i ≠ cs → Mv i ≤ M)
    (hA : A = (s - 2) * Bcc + Bcs) (hN1 : A + M + (s - 2) * Bcc + Bcs ≤ p)
    (hN2 : 2 * Bsc + 2 * Mv cs ≤ p - 3)
    (hx : (M : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p)
    (hxy : 2 * (1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) * M + 2 * (1 / 2 - (Bsc : ℝ) / p) * (Mv cs + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * Bcc + 2 * Bcs) / p) ^ 2 + (1 / 2 - (Bsc : ℝ) / p) ^ 2 - 1))
    (hz : 1 / Real.sqrt 2 ≤ 1 - (2 * (A : ℝ) + M) / p) :
    WinLB p (stagWin p cs A Mv Bcc Bsc Bcs) (1 - (Mv cs : ℝ) / p) := by
  sorry

end G1

section G2
variable {F : Type*} [Field F] {s : ℕ}

/-- **Condition (ii) for any windows** (the computation in the proof of `lem:lexcover`): every line
`β + 𝔽 α_j` meets `W^{(j)}` iff for every `σ` some `o ∈ Wo^{(j)}` has `σ_c + o κ_{c←j} ∈ W_{c←j}` (`c ≠ j`). -/
theorem cover_iff (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F) (W : Fin s → Fin s → Set F)
    (j : Fin s) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin W j) ↔
      ∀ σ : Fin s → F, ∃ o ∈ W j j, ∀ c, c ≠ j → σ c + o * kapL θ lamv zθ c j ∈ W c j := by
  sorry

end G2

section G3

/-- **`lem:D`** (doubling): let `u ∈ 𝔽_p^k`, let `v ∈ ℤ^k` represent `2u`, and suppose `v` satisfies the
hypotheses of `lem:ws` for arcs `I_1, …, I_k` (rows indexed from `0`), with number `N_k`. Then every run
`a, a+1, …, a + 2N_k - 2` of `2N_k - 1` consecutive integers contains an `o` with `σ + o u ∈ I_1 × ⋯ × I_k`,
for every `σ`. -/
theorem lemD (p : ℕ) [NeZero p] (k : ℕ) (hk : 1 ≤ k) (u : ℕ → ZMod p) (v : ℕ → ℤ)
    (hv2 : ∀ t < k, (v t : ZMod p) = 2 * u t) (L : ℕ → ℤ) (len : ℕ → ℕ)
    (hlen : ∀ t < k, len t ≤ p) (hv : ∀ t < k, 1 ≤ (v t).natAbs) (h1 : (v 0).natAbs ≤ len 0)
    (hN : ∀ t, t + 1 < k →
      wsN p len (fun t => (v t).natAbs) t * (v (t + 1)).natAbs ≤ len (t + 1))
    (σ : ℕ → ZMod p) (a : ℤ) :
    ∃ o : ℤ, a ≤ o ∧ o ≤ a + 2 * ((wsN p len (fun t => (v t).natAbs) (k - 1) : ℤ) - 1) ∧
      ∀ t < k, σ t + (o : ZMod p) * u t ∈ arc p (L t) (len t) := by
  sorry

end G3

section G4
variable {s : ℕ}

/-- **`lem:R`, the identities** (exact, over `ℚ`): with `g_{c⋆} = 1`, `g_j = 2^{1+δ}Q_j/Δ_{⋆j}` and
`θ = 2^δ L T`, every depth-zero cross `κ_{c←c'} = θ g_c/(g_{c'}Δ_{cc'})` equals `T n_{cc'}`; in particular, in
the row of `c⋆`, `θ/(g_j Δ_{⋆j}) = TL/(2Q_j)` (the frame factor cancels completely). -/
theorem lemR_rat (D : StagDesign s) (hD : sdOK D) (δ L T : ℕ) {c c' : Fin s} (h : c ≠ c') :
    sdKap D δ ((2 : ℚ) ^ δ * L * T) c c' = T * sdN D δ L c c' := by
  sorry

/-- **`lem:R`**: `n_{cc'} ∈ ℤ` for `c ≠ c⋆` (by the definition of `L`). -/
theorem lemR_int (D : StagDesign s) (δ L : ℕ) (hL : sdLOK D δ L) {c c' : Fin s} (hc : c ≠ D.cs)
    (h : c ≠ c') : (sdN D δ L c c').den = 1 := by
  sorry

/-- **`lem:R`**: `L/Q_j` is an odd integer, and `n_{⋆←j} = L/(2Q_j) = ½ + (L/Q_j - 1)/2 ∈ ½ + ℤ`. -/
theorem lemR_half (D : StagDesign s) (hD : sdOK D) (δ L : ℕ) (hL : sdLOK D δ L) {j : Fin s}
    (hj : j ≠ D.cs) :
    ((L : ℚ) / D.Q j).den = 1 ∧ ((L : ℚ) / D.Q j).num % 2 = 1 ∧
      sdN D δ L D.cs j = 1 / 2 + (((((L : ℚ) / D.Q j).num - 1) / 2 : ℤ) : ℚ) := by
  sorry

/-- **`lem:R`, existence of `L`**: for every `δ` with the conditions of `sdDeltaOK` there is a least `L` with the
conditions of `sdLOK` (odd, every `L/Q_j` and every `L n°_{cc'}`, `c ≠ c⋆`, an integer). -/
theorem lemR_L (D : StagDesign s) (hD : sdOK D) (δ : ℕ) (hδ : sdDeltaOK D δ) :
    ∃ L, IsLeast {L | sdLOK D δ L} L := by
  sorry

/-- **`lem:R`, existence of `δ`**: a least `δ ≥ 0` with the conditions of `sdDeltaOK` exists. -/
theorem lemR_delta (D : StagDesign s) : ∃ δ, IsLeast {δ | sdDeltaOK D δ} δ := by
  sorry

end G4

section G5
variable {s : ℕ}
variable {p : ℕ} [Fact p.Prime]

/-- **`lem:R` in `𝔽_p`**: let `p` be a prime dividing none of the `a_c - a_{c'}`, the numerators and denominators
of the `Q_j`, `L`, `T` and `2`, and `T` odd. With `θ = 2^δ L T` and the constants `λ_c = g_c w'(a_c)` (the
rationals `g_c` reduced mod `p`), for every choice of the local roots: `θ ≠ 0`, `λ_c ≠ 0`, every
`κ_{c←c'}` with `c ≠ c⋆` is the integer `T n_{cc'}`, and each half-cell offset is
`κ_{⋆←j} = ½ + (TL/Q_j - 1)/2` (with `2κ_{⋆←j} = TL/Q_j`). -/
theorem lemR_Fp (hp2 : p ≠ 2) (D : StagDesign s) (hD : sdOK D) (δ L T : ℕ) (hL : sdLOK D δ L)
    (hT : T % 2 = 1)
    (hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0)
    (hpQ : ∀ j, j ≠ D.cs → ((D.Q j).num : ZMod p) ≠ 0 ∧ ((D.Q j).den : ZMod p) ≠ 0)
    (hpL : (L : ZMod p) ≠ 0) (hpT : (T : ZMod p) ≠ 0)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) :
    sdTheta p δ L T ≠ 0 ∧ (∀ c, sdLam D p δ c ≠ 0) ∧
    (∀ c c', c ≠ D.cs → c ≠ c' →
      kapL (sdTheta p δ L T) (sdLam D p δ) zθ c c' = (((T : ℤ) * (sdN D δ L c c').num : ℤ) : ZMod p)) ∧
    ∀ j, j ≠ D.cs →
      2 * kapL (sdTheta p δ L T) (sdLam D p δ) zθ D.cs j = (((T : ℤ) * ((L : ℚ) / D.Q j).num : ℤ) : ZMod p) ∧
      kapL (sdTheta p δ L T) (sdLam D p δ) zθ D.cs j =
        ((halfZ p : ℤ) : ZMod p) + ((((T : ℤ) * ((L : ℚ) / D.Q j).num - 1) / 2 : ℤ) : ZMod p) := by
  sorry

end G5

section G6
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s : ℕ}

/-- `N_t^+` is non-increasing in `p`. -/
theorem stNP_anti (D : StagData s) {p p' : K} (hp : 0 < p) (hpp : p ≤ p') (hu : 2 < (D.u : K) * p)
    (c' : Fin s) : ∀ t, stNP D p' c' t ≤ stNP D p c' t := by
  sorry

/-- `M^+` is non-increasing in `p`. -/
theorem stMP_anti (D : StagData s) {p p' : K} (hp : 0 < p) (hpp : p ≤ p') (hu : 2 < (D.u : K) * p) :
    stMP D p' ≤ stMP D p := by
  sorry

/-- **`prop:P0`(b)** (monotone threshold): for `0 < p ≤ p'`, `𝒫(p)` implies `𝒫(p')`, and `M⋆^+(p') ≤ M⋆^+(p)`
(each `N_t^+` is a sum of terms non-increasing in `p`, and after division by `p` every inequality of `𝒫` has
the form "non-increasing ≤ non-decreasing"). -/
theorem P0_mono (D : StagData s) {p p' : K} (hp : 0 < p) (hpp : p ≤ p') (hP : StP D p) :
    StP D p' ∧ stMstP D p' ≤ stMstP D p := by
  sorry

end G6

section G7
variable {s : ℕ}

/-- **`𝒫` at a rational point** is the same over `ℚ` and over `ℝ`. -/
theorem StP_cast (D : StagData s) (q : ℚ) : StP D q ↔ StP D (q : ℝ) := by
  sorry

end G7

section G8
variable {s : ℕ} {p : ℕ} [Fact p.Prime]

/-- **`prop:P0`(a), condition (i)** of `prop:steer`: every depth-zero cross lies in its window (the crosses
`T n_{cc'}` within `[-B, B]` by (P3), the half-cell offsets `½ - (T n + 1)/2` within `½ + [-B_{⋆←C}, B_{⋆←C}]`). -/
theorem P0_cond_i (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ))
    (θ : ZMod p) (lamv : Fin s → ZMod p) (zθ : Fin s → PowerSeries (ZMod p))
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    ∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ stWin D p c c' := by
  sorry

/-- **`prop:P0`(a), condition (ii)** of `prop:steer`: column `c⋆` covers by `lem:ws`, every other column is a
doubled column (`lem:D`). -/
theorem P0_cond_ii (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ))
    (θ : ZMod p) (lamv : Fin s → ZMod p) (zθ : Fin s → PowerSeries (ZMod p))
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    ∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin (stWin D p) c') := by
  sorry

/-- **`prop:P0`(a), the window bound**: the staggered rule satisfies the hypotheses of `lem:W` (`M_i, M⋆ ≥ 1`,
`M = max M_i`, (D) with equality, (N)) and the three inequalities of its last statement, with
`M⋆ ≤ M⋆^+(p)`. -/
theorem P0_W (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ)) :
    (∀ c, 1 ≤ stMv D p c) ∧ (∀ i, i ≠ D.cs → stMv D p i ≤ stM D p) ∧
    stA D p = (s - 2) * stB D.eCC p + stB D.eCS p ∧
    stA D p + stM D p + (s - 2) * stB D.eCC p + stB D.eCS p ≤ p ∧
    2 * stB D.eSC p + 2 * stMv D p D.cs ≤ p - 3 ∧
    (stM D p : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p ∧
    2 * (1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) * stM D p +
        2 * (1 / 2 - (stB D.eSC p : ℝ) / p) * (stMv D p D.cs + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) ^ 2 +
        (1 / 2 - (stB D.eSC p : ℝ) / p) ^ 2 - 1) ∧
    1 / Real.sqrt 2 ≤ 1 - (2 * (stA D p : ℝ) + stM D p) / p ∧
    (stMv D p D.cs : ℝ) ≤ stMstP D (p : ℝ) := by
  sorry

/-- **`prop:P0`(a)**: at every prime `p` with `𝒫(p)`, if the crosses of the frame are `κ_{c←c'} = T n_{cc'}`
(`c ≠ c⋆`) and `2κ_{⋆←i} = T L/Q_i` (as `lem:R` gives), the staggered rule satisfies (i) and (ii) of
`prop:steer` and the hypotheses of `lem:W` including its last statement, with `M⋆ ≤ M⋆^+(p)`. -/
theorem P0_a (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (hP : StP D (p : ℝ))
    (θ : ZMod p) (lamv : Fin s → ZMod p) (zθ : Fin s → PowerSeries (ZMod p))
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    (∀ c c', c ≠ c' → -kapL θ lamv zθ c c' ∈ stWin D p c c') ∧
    (∀ c', LinesMeet (stAlpha θ lamv zθ c') (colWin (stWin D p) c')) ∧
    (∀ c, 1 ≤ stMv D p c) ∧ (∀ i, i ≠ D.cs → stMv D p i ≤ stM D p) ∧
    stA D p = (s - 2) * stB D.eCC p + stB D.eCS p ∧
    stA D p + stM D p + (s - 2) * stB D.eCC p + stB D.eCS p ≤ p ∧
    2 * stB D.eSC p + 2 * stMv D p D.cs ≤ p - 3 ∧
    (stM D p : ℝ) / p ≤ 1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p ∧
    2 * (1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) * stM D p +
        2 * (1 / 2 - (stB D.eSC p : ℝ) / p) * (stMv D p D.cs + 1 / 2) ≤
      p * ((1 - (((s - 2 : ℕ) : ℝ) * stB D.eCC p + 2 * stB D.eCS p) / p) ^ 2 +
        (1 / 2 - (stB D.eSC p : ℝ) / p) ^ 2 - 1) ∧
    1 / Real.sqrt 2 ≤ 1 - (2 * (stA D p : ℝ) + stM D p) / p ∧
    (stMv D p D.cs : ℝ) ≤ stMstP D (p : ℝ) := by
  sorry

end G8

section G9
variable {s : ℕ}

/-- **`prop:P0`, consequence** (with `P0_mono`): if `𝒫(p₀)` holds (`p₀ > 0` real), then for every prime
`p ≥ p₀` and every frame with the crosses `κ_{c←c'} = T n_{cc'}`, `2κ_{⋆←i} = T L/Q_i` (constants `λ_c ≠ 0`,
scale `θ ≠ 0`, local roots of a monic `w` of degree `s` with distinct places), selection rules for the
staggered rule exist, and every selection rule gives a quasi-uniform digital `(0,s)`-sequence over `𝔽_p` with
`c(P_{sK}) ≥ 1 - M⋆/p ≥ 1 - C''/p` for every `K ≥ 1`, `C'' = M⋆^+(p₀)` (and `M⋆ ≤ C''`, `M⋆` the integer own
size of column `c⋆`). -/
theorem P0_seq (D : StagData s) (hs : 2 ≤ s) (hv : D.Valid) (p0 : ℝ) (hp0 : 0 < p0) (hP0 : StP D p0)
    (p : ℕ) [Fact p.Prime] (hpp : p0 ≤ p) (w : (ZMod p)[X]) (hw : w.Monic) (hdeg : w.natDegree = s)
    (θ : ZMod p) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X) (hinj : Function.Injective (ssPlace zθ))
    (lamv : Fin s → ZMod p) (hlam : ∀ c, lamv c ≠ 0)
    (hκ : ∀ c c', c ≠ D.cs → c ≠ c' → kapL θ lamv zθ c c' = (((stT D.u p : ℤ) * D.nI c c' : ℤ) : ZMod p))
    (hκh : ∀ i, i ≠ D.cs → 2 * kapL θ lamv zθ D.cs i = (((stT D.u p : ℤ) * D.nI D.cs i : ℤ) : ZMod p)) :
    (stMv D p D.cs : ℝ) ≤ stMstP D p0 ∧
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (stWin D p) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (stWin D p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))
        (1 - (stMv D p D.cs : ℝ) / p)) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))
        (1 - stMstP D p0 / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))) ≤
          Real.sqrt s * p / (1 - stMstP D p0 / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ)))) := by
  sorry

/-- **The staggered rule of a staggered design** (`def:BS`, `lem:R`, `prop:P0`): let `D` be a staggered design over
an integer frame with `δ`, `L` as in `lem:R` (`sdLOK`), rows/fractions/`u` with valid data, and `𝒫(p₀)`. For
every prime `p ≥ p₀` as in `lem:R` (dividing none of the `a_c - a_{c'}`, the numerators and denominators of
the `Q_j`, `L` and `T`), with `θ = 2^δ L T`, the constants `λ_c = g_c w'(a_c)` of `lem:R` and the windows of the
rule, selection rules exist and every selection rule gives a quasi-uniform digital `(0,s)`-sequence with
`c(P_{sK}) ≥ 1 - M⋆/p ≥ 1 - M⋆^+(p₀)/p` for every `K ≥ 1`; the same holds for every multiplier family with
these constants and all responses in the windows ("every selection rule", `prop:steer`). -/
theorem P0_design (D : StagDesign s) (hs : 2 ≤ s) (hD : sdOK D) (δ L : ℕ) (hL : sdLOK D δ L)
    (rows : Fin s → ℕ → Fin s) (eCS eCC eSC u : ℚ)
    (hv : (sdData D δ L rows eCS eCC eSC u).Valid)
    (p0 : ℝ) (hp0 : 0 < p0) (hP0 : StP (sdData D δ L rows eCS eCC eSC u) p0)
    (p : ℕ) [Fact p.Prime] (hpp : p0 ≤ p)
    (hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0)
    (hpQ : ∀ j, j ≠ D.cs → ((D.Q j).num : ZMod p) ≠ 0 ∧ ((D.Q j).den : ZMod p) ≠ 0)
    (hpL : (L : ZMod p) ≠ 0) (hpT : (stT u p : ZMod p) ≠ 0)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s D.fr) = C (sdTheta p δ L (stT u p)) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) :
    (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) ≤ stMstP (sdData D δ L rows eCS eCC eSC u) p0 ∧
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows eCS eCC eSC u) p) rule) ∧
    (∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ (stWin (sdData D δ L rows eCS eCC eSC u) p) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
        (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))
        (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))) ≤
          Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
              (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p δ L (stT u p)) (sdLam D p δ) zθ rule) zθ))))) ∧
    ∀ g : Fin s → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam D p δ c) →
      RespInS (ssGen g zθ) (stWin (sdData D δ L rows eCS eCC eSC u) p) →
      IsSeq0 (zcode p) (ssGen g zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
        (1 - (stMv (sdData D δ L rows eCS eCC eSC u) p D.cs : ℝ) / p)) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
        (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
          Real.sqrt s * p / (1 - stMstP (sdData D δ L rows eCS eCC eSC u) p0 / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  sorry

end G9

section G10

/-- **`thm:A3`, the design** (`lem:R` data, `tab:BSdata`): `δ = 2` and `L = 21` are the least values with the
conditions of `lem:R`, `g = (1, -56, 6)`, `θ = 2^δ L T = 84T`, and the rationals
`n_{1←0} = 2352`, `n_{2←0} = -126`, `n_{0←1} = 3/2`, `n_{0←2} = 7/2`, `n_{1←2} = -392`, `n_{2←1} = -9`; the stored
row order of every column is the order of decreasing `|n|` (`def:BS` (S3), `app:LFdata`). -/
theorem A3_design :
    sdOK a3Design ∧ IsLeast {δ | sdDeltaOK a3Design δ} 2 ∧ IsLeast {L | sdLOK a3Design 2 L} 21 ∧
    (sdG a3Design 2 0 = 1 ∧ sdG a3Design 2 1 = -56 ∧ sdG a3Design 2 2 = 6) ∧ 2 ^ 2 * 21 = 84 ∧
    sdN a3Design 2 21 1 0 = 2352 ∧ sdN a3Design 2 21 2 0 = -126 ∧ sdN a3Design 2 21 0 1 = 3 / 2 ∧
    sdN a3Design 2 21 0 2 = 7 / 2 ∧ sdN a3Design 2 21 1 2 = -392 ∧ sdN a3Design 2 21 2 1 = -9 ∧
    (∀ c' : Fin 3, |sdN a3Design 2 21 (a3Rows c' 1) c'| ≤ |sdN a3Design 2 21 (a3Rows c' 0) c'|) := by
  sorry

/-- The data are valid (rows, nonzero crosses, odd half-cell numbers). -/
theorem a3Data_valid : a3Data.Valid := by
  sorry

/-- **`thm:A3`, the threshold** (`tab:BSdata`): `𝒫(p₀)` holds at `p₀ = 19 673 600`, with
`742 < M⋆^+(p₀) < 742.356` (exact rational evaluation by the kernel). -/
theorem A3_threshold : StP a3Data (19673600 : ℚ) ∧
    742 < stMstP a3Data (19673600 : ℚ) ∧ stMstP a3Data (19673600 : ℚ) < 742356 / 1000 := by
  sorry

end G10

section G11
variable {p : ℕ} [Fact p.Prime]

/-- **`thm:A3`, the crosses** (`lem:R` in `𝔽_p`): for every prime `p ≠ 2, 3, 7`, every odd `T` with `p ∤ T`, and
every choice of the local roots of the Faure frame `(0, 1, 2)`, with `θ = 84T` and `g = (1, -56, 6)`:
`κ_{1←0} = 2352T`, `κ_{2←0} = -126T`, `κ_{0←1} = 3T/2`, `κ_{0←2} = 7T/2`, `κ_{1←2} = -392T`, `κ_{2←1} = -9T`. -/
theorem A3_kappa (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7) (T : ℕ) (hT : T % 2 = 1) (hpT : (T : ZMod p) ≠ 0)
    (zθ : Fin 3 → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA a3Design.fr c : ℤ) : ZMod p)) :
    sdTheta p 2 21 T = ((84 * T : ℕ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 1 0 = ((2352 * T : ℤ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 2 0 = ((-126 * T : ℤ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 0 1 = ((3 * T : ℤ) : ZMod p) / 2 ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 0 2 = ((7 * T : ℤ) : ZMod p) / 2 ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 1 2 = ((-392 * T : ℤ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 2 1 = ((-9 * T : ℤ) : ZMod p) := by
  sorry

/-- **`thm:A3`** (the staggered rule in dimension three): for every prime `p ≥ 1.97·10⁷`, the local roots of the
Faure frame `(0, 1, 2)` with scale `θ = 84T` exist; for every choice of them, with `g = (1, -56, 6)`, the window
fractions `(27/1000, 1/200, 1/10)` and `u = 891/78 400 000` (`def:BS`), selection rules exist, and every
selection rule gives a digital `(0,3)`-sequence over `𝔽_p` with `c(P_{3K}) ≥ 1 - 742/p` for every `K ≥ 1`,
quasi-uniform (`h(P_{[N]}) ≤ (√3 p/(1 - 742/p)) δ(P_{[N]})` for every `N ≥ 2`, `lem:prefix`); the same for every
multiplier family with the constants `λ_c = g_c w'(a_c)` and all responses in the windows (= every selection
rule, `steer_every`). -/
theorem A3 (hp : 19700000 ≤ p) :
    (∃ zθ : Fin 3 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 3 a3Design.fr) = C (sdTheta p 2 21 (stT a3u p)) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA a3Design.fr c : ℤ) : ZMod p)) ∧
    ∀ zθ : Fin 3 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 3 a3Design.fr) = C (sdTheta p 2 21 (stT a3u p)) * X) →
      (∀ c, constantCoeff (zθ c) = ((frameA a3Design.fr c : ℤ) : ZMod p)) →
      (∃ rule : Fin 3 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ (stWin a3Data p) rule) ∧
      (∀ rule : Fin 3 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ (stWin a3Data p) rule →
        IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))
          (1 - 742 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N
            (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))) ≤
            Real.sqrt 3 * p / (1 - 742 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))))) ∧
      ∀ g : Fin 3 → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam a3Design p 2 c) →
        RespInS (ssGen g zθ) (stWin a3Data p) →
        IsSeq0 (zcode p) (ssGen g zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 742 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
            Real.sqrt 3 * p / (1 - 742 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  sorry

end G11

section G12

/-- **`thm:HB`** (hexagonal brick wall), V3 wording: if `b, e ≥ 1`, `2k + M_A < p` and `η > 0`
(`2b + 2M_B + 1 < p`), then a normalised multiplier family with all responses in the windows exists ("a selection
rule"), and every such family ("every selection rule") gives a digital `(0,2)`-sequence over `𝔽_p` with
`c(P_{2K}) ≥ min(1, LB^HB)` for every `K ≥ 1`. -/
theorem HB_V3 (p : ℕ) [Fact p.Prime] (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hka : 2 * hbK b e + hbMA p b < p) (hη : 2 * b + 2 * hbMB p b e + 1 < p) :
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e)) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (hbTheta p b e))) ∧
        ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p b e))))
          (min 1 (Real.sqrt (hbLB2 p b e)))) := by
  sorry

end G12

end GeoSeq
