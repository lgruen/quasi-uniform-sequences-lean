/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2Defs

@[expose] public section

/-!
# Statements: stage V2 (ordering the coordinates: `def:lex`, `lem:lex`, `rem:lexexact`, `lem:lexcover`,
  `lem:ws`, `lem:cauchy`, `def:MR`, `thm:MR`, `ex:MR101`)

PROVED (`GeoSeq/V2Lex.lean`, `GeoSeq/V2WS.lean`, `GeoSeq/V2Cauchy.lean`, `GeoSeq/V2.lean`, `GeoSeq/V2Ex.lean`);
generated verbatim from the proof files' signatures (definitions in `GeoSeq/V2Defs.lean`). Paper: V3
(development version V3 of the paper, `05-order.tex`); label → Lean map in the formalization notes of the research repository,
review the statement-review notes of the research repository.

* `lem:lex`: `lex_bound`, `lex_cost`; `rem:lexexact`: `lex_exact_row`, `lex_exact`, `lex_eq`, `lex_eq_cost`.
* `lem:lexcover`: `lexcover_iff` (second form), `lexcover_lattice` (`𝓑_j + L_j = ℤ^{1+j}`), `lexcover_zero`.
* `lem:ws`: `ws_cover` (general `k`, the V3 wrap count), `ws_pos`.
* `lem:cauchy`: `cauchy_mul`, `cauchy_super`, `cauchy_prod`.
* Faure frame: `exists_localRoot`, `faureW_monic`, `faureW_natDegree`, `faure_roots_exist`, `faure_placeDer`.
* `def:MR` arithmetic: `mrMu_mul`, `mrG_dvd`, `mrG_pos`, `mrMuBar_mul`; crosses `MR_kap`; windows `MR_LB`,
  `MR_cond_i`, `MR_cond_ii`.
* **`MR`** = `thm:MR`; `MR_every` (every multiplier family); **`MR101`** = `ex:MR101` (non-vacuity, `LB > 0`).
-/

namespace GeoSeq
open Finset

section LexWin
variable {s : ℕ}

/-- **`lem:lex`** (first moving coordinate): for ordered windows (`def:lex`), every
`L ≤ min_c (p - A_c - M_c - B_c)` gives `L/p ≤ LB(W)`, i.e. `p LB(W) ≥ min_c (p - A_c - M_c - B_c)`. -/
theorem lex_bound (p : ℕ) [NeZero p] (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) (L : ℝ) (hL : ∀ c, L ≤ (p : ℝ) - A c - M c - lexB Bx c) :
    WinLB p (lexWin p A M Bx) (L / p) := by
  sorry

/-- **`lem:lex`** with the cost: `LB(W) ≥ (p - max_c (A_c + M_c + B_c))/p`. -/
theorem lex_cost (p : ℕ) [NeZero p] (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) :
    WinLB p (lexWin p A M Bx) (((p : ℝ) - lexCost A M Bx) / p) := by
  sorry

/-- **`rem:lexexact`** (the bound is exact), one row: for ordered windows, every `LB ≤ LB(W)` has
`LB ≤ (p - A_c - M_c - B_c)/p` for every row `c` (step `e = 1_c + ∑_{c'>c} 1_{c'}`). -/
theorem lex_exact_row (p : ℕ) [NeZero p] (hp : 2 ≤ p) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ)
    (hd : IsLexData p A M Bx) (LB : ℝ) (hLB : WinLB p (lexWin p A M Bx) LB) (c : Fin s) :
    LB ≤ ((p : ℝ) - A c - M c - lexB Bx c) / p := by
  sorry

/-- **`rem:lexexact`**: every `LB ≤ LB(W)` has `LB ≤ (p - max_c (A_c + M_c + B_c))/p`. -/
theorem lex_exact (p : ℕ) [NeZero p] (hp : 2 ≤ p) (hs : 0 < s) (A M : Fin s → ℕ)
    (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p A M Bx) (LB : ℝ)
    (hLB : WinLB p (lexWin p A M Bx) LB) : LB ≤ ((p : ℝ) - lexCost A M Bx) / p := by
  sorry

/-- **`lem:lex` + `rem:lexexact`** (the bound is exact): for ordered windows the window bound is
`LB(W) = (p - max_c (A_c + M_c + B_c))/p`, i.e. this number is the greatest `LB` with `LB ≤ LB(W)`. -/
theorem lex_eq (p : ℕ) [NeZero p] (hp : 2 ≤ p) (hs : 0 < s) (A M : Fin s → ℕ)
    (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p A M Bx) :
    IsGreatest {LB : ℝ | WinLB p (lexWin p A M Bx) LB} (((p : ℝ) - lexCost A M Bx) / p) := by
  sorry

/-- **`rem:lexexact`** for `A_c = B_c`: `LB(W) = (p - Γ)/p` with the cost `Γ = max_c (2B_c + M_c)`. -/
theorem lex_eq_cost (p : ℕ) [NeZero p] (hp : 2 ≤ p) (hs : 0 < s) (M : Fin s → ℕ)
    (Bx : Fin s → Fin s → ℕ) (hd : IsLexData p (lexB Bx) M Bx) :
    IsGreatest {LB : ℝ | WinLB p (lexWin p (lexB Bx) M Bx) LB}
      (((p : ℝ) - (univ.sup fun c => 2 * lexB Bx c + M c)) / p) := by
  sorry
end LexWin

section Cover
variable {s : ℕ}

/-- **`lem:lexcover`** (coverings for ordered windows, second form): if the lower crosses of column `j`
are full, condition (ii) of `prop:steer` for column `j` holds iff for every `σ` some `o ∈ Wo^{(j)}` has
`σ_c + o κ_{c←j} ∈ W_{c←j}` for all `c < j` (only the entries `σ_c`, `c < j`, are read). -/
theorem lexcover_iff {F : Type*} [Field F] (θ : F) (lamv : Fin s → F) (zθ : Fin s → PowerSeries F)
    (W : Fin s → Fin s → Set F) (j : Fin s) (hlow : ∀ c, j < c → W c j = Set.univ) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin W j) ↔
      ∀ σ : Fin s → F, ∃ o ∈ W j j, ∀ c, c < j → σ c + o * kapL θ lamv zθ c j ∈ W c j := by
  sorry

/-- **`lem:lexcover`**, column `0`: the own window of ordered windows is nonempty (`M_0 ≥ 1`), so
column `0` satisfies (ii) (all its crosses are lower, hence full). -/
theorem lexcover_zero (p : ℕ) [Fact p.Prime] (θ : ZMod p) (lamv : Fin s → ZMod p)
    (zθ : Fin s → PowerSeries (ZMod p)) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (j : Fin s)
    (hj : j.val = 0) (hM : 1 ≤ M j) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin (lexWin p A M Bx) j) := by
  sorry

/-- **`lem:lexcover`** (lattice form): for ordered windows, with integers `κ̂_c ≡ κ_{c←j}` (`c < j`), column
`j` satisfies (ii) iff `𝓑_j + L_j = ℤ^{1+j}`: every `z ∈ ℤ^{1+j}` (coordinates `j` and `c < j` of `z`) is
`b + t (1, κ̂) + p y` with `b ∈ 𝓑_j = Wo^{(j)} × ∏_{c<j} [-B_{c←j}, B_{c←j}]`, `t ∈ ℤ`, `y ∈ ℤ^{1+j}`
(`L_j = ℤ(1, κ̂_0, …, κ̂_{j-1}) + pℤ^{1+j}`). -/
theorem lexcover_lattice (p : ℕ) [Fact p.Prime] (θ : ZMod p) (lamv : Fin s → ZMod p)
    (zθ : Fin s → PowerSeries (ZMod p)) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (j : Fin s)
    (κh : Fin s → ℤ) (hκ : ∀ c, c < j → (κh c : ZMod p) = kapL θ lamv zθ c j) :
    LinesMeet (stAlpha θ lamv zθ j) (colWin (lexWin p A M Bx) j) ↔
      ∀ z : Fin s → ℤ, ∃ b : Fin s → ℤ,
        (-((A j : ℤ) + M j - 1) ≤ b j ∧ b j ≤ -(A j : ℤ)) ∧
        (∀ c, c < j → -(Bx c j : ℤ) ≤ b c ∧ b c ≤ Bx c j) ∧
        ∃ (t : ℤ) (y : Fin s → ℤ), z j = b j + t + p * y j ∧
          ∀ c, c < j → z c = b c + t * κh c + p * y c := by
  sorry
end Cover
end GeoSeq

namespace GeoSeq

/-- **`lem:ws` with positive steps** `ν_t ≥ 1` (rows indexed from `0`). -/
theorem ws_pos (p : ℕ) [NeZero p] (k : ℕ) (hk : 1 ≤ k) (ν : ℕ → ℕ) (L : ℕ → ℤ) (len : ℕ → ℕ)
    (hlen : ∀ t < k, len t ≤ p) (hν : ∀ t < k, 1 ≤ ν t) (h1 : ν 0 ≤ len 0)
    (hN : ∀ t, t + 1 < k → wsN p len ν t * ν (t + 1) ≤ len (t + 1)) (σ : ℕ → ZMod p) (a : ℤ) :
    ∃ o : ℤ, a ≤ o ∧ o < a + wsN p len ν (k - 1) ∧
      ∀ t < k, σ t + (o : ZMod p) * (ν t : ZMod p) ∈ arc p (L t) (len t) := by
  sorry

/-- **`lem:ws`** (mixed-radix covering), general `k ≥ 1`; rows indexed `0, …, k-1` (row `0` = the paper's
row `1`, the fast row). Let `v_t ∈ ℤ` with `ν_t = |v_t| ≥ 1` and arcs `I_t = arc p (L t) (len t)` of
`|I_t| = len t ≤ p` residues. If `ν_0 ≤ |I_0|` and `N_{t-1} ν_t ≤ |I_t|` for `t ≥ 1`, with
`N_0 = 1 + ⌈(p - |I_0|)/ν_0⌉`, `N_t = N_{t-1} - 1 + ⌈p/ν_t⌉` (`wsN`), then for every `σ ∈ (ℤ/p)^k` every
set of `N_{k-1}` consecutive integers `a, …, a + N_{k-1} - 1` contains an `o` with `σ + o v ∈ I_0 × ⋯ × I_{k-1}`. -/
theorem ws_cover (p : ℕ) [NeZero p] (k : ℕ) (hk : 1 ≤ k) (v : ℕ → ℤ) (L : ℕ → ℤ) (len : ℕ → ℕ)
    (hlen : ∀ t < k, len t ≤ p) (hv : ∀ t < k, 1 ≤ (v t).natAbs) (h1 : (v 0).natAbs ≤ len 0)
    (hN : ∀ t, t + 1 < k →
      wsN p len (fun t => (v t).natAbs) t * (v (t + 1)).natAbs ≤ len (t + 1))
    (σ : ℕ → ZMod p) (a : ℤ) :
    ∃ o : ℤ, a ≤ o ∧ o < a + wsN p len (fun t => (v t).natAbs) (k - 1) ∧
      ∀ t < k, σ t + (o : ZMod p) * (v t : ZMod p) ∈ arc p (L t) (len t) := by
  sorry
end GeoSeq

namespace GeoSeq
open Finset PowerSeries
open scoped Polynomial

section Cauchy
variable {F : Type*} [Field F] {s : ℕ}

/-- **`lem:cauchy`**, the identity: `κ_{c←c'} κ_{c'←j} = θ τ(c,c',j) κ_{c←j}` for `c < c' < j` (the `λ_c`
cancel; any frame of distinct places, any scale `θ`, constants `λ_c ≠ 0`). -/
theorem cauchy_mul (θ : F) (lamv : Fin s → F) (hlam : ∀ c, lamv c ≠ 0) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (c c' j : Fin s) (h1 : c < c') (h2 : c' < j) :
    kapL θ lamv zθ c c' * kapL θ lamv zθ c' j = θ * tauC zθ c c' j * kapL θ lamv zθ c j := by
  sorry

/-- **`lem:cauchy`**, the free superdiagonal: for any `d_1, …, d_{s-1} ≠ 0` there are constants
`λ_c ≠ 0` with `κ_{t-1←t} = d_t` (`t ≥ 1`; `d_0` is not used). -/
theorem cauchy_super (θ : F) (hθ : θ ≠ 0) (zθ : Fin s → PowerSeries F)
    (hinj : Function.Injective (ssPlace zθ)) (d : Fin s → F) (hd : ∀ t, d t ≠ 0) :
    ∃ lamv : Fin s → F, (∀ c, lamv c ≠ 0) ∧
      ∀ t : Fin s, 1 ≤ t.val → kapL θ lamv zθ (predF t) t = d t := by
  sorry

/-- **`lem:cauchy`**, the product formula: if `κ_{t-1←t} = d_t` for all `t ≥ 1`, then for `c < j`
`κ_{c←j} = d_{c+1} ⋯ d_j / ∏_{i=c+2}^{j} θ τ(c, i-1, i)`. -/
theorem cauchy_prod (θ : F) (hθ : θ ≠ 0) (lamv : Fin s → F) (hlam : ∀ c, lamv c ≠ 0)
    (zθ : Fin s → PowerSeries F) (hinj : Function.Injective (ssPlace zθ)) (d : Fin s → F)
    (hsup : ∀ t : Fin s, 1 ≤ t.val → kapL θ lamv zθ (predF t) t = d t) (c j : Fin s) (hcj : c < j) :
    kapL θ lamv zθ c j =
      (∏ i ∈ univ.filter (fun i : Fin s => c < i ∧ i ≤ j), d i) /
        ∏ i ∈ univ.filter (fun i : Fin s => c.val + 2 ≤ i.val ∧ i ≤ j), θ * tauC zθ c (predF i) i := by
  sorry
end Cauchy

section Roots

/-- **Local roots exist** (Hensel's lemma over `F[[x]]`): a simple root `a` of a monic polynomial `w`
(`w(a) = 0`, `w'(a) ≠ 0`) lifts, for every scale `θ`, to a power series `z = z(θx)` with
`w(z(θx)) = θx` and `z(0) = a`. -/
theorem exists_localRoot {F : Type*} [Field F] (w : F[X]) (hw : w.Monic) (a : F)
    (ha : w.eval a = 0) (hd : w.derivative.eval a ≠ 0) (θ : F) :
    ∃ z : PowerSeries F, Polynomial.aeval z w = C θ * X ∧ constantCoeff z = a := by
  sorry

/-- The Faure frame `∏_{c<s} (z - c)` is monic of degree `s`. -/
theorem faureW_monic (s p : ℕ) : (faureW s p).Monic := by
  sorry

theorem faureW_natDegree (s p : ℕ) [Fact p.Prime] : (faureW s p).natDegree = s := by
  sorry

/-- **The local roots of the Faure frame exist** (`s ≤ p`, any scale `θ`): power series
`z_c(θx)`, `c < s`, with `∏_b (z_c(θx) - b) = θx` and `z_c(0) = c`. -/
theorem faure_roots_exist (s p : ℕ) [Fact p.Prime] (hsp : s ≤ p) (θ : ZMod p) :
    ∃ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (faureW s p) = C θ * X) ∧
      ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p) := by
  sorry
end Roots
end GeoSeq

namespace GeoSeq
open Finset PowerSeries
open scoped Polynomial

section Arith

/-- `μ_{cj} c! (n-j)! (j-c) = n!` for `c < j ≤ n = s - 1`: `μ_{cj}` is an integer (`def:MR`). -/
theorem mrMu_mul (s c j : ℕ) (hcj : c < j) (hj : j ≤ s - 1) :
    mrMu s c j * (c.factorial * (s - 1 - j).factorial * (j - c)) = (s - 1).factorial := by
  sorry

theorem mrG_dvd (s c j : ℕ) (hcj : c < j) (hj : j < s) : mrG s ∣ mrMu s c j := by
  sorry

theorem mrG_pos (s : ℕ) (hs : 2 ≤ s) : 0 < mrG s := by
  sorry

/-- `μ̄_{cj} (n-j)! c! (j-c) = n!/gcd` (both sides times `gcd` are `n!`). -/
theorem mrMuBar_mul (s c j : ℕ) (hs : 2 ≤ s) (hcj : c < j) (hj : j < s) :
    mrMu s c j / mrG s * ((s - 1 - j).factorial * c.factorial * (j - c)) =
      (s - 1).factorial / mrG s := by
  sorry
end Arith

section Faure

/-- **`w'(c) = (-1)^{n-c} c! (n-c)!`** for the Faure frame (places `a_b = b`, `b < s`, `n = s - 1`). -/
theorem faure_placeDer (s p : ℕ) [Fact p.Prime] (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) (c : Fin s) :
    placeDer zθ c =
      (((-1) ^ (s - 1 - c) * (c : ℕ).factorial * (s - 1 - c).factorial : ℤ) : ZMod p) := by
  sorry
end Faure

section Kap
variable {p : ℕ} [Fact p.Prime]

/-- **The crosses of `MR(s,p,h)`** (proof of `thm:MR`, "Crosses"): for the Faure frame, the scale
`θ = n!/gcd` and the constants `λ_c = (n-c)!/(h_1 ⋯ h_c)` (`p ≥ s`, step factors `1 ≤ h_t < p`),
`κ_{c←j} = θ λ_c/(λ_j w'(c) (j - c)) = (-1)^{n-c} μ̄_{cj} h_{c+1} ⋯ h_j` for `c < j`, the integers of (MR2). -/
theorem MR_kap (s : ℕ) (hs : 2 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t ∧ h t < p) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) (c j : Fin s) (hcj : c < j) :
    kapL (mrTheta s p) (mrLam s p h) zθ c j = (mrKapZ s h c j : ZMod p) := by
  sorry
end Kap

section Design
variable {s p : ℕ} {h : ℕ → ℕ}

/-- **The window bound of `MR(s,p,h)`** (proof of `thm:MR`, "Bound"; `lem:lex`, `rem:lexexact`): if `Γ < p`,
the windows are ordered and `LB(W) = (p - Γ)/p` (the greatest `LB` with `LB ≤ LB(W)`). -/
theorem MR_LB (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p) :
    IsGreatest {LB : ℝ | WinLB p (mrWin s p h) LB} (((p : ℝ) - mrCost s p h) / p) := by
  sorry

/-- **Condition (i) of `prop:steer`** for `MR(s,p,h)` (`Γ < p`): `-κ_{c←c'} ∈ W_{c←c'}`. -/
theorem MR_cond_i (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p)) (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) :
    ∀ c c' : Fin s, c ≠ c' → -kapL (mrTheta s p) (mrLam s p h) zθ c c' ∈ mrWin s p h c c' := by
  sorry

/-- **Condition (ii) of `prop:steer`** for `MR(s,p,h)` (`Γ < p`): every column covers (column `0` by
`M_0 = 1`, column `j ≥ 1` by `lem:ws` with row `0` fast and rows `1, …, j-1` slow, and `lem:lexcover`). -/
theorem MR_cond_ii (s p : ℕ) [Fact p.Prime] (hs : 2 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p)) (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) :
    ∀ j : Fin s, LinesMeet (stAlpha (mrTheta s p) (mrLam s p h) zθ j) (colWin (mrWin s p h) j) := by
  sorry
end Design

section Main

/-- **`thm:MR`** (mixed-radix designs). Let `s ≥ 3`, `p ≥ s` prime, `h_1, …, h_n` positive integers
(`n = s - 1`), `MR(s,p,h)` the mixed-radix design of `def:MR` (Faure frame with local roots `z_c(θx)`,
`w(z_c(θx)) = θx`, `z_c(0) = c`; scale `θ = n!/gcd`; constants `λ_c = (n-c)!/(h_1 ⋯ h_c)`; the ordered
windows of (MR2), (MR3)) and `Γ` its cost. If `Γ < p`, then selection rules exist, and every selection rule
for `MR(s,p,h)` defines a digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every
`K ≥ 1`, and the sequence is quasi-uniform: `h(P_{[N]}) ≤ (√s p/((p - Γ)/p)) δ(P_{[N]})` for every `N ≥ 2`
(`lem:prefix`). -/
theorem MR (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (faureW s p) = C (mrTheta s p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (mrTheta s p) (mrLam s p h) zθ (mrWin s p h) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p,
      IsSelRule (mrTheta s p) (mrLam s p h) zθ (mrWin s p h) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
        (seqPoint (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ))
        (((p : ℝ) - mrCost s p h) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist
            (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - mrCost s p h) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p)
                (ssGen (ruleMult (mrTheta s p) (mrLam s p h) zθ rule) zθ)))) := by
  sorry

/-- **`thm:MR` for every multiplier family** (`prop:steer`, "every selection rule"): under the
hypotheses of `MR`, every self-similar scramble of the Faure frame with the constants `λ_c` of (MR1)
(`g_c(0) ≠ 0`, `λ_c = g_c(0) w'(c)`) whose one-digit responses all lie in the windows of `MR(s,p,h)`
gives a quasi-uniform digital `(0,s)`-sequence with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem MR_every (s p : ℕ) [Fact p.Prime] (hs : 3 ≤ s) (hsp : s ≤ p) (h : ℕ → ℕ)
    (hh : ∀ t, 1 ≤ t → t ≤ s - 1 → 1 ≤ h t) (hΓ : mrCost s p h < p)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (faureW s p) = C (mrTheta s p) * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod p))
    (g : Fin s → PowerSeries (ZMod p)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hlam : ∀ c, lam g zθ c = mrLam s p h c) (hW : RespInS (ssGen g zθ) (mrWin s p h)) :
    IsSeq0 (zcode p) (ssGen g zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen g zθ))
        (((p : ℝ) - mrCost s p h) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - mrCost s p h) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  sorry
end Main
end GeoSeq

namespace GeoSeq
open Finset PowerSeries
open scoped Polynomial

/-- **`ex:MR101`** (non-vacuity of `thm:MR`, `LB = 28/101 > 0`). For `s = 3`: `γ_1 = 5/2`, `γ_2 = 1/2`,
`Q_3^3 = 5/2`, `θ = 2`; the step factors `(9, 2)` are those of the mixed-radix rule
`h_t = max(1, round(γ_t u))`, `u = (101/Q_3^3)^{1/3}`, in the rational form
`(h_t - 1/2)^3 Q_3^3 ≤ γ_t^3 p < (h_t + 1/2)^3 Q_3^3`; the upper crosses are `κ_{0←1} = 18`, `κ_{0←2} = 18`,
`κ_{1←2} = -4`; column `1`: `B_{0←1} = 18`, `M_1 = 5`; column `2`: `B_{0←2} = 18`, `B_{1←2} = 10`, `M_2 = 30`;
`Γ = 73`. The local roots of the Faure frame exist, and for every choice of them a selection rule exists and
every selection rule gives a digital `(0,3)`-sequence over `𝔽_101` with `c(P_{3K}) ≥ 28/101` for all `K ≥ 1`. -/
theorem MR101 :
    mrGamma 3 1 = 5 / 2 ∧ mrGamma 3 2 = 1 / 2 ∧ mrQss 3 = 5 / 2 ∧ mrTheta 3 101 = 2 ∧
    ((17 / 2 : ℚ) ^ 3 * mrQss 3 ≤ mrGamma 3 1 ^ 3 * 101 ∧
      mrGamma 3 1 ^ 3 * 101 < (19 / 2 : ℚ) ^ 3 * mrQss 3) ∧
    ((3 / 2 : ℚ) ^ 3 * mrQss 3 ≤ mrGamma 3 2 ^ 3 * 101 ∧
      mrGamma 3 2 ^ 3 * 101 < (5 / 2 : ℚ) ^ 3 * mrQss 3) ∧
    mrKapZ 3 mrH101 0 1 = 18 ∧ mrKapZ 3 mrH101 0 2 = 18 ∧ mrKapZ 3 mrH101 1 2 = -4 ∧
    mrBx 3 101 mrH101 0 1 = 18 ∧ mrM 3 101 mrH101 1 = 5 ∧
    mrBx 3 101 mrH101 0 2 = 18 ∧ mrBx 3 101 mrH101 1 2 = 10 ∧ mrM 3 101 mrH101 2 = 30 ∧
    mrCost 3 101 mrH101 = 73 ∧
    (∃ zθ : Fin 3 → PowerSeries (ZMod 101),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 101) = C (mrTheta 3 101) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 101)) ∧
    ∀ zθ : Fin 3 → PowerSeries (ZMod 101),
      (∀ c, Polynomial.aeval (zθ c) (faureW 3 101) = C (mrTheta 3 101) * X) →
      (∀ c, constantCoeff (zθ c) = ((c : ℕ) : ZMod 101)) →
      (∃ rule : Fin 3 → ℕ → (ℕ → ZMod 101) → ZMod 101,
        IsSelRule (mrTheta 3 101) (mrLam 3 101 mrH101) zθ (mrWin 3 101 mrH101) rule) ∧
      ∀ rule : Fin 3 → ℕ → (ℕ → ZMod 101) → ZMod 101,
        IsSelRule (mrTheta 3 101) (mrLam 3 101 mrH101) zθ (mrWin 3 101 mrH101) rule →
        IsSeq0 (zcode 101) (ssGen (ruleMult (mrTheta 3 101) (mrLam 3 101 mrH101) zθ rule) zθ) ∧
        ∀ K : ℕ, 1 ≤ K → SepAtLevel 101 3 K
          (seqPoint (zcode 101) (ssGen (ruleMult (mrTheta 3 101) (mrLam 3 101 mrH101) zθ rule) zθ))
          (28 / 101) := by
  sorry
end GeoSeq
