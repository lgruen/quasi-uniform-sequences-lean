/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V1Defs
public import GeoSeq.V4Defs

@[expose] public section

/-!
# GeoSeq stage V7: definitions (graph rule `def:graphrule`, `thm:p7`; digital shifts `lem:shift`;
the assembly `thm:dim3`, `thm:dim45`)

* `QUSep D s C LB`: the digital sequence with generator matrices `C` over the digit code `D` is a
  `(0,s)`-sequence, `c(P_{sK}) ≥ LB` for every `K ≥ 1`, and the mesh ratio of every prefix is at most
  `√s q / LB` (the conclusion of `lem:prefix`, i.e. "quasi-uniform" in the explicit form used throughout).
* Graph rule (`app:p7`, `s = 3`, indices of coordinates modulo `3`): `graphCol wt ξ c'` is the column
  `t(ξ)` with own entry `w(ξ)` in row `c'` and the entries of `ξ = (ξ_1, ξ_2)` in rows `c'+1`, `c'+2`;
  `graphXi … c' h l` = the cross partial sums `(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})` at length `l`, which
  depend only on the history `h 0, …, h (l-1)` (`ψ_{c',0}, …, ψ_{c',l-1}`; computed by `colVec` at depth
  `l - 1`, `prop:LI`(c)); `graphRule wt …` = the digit `ψ_{c',l}` of `def:graphrule` (`O^{(l)}_{c'} =
  w(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})`, solved for the digit, `θ ≠ 0`); `graphSig`, `GraphLB`: the bound
  `LB(w)` of `def:graphrule` in pointwise form (`LB ≤` every term). `p7Tab`, `wP7`: the table of `tab:p7`;
  `p7G`, `p7van`, `p7colL`, `p7chk`, `p7code`: the reflected checker of the finite statement of `thm:p7`.
* Digital shifts (`lem:shift`): `shDigit D C ς v c n = y_{c,n}(v) + ς_{c,n}`, the real points `shPoint`, the
  cell indices `shCell` and the `(0,s)`-property `IsSeq0Sh` of the shifted sequence (same definitions as
  `seqPoint`, `cellIdx`, `BlockNet0`, `IsSeq0` with the shifted digits); `CertAt D C K LB`: the hypotheses of
  `lem:cert` (`cert`) hold at level `K` with the bound `LB`.
* `edP211`: the explicit ordered windows at `p = 211`, `s = 5` (`thm:dim45`(b); the covering of its columns
  `3`, `4` is the computer-assisted part, stated as a hypothesis).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Quasi-uniform sequences with a separation bound -/

/-- **A quasi-uniform `(0,s)`-sequence with `c(P_{sK}) ≥ LB`** (`thm:dim3`, `thm:dim45`; the conclusion of
`lem:prefix`): `IsSeq0`, `c(P_{sK}) ≥ LB` for every `K ≥ 1`, and `h(P_{[N]}) ≤ (√s q / LB) δ(P_{[N]})` for every
`N ≥ 2` (`h` Euclidean covering radius, `δ = 2 · sepRad` toroidal). -/
def QUSep {R : Type*} [CommRing R] {q : ℕ} [NeZero q] (D : DigitCode R q) (s : ℕ) (C : Gen s R)
    (LB : ℝ) : Prop :=
  IsSeq0 D C ∧ (∀ K : ℕ, 1 ≤ K → SepAtLevel q s K (seqPoint D C) LB) ∧
    ∀ N : ℕ, 2 ≤ N → Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q / LB * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C)))

/-! ## The graph rule (`def:graphrule`, `s = 3`) -/

section Graph

variable {F : Type*} [Field F]

/-- The column `t(ξ)` of `def:graphrule` placed in column `c'`: own entry `w(ξ_1, ξ_2)` in row `c'`, `ξ_1` in row
`c'+1`, `ξ_2` in row `c'+2` (indices modulo `3`). -/
def graphCol (wt : F → F → F) (ξ : F × F) (c' c : Fin 3) : F :=
  if c = c' then wt ξ.1 ξ.2 else if c = c' + 1 then ξ.1 else ξ.2

/-- The cross partial sums `(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})` of column `c'` at carry length `l ≥ 1`, for the
history `h` (paper digits `ψ_{c',0}, …, ψ_{c',l-1}`): entries `c'+1`, `c'+2` of the column vector at depth `l - 1`
(`colVec`, `prop:LI`(c)), which read only `h 0, …, h (l-1)`. -/
noncomputable def graphXi (θ : F) (lamv : Fin 3 → F) (zθ : Fin 3 → PowerSeries F) (c' : Fin 3)
    (h : ℕ → F) (l : ℕ) : F × F :=
  (colVec θ lamv zθ c' (rescale θ (histSer h l)) (l - 1) (c' + 1),
    colVec θ lamv zθ c' (rescale θ (histSer h l)) (l - 1) (c' + 2))

/-- **The graph rule of `w`** (`def:graphrule`): at depth `l ≥ 1`, column `c'`, history `h`, the digit `ψ_{c',l}` with
`O^{(l)}_{c'} = w(X^{(l)}_{c'+1←c'}, X^{(l)}_{c'+2←c'})`. The own entry of `β_l - θ^l ψ α_{c'}` is
`β_l[c'] - θ^l ψ` (`prop:depthdir`), so `ψ = (β_l[c'] - w(ξ))/θ^l`. -/
noncomputable def graphRule (wt : F → F → F) (θ : F) (lamv : Fin 3 → F) (zθ : Fin 3 → PowerSeries F) :
    Fin 3 → ℕ → (ℕ → F) → F :=
  fun c' l h => (stBeta θ lamv zθ c' h l c' -
    wt (graphXi θ lamv zθ c' h l).1 (graphXi θ lamv zθ c' h l).2) / θ ^ l

end Graph

/-- `σ_c = ∑_{c'} e_{c'} t(ξ^{(c')})[c]` of `def:graphrule` (the terms with `e_{c'} = 0` vanish). -/
def graphSig {p : ℕ} (wt : ZMod p → ZMod p → ZMod p) (e : Fin 3 → ℤ) (ξ : Fin 3 → ZMod p × ZMod p)
    (c : Fin 3) : ZMod p :=
  ∑ c', (e c' : ZMod p) * graphCol wt (ξ c') c' c

/-- **`LB ≤ LB(w)`** (`def:graphrule`), in pointwise form: for every step `e ∈ {-1,0,1}^3 \ {0}` and every choice of
one `ξ^{(c')} ∈ 𝔽_p^2` per column, `LB ≤ (∑_c f_1(e_c, σ_c)²)^{1/2}`, `f_1 = gapNum1/p` (`rem:onedigit`). (The paper
takes the steps up to sign; the term is invariant under `e ↦ -e`, so all steps is the same.) -/
def GraphLB (p : ℕ) [NeZero p] (wt : ZMod p → ZMod p → ZMod p) (LB : ℝ) : Prop :=
  ∀ e : Fin 3 → ℤ, (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) → ∀ ξ : Fin 3 → ZMod p × ZMod p,
    LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (graphSig wt e ξ c) : ℝ) / p) ^ 2)

/-- **The table of `tab:p7`**: row `ξ_1`, column `ξ_2`, entries `w(ξ_1, ξ_2) ∈ {0, …, 6}`. -/
def p7Tab : List (List ℕ) :=
  [[0, 2, 2, 6, 3, 0, 0],
   [5, 4, 6, 6, 5, 3, 0],
   [0, 4, 0, 1, 1, 3, 2],
   [0, 0, 4, 1, 6, 5, 0],
   [2, 2, 4, 3, 1, 5, 2],
   [2, 0, 6, 6, 1, 0, 5],
   [4, 2, 6, 4, 3, 3, 5]]

/-- The table `w : 𝔽_7^2 → 𝔽_7` of `tab:p7` (`thm:p7`). -/
def wP7 (a b : ZMod 7) : ZMod 7 := (((p7Tab.getD a.val []).getD b.val 0 : ℕ) : ZMod 7)

/-! ## The finite check of `thm:p7` (checker; soundness in `GeoSeq/V7P7Data.lean`) -/

/-- The 49 graph columns `(w(a, b), a, b)` of `tab:p7` (values as natural numbers `< 7`). -/
def p7G : List (ℕ × ℕ × ℕ) :=
  (List.range 7).flatMap fun a => (List.range 7).map fun b => ((p7Tab.getD a []).getD b 0, a, b)

/-- Coordinate `c` vanishes (`f_1(e_c, σ_c) = 0`, `rem:onedigit`), step entry coded `e ∈ {0, 1, 6}`. -/
def p7van (e σ : ℕ) : Bool := if e = 0 then (σ == 0 || σ == 1 || σ == 6) else σ == e

/-- The columns run over for a coordinate with step entry (code) `e`: one dummy column if `e = 0`. -/
def p7colL (e : ℕ) : List (ℕ × ℕ × ℕ) := if e = 0 then [(0, 0, 0)] else p7G

/-- **The checker of `thm:p7`** for the step with codes `(e₀, e₁, e₂)`: for every choice of graph columns (column
`c'` contributes its own entry to row `c'`, `ξ_1` to row `c'+1`, `ξ_2` to row `c'+2`), some row does not vanish. -/
def p7chk (e0 e1 e2 : ℕ) : Bool :=
  (p7colL e0).all fun t0 => (p7colL e1).all fun t1 =>
    (p7colL e2).all fun t2 =>
      !(p7van e0 ((e0 * t0.1 + e1 * t1.2.2 + e2 * t2.2.1) % 7) &&
        p7van e1 ((e0 * t0.2.1 + e1 * t1.1 + e2 * t2.2.2) % 7) &&
        p7van e2 ((e0 * t0.2.2 + e1 * t1.2.1 + e2 * t2.1) % 7))

/-- The code of a step entry: `0 ↦ 0`, `1 ↦ 1`, `-1 ↦ 6`. -/
def p7code (e : ℤ) : ℕ := if e = 0 then 0 else if e = 1 then 1 else 6

/-! ## The single prime `p = 211` of `thm:dim45`(b) -/

instance fact_prime_211 : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- **The explicit ordered windows at `p = 211`, `s = 5`** (`thm:LF`(b), `thm:dim45`(b); archive
`lex_witnesses/smallp/s5_p211.cfg`): places `(0, 1, 112, 22, 6)`, `θ = 93`, `λ = (1, 74, 111, 122, 109)`, upper crosses
`κ_{0←·} = (-16, 20, -30, 24)`, `κ_{1←·} = (32, -24, -11)`, `κ_{2←·} = (-16, -43)`, `κ_{3←4} = -60`; upper windows
`B_{0←·} = (16, 24, 32, 32)`, `B_{1←·} = (32, 34, 32)`, `B_{2←·} = (36, 48)`, `B_{3←4} = 60`; own windows
`[-104,-104]`, `[-110,-98]`, `[-115,-84]`, `[-137,-60]`, `[-191,0]` (`A = (104,98,84,60,0)`, `M = (1,13,32,78,192)`),
`Γ = 209`, `LB = 2/211`. -/
def edP211 : EDesign 5 :=
  ⟨[0, 1, 112, 22, 6], 93, [1, 74, 111, 122, 109],
    [[0, -16, 20, -30, 24], [0, 0, 32, -24, -11], [0, 0, 0, -16, -43], [0, 0, 0, 0, -60], [0, 0, 0, 0, 0]],
    [104, 98, 84, 60, 0], [1, 13, 32, 78, 192],
    [[0, 16, 24, 32, 32], [0, 0, 32, 34, 32], [0, 0, 0, 36, 48], [0, 0, 0, 0, 60], [0, 0, 0, 0, 0]]⟩

/-! ## Digital shifts (`lem:shift`) -/

section Shift

variable {R : Type*} [CommRing R] {q s : ℕ}

/-- The digits of the shifted sequence (`lem:shift`): `y_{c,n}(v) + ς_{c,n}`. -/
def shDigit [NeZero q] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) (v : ℕ) (c : Fin s)
    (n : ℕ) : R :=
  seqDigit D C v c n + ς c n

/-- The points of the shifted sequence: `∑_n enc(y_{c,n}(v) + ς_{c,n}) q^{-n-1}`. -/
noncomputable def shPoint [NeZero q] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) (v : ℕ) :
    Fin s → ℝ :=
  fun c => ∑' n : ℕ, ((D.enc (shDigit D C ς v c n) : ℕ) : ℝ) / (q : ℝ) ^ (n + 1)

/-- The cell index of the shifted point with `d` digits in coordinate `c`. -/
def shCell [NeZero q] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) (v : ℕ) (c : Fin s)
    (d : ℕ) : ℕ :=
  ∑ n : Fin d, (D.enc (shDigit D C ς v c n) : ℕ) * q ^ (d - 1 - (n : ℕ))

/-- The `(0,s)`-sequence property of the shifted sequence: every block of `q^m` consecutive points starting at a
multiple of `q^m` is a `(0,m,s)`-net (as `BlockNet0`, `IsSeq0`). -/
def IsSeq0Sh [NeZero q] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) : Prop :=
  ∀ m k : ℕ, ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ a : Fin s → ℕ, (∀ c, a c < q ^ d c) →
    ∃! v : ℕ, (k * q ^ m ≤ v ∧ v < (k + 1) * q ^ m) ∧ ∀ c, shCell D C ς v c (d c) = a c

/-- **`lem:cert` gives `c(P_{sK}) ≥ min(1, LB)` at level `K`** (`lem:shift`): the hypotheses of `cert` hold at level
`K` for some number `j` of geometric digits and carry responses `Dr i l = D_i(l)` (`D_i(0) = 0`), i.e. `LB` is at most
every certificate term over all steps, carry lengths and stop digits. -/
def CertAt [NeZero q] [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (K : ℕ) (LB : ℝ) : Prop :=
  ∃ (j : ℕ) (Dr : ℕ → ℕ → Fin s → Fin s → R), (∀ i c c', Dr i 0 c c' = 0) ∧
    (∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c')) ∧
    ∀ e l, IsStep K e l → ∀ y : Fin s → R, LB ≤ certTerm D j e (certSigma D Dr j e l y)

end Shift

end GeoSeq
