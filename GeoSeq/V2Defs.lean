/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V1Defs
public import GeoSeq.SteerDefs

@[expose] public section

/-!
# GeoSeq stage V2: definitions for ordering the coordinates (`sec:order`)

* **Ordered windows** (`def:lex`): integer data `A_c`, `M_c` (own windows) and `B_{c←c'}` (upper crosses,
  `c < c'`; `Bx c c'`), `B_c = ∑_{c'>c} B_{c←c'}` (`lexB`); `lexWin` = the window system (lower crosses full,
  upper crosses `[-B_{c←c'}, B_{c←c'}]`, own windows `[-(A_c+M_c-1), -A_c]`), `IsLexData` = the integer
  conditions `M_c ≥ 1`, `B_c ≤ A_c`, `A_c + M_c + B_c ≤ p`; `lexCost` = `max_c (A_c + M_c + B_c)` (for
  `A_c = B_c` the cost `Γ = max_c (2B_c + M_c)` of `rem:lexexact`).
* **Mixed-radix coverings** (`lem:ws`): arcs `arc p L len = {L, …, L+len-1} mod p`, the ceiling `cdiv`,
  the run lengths `wsN` (`N_1 = 1 + ⌈(p-|I_1|)/ν_1⌉`, `N_t = N_{t-1} - 1 + ⌈p/ν_t⌉`; rows indexed from `0`).
* **Cauchy structure** (`lem:cauchy`): `tauC` = `τ(c,c',j)`, `predF` (`i ↦ i-1` on `Fin s`).
* **Mixed-radix designs** (`def:MR`): `mrMu` = `μ_{cj}`, `mrG` = their gcd, `mrNu` = `ν_{tj} = μ̄_{tj} h_{t+1}⋯h_j`,
  `mrKapZ` = the integer cross `(-1)^{n-t} ν_{tj}`, the column recursion `mrN`, the windows `mrBx`
  (`B_{t←j}`), `mrM` (`M_j`), `mrB` (`B_c = A_c`), the cost `mrCost` (`Γ`), `mrWin` (the ordered windows of
  (MR3)), the Faure frame `faureW` (`w = ∏_{c<s} (z - c)`), the scale `mrTheta` (`θ = n!/gcd`) and the
  constants `mrLam` (`λ_c = (n-c)!/(h_1⋯h_c)`); `mrGamma` (`γ_t`) and `mrQss` (`Q_s^s`) of the
  mixed-radix rule (rational numbers; the rounding of the rule is stage V3).
Indices: rows and columns of a design are natural numbers `< s` (read as `Fin s` in the windows);
step factors `h : ℕ → ℕ`, of which only `h 1, …, h n` (`n = s - 1`) are read.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Ordered windows (`def:lex`) -/

section Lex

variable {s : ℕ}

/-- `B_c = ∑_{c' > c} B_{c←c'}` (`def:lex`). -/
def lexB (Bx : Fin s → Fin s → ℕ) (c : Fin s) : ℕ := ∑ c' ∈ univ.filter (fun c' => c < c'), Bx c c'

/-- **Ordered windows** (`def:lex`), in the order `0 < 1 < ⋯ < s-1`: every lower cross is full
(`W_{c←c'} = 𝔽_p` for `c > c'`), every upper cross is the symmetric interval `[-B_{c←c'}, B_{c←c'}]`
(`c < c'`), and every own window is the interval `Wo^{(c)} = [-(A_c+M_c-1), -A_c]` just behind `0`. -/
def lexWin (p : ℕ) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) : Fin s → Fin s → Set (ZMod p) :=
  fun c c' => if c' < c then Set.univ
    else if c < c' then intWin p (-(Bx c c' : ℤ)) (Bx c c')
    else intWin p (-((A c : ℤ) + M c - 1)) (-(A c : ℤ))

/-- The integer conditions of `def:lex`: `M_c ≥ 1`, `B_c ≤ A_c` and `A_c + M_c + B_c ≤ p`. -/
def IsLexData (p : ℕ) (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) : Prop :=
  ∀ c, 1 ≤ M c ∧ lexB Bx c ≤ A c ∧ A c + M c + lexB Bx c ≤ p

/-- `max_c (A_c + M_c + B_c)` (`lem:lex`, `rem:lexexact`; `= Γ = max_c (2B_c + M_c)` when `A_c = B_c`). -/
def lexCost (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) : ℕ := univ.sup fun c => A c + M c + lexB Bx c

end Lex

/-! ## Mixed-radix coverings (`lem:ws`) -/

/-- An **arc** (`sec:order`): the `len` consecutive residues `L, L+1, …, L+len-1` in `ℤ/pℤ`
(a set of at most `p` consecutive residues when `len ≤ p`; then `|I| = len`). -/
def arc (p : ℕ) (L : ℤ) (len : ℕ) : Set (ZMod p) := {x | ∃ i : ℕ, i < len ∧ x = ((L + i : ℤ) : ZMod p)}

/-- The ceiling `⌈a/b⌉ = (a + b - 1)/b` of a quotient of natural numbers (`b ≥ 1`). -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- **The run lengths of `lem:ws`** (rows indexed from `0`: row `0` is the paper's row `1`, the fast row):
`N_0 = 1 + ⌈(p - |I_0|)/ν_0⌉` and `N_t = N_{t-1} - 1 + ⌈p/ν_t⌉` for `t ≥ 1`. -/
def wsN (p : ℕ) (len ν : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1 + cdiv (p - len 0) (ν 0)
  | t + 1 => wsN p len ν t - 1 + cdiv p (ν (t + 1))

/-! ## Cauchy structure (`lem:cauchy`) -/

section Cauchy

variable {F : Type*} [Field F] {s : ℕ}

/-- `τ(c,c',j) = (a_j - a_c)/(w'(a_{c'}) (a_{c'} - a_c) (a_j - a_{c'}))` (`lem:cauchy`), with the places
`a = ssPlace zθ` and `w'(a_{c'}) = placeDer zθ c'`. -/
noncomputable def tauC (zθ : Fin s → PowerSeries F) (c c' j : Fin s) : F :=
  (ssPlace zθ j - ssPlace zθ c) /
    (placeDer zθ c' * (ssPlace zθ c' - ssPlace zθ c) * (ssPlace zθ j - ssPlace zθ c'))

/-- `i ↦ i - 1` on `Fin s` (truncated at `0`). -/
def predF (i : Fin s) : Fin s := ⟨i.val - 1, by omega⟩

end Cauchy

/-! ## Mixed-radix designs (`def:MR`) -/

/-- `μ_{cj} = n!/(c! (n-j)! (j-c))`, `n = s - 1` (`def:MR`; an integer for `c < j ≤ n`). -/
def mrMu (s c j : ℕ) : ℕ := (s - 1).factorial / (c.factorial * (s - 1 - j).factorial * (j - c))

/-- The greatest common divisor of all `μ_{cj}`, `0 ≤ c < j ≤ n` (`def:MR`). -/
def mrG (s : ℕ) : ℕ :=
  ((range s ×ˢ range s).filter (fun x : ℕ × ℕ => x.1 < x.2)).gcd fun x => mrMu s x.1 x.2

/-- `h_{a+1} ⋯ h_b` (empty product `1` for `b ≤ a`). -/
def hprod (h : ℕ → ℕ) (a b : ℕ) : ℕ := ∏ i ∈ Ioc a b, h i

/-- The steps `ν_{tj} = μ̄_{tj} h_{t+1} ⋯ h_j`, `μ̄ = μ/gcd` (`def:MR` (MR2)). -/
def mrNu (s : ℕ) (h : ℕ → ℕ) (t j : ℕ) : ℕ := mrMu s t j / mrG s * hprod h t j

/-- The integer upper crosses `κ_{t←j} = (-1)^{n-t} μ̄_{tj} h_{t+1} ⋯ h_j` (`def:MR` (MR2)). -/
def mrKapZ (s : ℕ) (h : ℕ → ℕ) (t j : ℕ) : ℤ := (-1) ^ (s - 1 - t) * (mrNu s h t j : ℤ)

/-- The recursion (MR2) for column `j`: `N` after row `0` (the fast row) and after each slow row `t`:
`N ← 1 + ⌈(p - 2ν_{0j} - 1)/ν_{0j}⌉`, then `N ← N - 1 + ⌈p/ν_{tj}⌉` for `t = 1, …, j-1`. -/
def mrN (s p : ℕ) (h : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 1 + cdiv (p - 2 * mrNu s h 0 j - 1) (mrNu s h 0 j)
  | t + 1 => mrN s p h j t - 1 + cdiv p (mrNu s h (t + 1) j)

/-- The upper cross windows `B_{t←j}` of (MR2): `B_{0←j} = ν_{0j}`,
`B_{t←j} = max(ν_{tj}, ⌈(N ν_{tj} - 1)/2⌉)` with `N` the value after row `t - 1`. -/
def mrBx (s p : ℕ) (h : ℕ → ℕ) (t j : ℕ) : ℕ :=
  if t = 0 then mrNu s h 0 j else max (mrNu s h t j) (cdiv (mrN s p h j (t - 1) * mrNu s h t j - 1) 2)

/-- The own window sizes: `M_0 = 1` (MR3) and `M_j = N` after the last slow row `j - 1` (MR2). -/
def mrM (s p : ℕ) (h : ℕ → ℕ) (j : ℕ) : ℕ := if j = 0 then 1 else mrN s p h j (j - 1)

/-- `B_c = ∑_{j > c} B_{c←j}` (`= A_c`, (MR3)). -/
def mrB (s p : ℕ) (h : ℕ → ℕ) (c : ℕ) : ℕ := ∑ j ∈ Ioo c s, mrBx s p h c j

/-- **The cost** `Γ = max_c (2B_c + M_c)` of the mixed-radix design (MR3). -/
def mrCost (s p : ℕ) (h : ℕ → ℕ) : ℕ := (range s).sup fun c => 2 * mrB s p h c + mrM s p h c

/-- **The windows of `MR(s,p,h)`** (MR2), (MR3): the ordered windows with `A_c = B_c`, own window sizes
`M_c` and upper crosses `B_{c←j}`. -/
def mrWin (s p : ℕ) (h : ℕ → ℕ) : Fin s → Fin s → Set (ZMod p) :=
  lexWin p (fun c => mrB s p h c) (fun c => mrM s p h c) (fun c j => mrBx s p h c j)

/-- **The Faure frame** `w = ∏_{c<s} (z - c)` over `𝔽_p` (places `a_c = c`; (MR1)). -/
noncomputable def faureW (s p : ℕ) : Polynomial (ZMod p) :=
  ∏ c ∈ range s, (Polynomial.X - Polynomial.C (c : ZMod p))

/-- **The scale** `θ = n!/gcd` of (MR1). -/
def mrTheta (s p : ℕ) : ZMod p := (((s - 1).factorial / mrG s : ℕ) : ZMod p)

/-- **The constants** `λ_c = (n-c)!/(h_1 ⋯ h_c)` of (MR1). -/
noncomputable def mrLam (s p : ℕ) [Fact p.Prime] (h : ℕ → ℕ) : Fin s → ZMod p :=
  fun c => ((s - 1 - c).factorial : ZMod p) / (hprod h 0 c : ZMod p)

/-- `γ_t = ∑_{j=t+1}^{n} μ_{tj}/μ_{t-1,j} + gcd/μ_{t-1,t}` (`def:MR`, the mixed-radix rule). -/
def mrGamma (s t : ℕ) : ℚ :=
  (∑ j ∈ Ioc t (s - 1), (mrMu s t j : ℚ) / mrMu s (t - 1) j) + (mrG s : ℚ) / mrMu s (t - 1) t

/-- `Q_s^s = 2 μ̄_{0n} ∏_{t=1}^{n} γ_t` (`def:MR`, the mixed-radix rule). -/
def mrQss (s : ℕ) : ℚ := 2 * ((mrMu s 0 (s - 1) / mrG s : ℕ) : ℚ) * ∏ t ∈ Ioc 0 (s - 1), mrGamma s t

/-! ## The example `ex:MR101` -/

/-- `101` is prime (for the example `ex:MR101`). -/
instance fact_prime_101 : Fact (Nat.Prime 101) := ⟨by norm_num⟩

/-- The step factors `(h_1, h_2) = (9, 2)` of `ex:MR101` (`s = 3`, `p = 101`; other indices unused). -/
def mrH101 : ℕ → ℕ := fun t => if t = 1 then 9 else if t = 2 then 2 else 1

end GeoSeq
