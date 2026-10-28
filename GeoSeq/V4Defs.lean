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
# GeoSeq stage V4: definitions for the small primes (`thm:LF`, `app:LFdata`)

* **Integer frames**: places `a_c ∈ ℤ` (`frameA`), `w'(a_c) = ∏_{b≠c} (a_c - a_b)` (`frameW`), the frame
  polynomial `w = ∏_{c<s} (z - a_c)` over `𝔽_p` (`framePoly`). Every frame of `tab:LFlist` is integral.
* **Ordered designs** (`thm:LF`(a), `app:LFdata`): `ODesign` = integer frame, rational scale
  `θ = thn/thd`, integer superdiagonal `d_1, …, d_{s-1}` (`sup`, entry `0` unused) and the row order of every
  column (fast row first). The upper crosses are determined by `lem:cauchy`: with `λ_0 = 1` and
  `κ_{c-1←c} = d_c`, `κ_{c←j} = θ^{-(j-c-1)} ∏_{i=c}^{j-1} d_{i+1} w'(a_i) (a_{i+1} - a_i) / (w'(a_c)(a_j - a_c))`
  = `odNum/odDen` (`odK` = the integer quotient). The windows are those of `lem:ws` in the stored row order
  (`odN`, `odBp`: `B = ν` for the fast row, `B = max(ν, ⌈(Nν-1)/2⌉)` and `N ← N - 1 + ⌈p/ν⌉` for each slow
  row), `M_0 = 1`, `M_j = N`, `A_c = B_c`, lower crosses full (`odWin`), and `Γ = max_c (2B_c + M_c)`
  (`odCost`). `odValid p D`: the conditions of an ordered design at `p` (row orders are permutations,
  places distinct mod `p`, `θ` prime to `p`, positive superdiagonal prime to `p`, integral nonzero upper
  triangle, `Γ < p`); decidable, checked by `decide +kernel` on the archived data.
* The `𝔽_p` data of an ordered design: `odTheta` (`θ`), `odLam` (`λ_c = θ^c/∏_{i<c} d_{i+1} w'(a_i)(a_{i+1}-a_i)`).
* **Explicit ordered windows** (`thm:LF`(b)): `EDesign` = integer frame, `θ`, `λ_c` (integers mod `p`),
  integer upper crosses, `A_c`, `M_c`, `B_{c←j}`; `edValid p E` checks the crosses (`θλ_c ≡ κ_{c←j} λ_j w'(a_c)
  (a_j - a_c)`), condition (i), the integer conditions of `def:lex` and the coverings of every column by
  enumeration of `𝔽_p^j` (`edCover`, `lem:lexcover`).
* **Range checker**: `lfSmallDiv`, `lfCover` (every integer of a range is either in the sorted list of
  archived primes or has a small divisor), `ODRec` (an archived record: prime and design), `lfOK`.
-/

namespace GeoSeq

open Finset

/-! ## Integer frames -/

/-- The place `a_c` of an integer frame stored as a list. -/
def frameA (fr : List ℤ) (c : ℕ) : ℤ := fr.getD c 0

/-- `w'(a_c) = ∏_{b<s, b≠c} (a_c - a_b)` for an integer frame. -/
def frameW (s : ℕ) (fr : List ℤ) (c : ℕ) : ℤ := ∏ b ∈ (range s).erase c, (frameA fr c - frameA fr b)

/-- The frame polynomial `w = ∏_{c<s} (z - a_c)` over `𝔽_p`. -/
noncomputable def framePoly (p s : ℕ) (fr : List ℤ) : Polynomial (ZMod p) :=
  ∏ c ∈ range s, (Polynomial.X - Polynomial.C ((frameA fr c : ℤ) : ZMod p))

/-! ## Ordered designs (`thm:LF`(a)) -/

/-- **An ordered design with an integer frame** (`sec:order`, "Small primes"; `app:LFdata`): places
`a_c = frame[c]`, scale `θ = thn/thd`, superdiagonal `d_c = sup[c]` (`1 ≤ c ≤ s-1`; `sup[0]` unused), and
`ord[j]` = the rows `0, …, j-1` of column `j` in the order used by `lem:ws` (fast row first). -/
structure ODesign (s : ℕ) where
  frame : List ℤ
  thn : ℤ
  thd : ℤ
  sup : List ℤ
  ord : List (List ℕ)

variable {s : ℕ}

/-- `d_{i+1} w'(a_i) (a_{i+1} - a_i)`, the `i`-th factor of the products of `lem:cauchy`. -/
def odFac (D : ODesign s) (i : ℕ) : ℤ :=
  D.sup.getD (i + 1) 0 * frameW s D.frame i * (frameA D.frame (i + 1) - frameA D.frame i)

/-- `Q_{cj} = ∏_{i=c}^{j-1} d_{i+1} w'(a_i) (a_{i+1} - a_i)`. -/
def odQ (D : ODesign s) (c j : ℕ) : ℤ := ∏ i ∈ Ico c j, odFac D i

/-- Numerator of `κ_{c←j}`: `thd^{j-c-1} Q_{cj}`. -/
def odNum (D : ODesign s) (c j : ℕ) : ℤ := D.thd ^ (j - c - 1) * odQ D c j

/-- Denominator of `κ_{c←j}`: `thn^{j-c-1} w'(a_c) (a_j - a_c)`. -/
def odDen (D : ODesign s) (c j : ℕ) : ℤ :=
  D.thn ^ (j - c - 1) * frameW s D.frame c * (frameA D.frame j - frameA D.frame c)

/-- **The upper cross** `κ_{c←j} = odNum/odDen` (`c < j`; an integer when `odDen ∣ odNum`, `lem:cauchy`). -/
def odK (D : ODesign s) (c j : ℕ) : ℤ := odNum D c j / odDen D c j

/-- The row at position `t` of the order of column `j`. -/
def odRow (D : ODesign s) (j t : ℕ) : ℕ := (D.ord.getD j []).getD t 0

/-- The position of row `c` in the order of column `j`. -/
def odPos (D : ODesign s) (c j : ℕ) : ℕ := (D.ord.getD j []).idxOf c

/-- `ν_t = |κ_{r_t←j}|` for the row `r_t` at position `t` of column `j`. -/
def odNu (D : ODesign s) (j t : ℕ) : ℕ := (odK D (odRow D j t) j).natAbs

/-- The run lengths of `lem:ws` for column `j` in the stored order: `N_0 = 1 + ⌈(p - 2ν_0 - 1)/ν_0⌉`,
`N_t = N_{t-1} - 1 + ⌈p/ν_t⌉`. -/
def odN (D : ODesign s) (p j : ℕ) : ℕ → ℕ
  | 0 => 1 + cdiv (p - 2 * odNu D j 0 - 1) (odNu D j 0)
  | t + 1 => odN D p j t - 1 + cdiv p (odNu D j (t + 1))

/-- The window `B` of the row at position `t` of column `j`: `ν_0` (fast row), else
`max(ν_t, ⌈(N_{t-1} ν_t - 1)/2⌉)` (`app:LFdata`). -/
def odBp (D : ODesign s) (p j t : ℕ) : ℕ :=
  if t = 0 then odNu D j 0 else max (odNu D j t) (cdiv (odN D p j (t - 1) * odNu D j t - 1) 2)

/-- `B_{c←j}`. -/
def odBx (D : ODesign s) (p c j : ℕ) : ℕ := odBp D p j (odPos D c j)

/-- `M_0 = 1`, `M_j = N_{j-1}`. -/
def odM (D : ODesign s) (p j : ℕ) : ℕ := if j = 0 then 1 else odN D p j (j - 1)

/-- `B_c = ∑_{j>c} B_{c←j}` (`= A_c`). -/
def odB (D : ODesign s) (p c : ℕ) : ℕ := ∑ j ∈ Ioo c s, odBx D p c j

/-- **The cost** `Γ = max_c (2B_c + M_c)` of an ordered design at `p`. -/
def odCost (D : ODesign s) (p : ℕ) : ℕ := (range s).sup fun c => 2 * odB D p c + odM D p c

/-- **The windows of an ordered design** at `p`: ordered windows (`def:lex`) with `A_c = B_c`. -/
def odWin (D : ODesign s) (p : ℕ) : Fin s → Fin s → Set (ZMod p) :=
  lexWin p (fun c => odB D p c) (fun c => odM D p c) (fun c j => odBx D p c j)

/-- **The conditions of an ordered design at `p`** (`sec:order`, "Small primes"; `app:LFdata`): the row
orders are permutations of `0, …, j-1`; the places are distinct mod `p`; `θ` is prime to `p`; the
superdiagonal is positive and prime to `p`; the upper triangle is integral (`odDen ∣ odNum`) and nonzero;
and `Γ < p`. -/
def odValid (p : ℕ) (D : ODesign s) : Prop :=
  (∀ j < s, (D.ord.getD j []).length = j ∧ (D.ord.getD j []).Nodup ∧ ∀ x ∈ D.ord.getD j [], x < j) ∧
  (∀ c < s, ∀ b < c, (frameA D.frame c - frameA D.frame b) % (p : ℤ) ≠ 0) ∧
  D.thn % (p : ℤ) ≠ 0 ∧ D.thd % (p : ℤ) ≠ 0 ∧
  (∀ i < s, 1 ≤ i → 0 < D.sup.getD i 0 ∧ D.sup.getD i 0 % (p : ℤ) ≠ 0) ∧
  (∀ j < s, ∀ c < j, odNum D c j % odDen D c j = 0 ∧ odK D c j ≠ 0) ∧
  odCost D p < p

instance (p : ℕ) (D : ODesign s) : Decidable (odValid p D) := by unfold odValid; infer_instance

/-- The scale `θ = thn/thd` in `𝔽_p`. -/
def odTheta (D : ODesign s) (p : ℕ) [Fact p.Prime] : ZMod p := (D.thn : ZMod p) / (D.thd : ZMod p)

/-- The constants `λ_c = θ^c / Q_{0c}` in `𝔽_p` (so that `κ_{c-1←c} = d_c`, `lem:cauchy`). -/
def odLam (D : ODesign s) (p : ℕ) [Fact p.Prime] : Fin s → ZMod p :=
  fun c => odTheta D p ^ (c : ℕ) / (odQ D 0 c : ZMod p)

/-! ## Explicit ordered windows (`thm:LF`(b)) -/

/-- **Explicit ordered windows** over `𝔽_p` with an integer frame: places `a_c`, scale `θ`, constants
`λ_c` (integers read mod `p`), integer upper crosses `κ_{c←j} = kap[c][j]` (`c < j`), own windows
`[-(A_c+M_c-1), -A_c]`, upper cross windows `[-B_{c←j}, B_{c←j}]`, `B_{c←j} = Bx[c][j]`. -/
structure EDesign (s : ℕ) where
  frame : List ℤ
  th : ℤ
  lam : List ℤ
  kap : List (List ℤ)
  A : List ℕ
  M : List ℕ
  Bx : List (List ℕ)

/-- `κ_{c←j}`. -/
def edK (E : EDesign s) (c j : ℕ) : ℤ := (E.kap.getD c []).getD j 0

/-- `B_{c←j}`. -/
def edBx (E : EDesign s) (c j : ℕ) : ℕ := (E.Bx.getD c []).getD j 0

/-- The own window offset `A_c`. -/
def edA (E : EDesign s) (c : ℕ) : ℕ := E.A.getD c 0

/-- The own window size `M_c`. -/
def edM (E : EDesign s) (c : ℕ) : ℕ := E.M.getD c 0

/-- `λ_c` (an integer). -/
def edLamZ (E : EDesign s) (c : ℕ) : ℤ := E.lam.getD c 0

/-- The windows of explicit ordered windows (`def:lex`). -/
def edWin (E : EDesign s) (p : ℕ) : Fin s → Fin s → Set (ZMod p) :=
  lexWin p (fun c => edA E c) (fun c => edM E c) (fun c j => edBx E c j)

/-- `Γ = max_c (A_c + M_c + B_c)` (`lexCost`). -/
def edCost (E : EDesign s) : ℕ :=
  lexCost (fun c : Fin s => edA E c) (fun c => edM E c) (fun c j => edBx E c j)

/-- The offset of own value `i` (`o_i = -(A_j+M_j-1) + i`) in row `c` of column `j`:
`(o_i κ_{c←j} + B_{c←j}) mod p` (a natural number `< p`). -/
def edOff (p : ℕ) (E : EDesign s) (j c i : ℕ) : ℕ :=
  (((-((edA E j : ℤ) + edM E j - 1) + i) * edK E c j + edBx E c j) % (p : ℤ)).toNat

/-- The offsets of all own values of column `j` (rows `0, …, j-1`). -/
def edOffs (p : ℕ) (E : EDesign s) (j : ℕ) : List (List ℕ) :=
  (List.range (edM E j)).map fun i => (List.range j).map fun c => edOff p E j c i

/-- Rows `c < k` of an own value with offsets `rs` lie in their windows at the point `σ`:
`(σ_c + rs_c) mod p ≤ 2B_c`, i.e. `σ_c + o κ_{c←j} ∈ [-B_c, B_c]` modulo `p`. -/
def rowsOK (p : ℕ) (Bs σ rs : List ℕ) (k : ℕ) : Bool :=
  (List.range k).all fun c => decide ((σ.getD c 0 + rs.getD c 0) % p ≤ 2 * Bs.getD c 0)

/-- Enumerate the points of `[0,p)^k` appended to the prefix `σ`. -/
def enumAll (p : ℕ) (test : List ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, σ => test σ
  | k + 1, σ => (List.range p).all fun x => enumAll p test k (σ ++ [x])

/-- **The covering of column `j ≥ 1` by enumeration of `𝔽_p^j`** (`lem:lexcover`, second form): for every
`(σ_0, …, σ_{j-2})` the own values whose rows `c < j-1` lie in their windows (`G`) cover every
`σ_{j-1} ∈ 𝔽_p` in row `j-1`. Column `0` has no upper rows (`true`). -/
def edCover (p : ℕ) (E : EDesign s) (j : ℕ) : Bool :=
  if j = 0 then true else
  enumAll p (fun pre =>
    (List.range p).all fun x =>
      ((edOffs p E j).filter fun rs => rowsOK p ((List.range j).map fun c => edBx E c j) pre rs (j - 1)).any
        fun rs => decide ((x + rs.getD (j - 1) 0) % p ≤ 2 * edBx E (j - 1) j)) (j - 1) []

/-- **The conditions of explicit ordered windows at `p`**: places distinct mod `p`; `θ`, `λ_c` prime to `p`;
the crosses `θ λ_c ≡ κ_{c←j} λ_j w'(a_c) (a_j - a_c)` (`prop:LI`(c), λ-form); condition (i)
`|κ_{c←j}| ≤ B_{c←j}`; the integer conditions of `def:lex` (`M_c ≥ 1`, `B_c ≤ A_c`, `A_c + M_c + B_c ≤ p`);
`Γ < p`; and the covering of every column by enumeration. -/
def edValid (p : ℕ) (E : EDesign s) : Prop :=
  (∀ c < s, ∀ b < c, (frameA E.frame c - frameA E.frame b) % (p : ℤ) ≠ 0) ∧
  E.th % (p : ℤ) ≠ 0 ∧ (∀ c < s, edLamZ E c % (p : ℤ) ≠ 0) ∧
  (∀ j < s, ∀ c < j, (E.th * edLamZ E c - edK E c j * edLamZ E j * frameW s E.frame c *
      (frameA E.frame j - frameA E.frame c)) % (p : ℤ) = 0 ∧ (edK E c j).natAbs ≤ edBx E c j) ∧
  (∀ c < s, 1 ≤ edM E c ∧ (∑ j ∈ Ioo c s, edBx E c j) ≤ edA E c ∧
      edA E c + edM E c + ∑ j ∈ Ioo c s, edBx E c j ≤ p) ∧
  edCost E < p ∧
  (∀ j < s, edCover p E j = true)

instance (p : ℕ) (E : EDesign s) : Decidable (edValid p E) := by unfold edValid; infer_instance

/-- The scale `θ` of explicit ordered windows in `𝔽_p`. -/
def edTheta (E : EDesign s) (p : ℕ) : ZMod p := (E.th : ZMod p)

/-- The constants `λ_c ∈ 𝔽_p` of explicit ordered windows. -/
def edLam (E : EDesign s) (p : ℕ) : Fin s → ZMod p := fun c => (edLamZ E c : ZMod p)

/-- `11` is prime (`thm:LF`(b)). -/
instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `37` is prime (`thm:LF`(b)). -/
instance fact_prime_37 : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- `p = 11`, `s = 3` (`app:LFdata`): Faure frame `(0,1,2)`, `θ = 5`, `λ = (1,4,2)`, upper crosses
`(κ_{0←1}, κ_{0←2}, κ_{1←2}) = (2,2,1)`, upper windows `[-2,2]`, own windows `[-4,-4]`, `[-5,-2]`, `[-9,0]`
(`A = (4,2,0)`, `M = (1,4,10)`). -/
def edP11 : EDesign 3 :=
  ⟨[0, 1, 2], 5, [1, 4, 2], [[0, 2, 2], [0, 0, 1], [0, 0, 0]], [4, 2, 0], [1, 4, 10],
    [[0, 2, 2], [0, 0, 2], [0, 0, 0]]⟩

/-- `p = 37`, `s = 4` (`lex_witnesses/smallp/s4_p37.cfg`): places `(0,1,35,34)`, `θ = 25`,
`λ = (1,19,15,10)`, upper crosses `κ_{0←1} = 4`, `κ_{0←2} = -5`, `κ_{0←3} = -5`, `κ_{1←2} = 7`,
`κ_{1←3} = -6`, `κ_{2←3} = 3`; upper windows `B_{0←1} = 4`, `B_{0←2} = 6`, `B_{0←3} = 7`, `B_{1←2} = 7`,
`B_{1←3} = 7`, `B_{2←3} = 9`; own windows `[-17,-17]`, `[-21,-14]`, `[-23,-9]`, `[-35,0]`
(`A = (17,14,9,0)`, `M = (1,8,15,36)`). -/
def edP37 : EDesign 4 :=
  ⟨[0, 1, 35, 34], 25, [1, 19, 15, 10],
    [[0, 4, -5, -5], [0, 0, 7, -6], [0, 0, 0, 3], [0, 0, 0, 0]], [17, 14, 9, 0], [1, 8, 15, 36],
    [[0, 4, 6, 7], [0, 0, 7, 7], [0, 0, 0, 9], [0, 0, 0, 0]]⟩

/-! ## Range checker -/

/-- A divisor `2 ≤ d < min(n, B)` of `n`. -/
def lfSmallDiv (n B : ℕ) : Bool := (List.range B).any (fun d => 2 ≤ d && d < n && n % d == 0)

/-- Every integer of `[n, n + k)` is either the head of the (sorted) list `ps` when reached, or has a
small divisor. -/
def lfCover (B : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, 0, _ => true
  | n, k + 1, [] => lfSmallDiv n B && lfCover B (n + 1) k []
  | n, k + 1, q :: qs => if q = n then lfCover B (n + 1) k qs
      else lfSmallDiv n B && lfCover B (n + 1) k (q :: qs)

/-- **An archived record**: a prime and an ordered design. -/
structure ODRec (s : ℕ) where
  p : ℕ
  D : ODesign s

/-- A record passes: the design is valid at its prime, and `(p - Γ)/p > 1/10` from `y1` on and
`(p - Γ)/p ≥ 3/10` from `y3` on (integer forms `p < 10(p - Γ)`, `3p ≤ 10(p - Γ)`). -/
def ODRec.ok (y1 y3 : ℕ) (r : ODRec s) : Bool :=
  decide (odValid r.p r.D) && (!decide (y1 ≤ r.p) || decide (r.p < 10 * (r.p - odCost r.D r.p))) &&
    (!decide (y3 ≤ r.p) || decide (3 * r.p ≤ 10 * (r.p - odCost r.D r.p)))

/-- **The archive check of a range** `[lo, lo + len)`: every record passes and every integer of the range is
an archived prime or has a divisor `2 ≤ d < min(n, B)`. -/
def lfOK (lo len B y1 y3 : ℕ) (recs : List (ODRec s)) : Bool :=
  recs.all (ODRec.ok y1 y3) && lfCover B lo len (recs.map ODRec.p)

end GeoSeq
