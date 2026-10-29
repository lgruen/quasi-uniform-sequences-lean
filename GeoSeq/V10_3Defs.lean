/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_3PF
public import GeoSeq.V94Defs
public import GeoSeq.V93Defs
public import GeoSeq.V99CovDefs
public import GeoSeq.V95Defs

@[expose] public section

/-!
# GeoSeq stage V10-3: definitions for prime-power bases (`sec:primepower`, `sec:fail` over `𝔽_q`)

* **`prop:primepower`.** The certificate `ppCheck` (a `Bool`, evaluated by the kernel): for the weights `w` of the
  coordinates `c ≠ c⋆` (in the order `c⋆.succAbove`), every step `e ∈ {-1,0,1}^s \ {0}`, every choice of digit
  increments `Δ_c` from a list `Δs` and every digit `r`, `N + 1 ≤ |e_{c⋆} q + enc(r + σ) - enc(r)|` with
  `σ = ∑_{c ≠ c⋆} e_c w_c Δ_c`, organised through two checked lists (the products `w_c Δ` and the values `σ`) so that
  no field multiplication is repeated; then `β_q(k) ≥ N/q` (`V10_3Beta.lean`, `pp_sep`). `PPConcl` is the conclusion
  of `prop:primepower` (`(0,s)`-sequence, `sep(P_{sK}) ≥ β` for every `K ≥ 1`, `δ(P_{[N]}) ≥ (β/q) N^{-1/s}`,
  quasi-uniform). `PF.pbDelta` is the set `𝒟_f = {1, 1+x, …, 1+x+⋯+x^{r-1}}` of the power-basis code.
* **`sec:fail` with a general digit code.** The index polynomial `idxPolyD D n = ∑_k enc⁻¹(n_k) z^k` of the integer
  index `n = ∑_k n_k q^k`, its inverse `polyIdxD`, the points `linPtD D Y n` of a sequence with linear coordinates
  `Y_c` read through the code, and the hypothesis `IsCarryPair D ȳ y°` (the content of `eq:carrydigit`:
  `enc ȳ = q - 1` and `enc(y° - ȳ) = enc(y°) + 1`).
-/

namespace GeoSeq

open Finset Polynomial

/-! ## The certificate of `prop:primepower` -/

/-- All vectors `Fin n → α` with entries in the list `L`. -/
def vecsOf {α : Type*} : (n : ℕ) → List α → List (Fin n → α)
  | 0, _ => [Fin.elim0]
  | n + 1, L => L.flatMap fun x => (vecsOf n L).map (Fin.cons x)

/-- `N + 1 ≤ |e q + enc(r + σ) - enc(r)|` for every digit `r` of the list (`q f_1(e, σ) ≥ N`). -/
def gapOK {F : Type*} [Add F] (enc : F → ℕ) (q : ℕ) (elems : List F) (e : ℤ) (σ : F) (N : ℕ) : Bool :=
  elems.all fun r => decide (N + 1 ≤ ((e * q + (enc (r + σ) : ℤ) - enc r).natAbs))

/-- All vectors `Fin n → α` with entry `i` in the list `L i`. -/
def vecsOfL {α : Type*} : (n : ℕ) → (Fin n → List α) → List (Fin n → α)
  | 0, _ => [Fin.elim0]
  | n + 1, L => (L 0).flatMap fun x => (vecsOfL n (Fin.tail L)).map (Fin.cons x)

/-- `e · x` for `e ∈ {-1, 0, 1}` without multiplication (`x`, `-x`, `0`). -/
def smul3 {F : Type*} [Neg F] [Zero F] (e : ℤ) (x : F) : F := if e = 1 then x else if e = -1 then -x else 0

/-- **The certificate of `prop:primepower`**: `q β_q(k) ≥ N`. With `prods i` a list containing the products `w_i Δ`
(`Δ ∈ Δs`, `w_i` the weight of the coordinate `c⋆.succAbove i`) and `S` a list containing every value
`σ = ∑_i e'_i w_i Δ_i` with `e' ∈ {-1,0,1}^n \ {0}`: `N + 1 ≤ q` (the axis step of `c⋆`), the two inclusions, and
`gapOK` for every `σ ∈ S` and every `e_{c⋆} ∈ {-1,0,1}`. (The lists `prods`, `S` only make the kernel evaluation fast;
they are checked, not trusted.) -/
def ppCheck {F : Type*} [CommRing F] [DecidableEq F] (enc : F → ℕ) (q : ℕ) (elems Δs : List F) (n : ℕ)
    (w : Fin n → F) (prods : Fin n → List F) (S : List F) (N : ℕ) : Bool :=
  decide (N + 1 ≤ q) &&
    (List.finRange n).all (fun i => Δs.all fun Δ => decide (w i * Δ ∈ prods i)) &&
    (vecsOf n [-1, 0, 1]).all (fun e' => decide (∀ i, e' i = 0) ||
      (vecsOfL n prods).all fun P => decide ((∑ i, smul3 (e' i) (P i)) ∈ S)) &&
    S.all (fun σ => [(-1 : ℤ), 0, 1].all fun es => gapOK enc q elems es σ N)

/-- **The conclusion of `prop:primepower`** for the sequence `C` and the bound `β`: a digital `(0,s)`-sequence with
`sep(P_{sK}) ≥ β` for every `K ≥ 1`, `δ(P_{[N]}) ≥ (β/q) N^{-1/s}` for every `N ≥ 2`, and quasi-uniform. -/
def PPConcl {R : Type*} [CommRing R] {q : ℕ} [NeZero q] (D : DigitCode R q) (s : ℕ) (C : Gen s R) (β : ℝ) :
    Prop :=
  IsSeq0 D C ∧ (∀ K, 1 ≤ K → SepAtLevel q s K (seqPoint D C) β) ∧ SepAllN s (seqPoint D C) (β / q) ∧
    IsQuasiUniform (seqPoint D C)

namespace PF

variable {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [NeZero p]

/-- The inverse map given by a table of codes (`a ↦ dec(L[enc a])`). -/
def tabInv (L : List ℕ) (a : PF p d fc) : PF p d fc := dec (L.getD (encN a) 0)

/-- All elements, in the order of their codes. -/
def elems (p d : ℕ) [NeZero p] (fc : Fin (d + 1) → ZMod p) : List (PF p d fc) :=
  (List.range (p ^ (d + 1))).map dec

/-- The digit increments of the power-basis code (`sec:primepower`):
`𝒟_f = {1, 1 + x, …, 1 + x + ⋯ + x^d}` (codes `1, 1 + p, …, 1 + p + ⋯ + p^d`). -/
def pbDelta (p d : ℕ) [NeZero p] (fc : Fin (d + 1) → ZMod p) : List (PF p d fc) :=
  (List.range (d + 1)).map fun j => dec (∑ i ∈ range (j + 1), p ^ i)

end PF

/-! ## `sec:fail` with a general digit code -/

section Fail
variable {F : Type*} [Field F] {q s : ℕ}

/-- The index polynomial `V = ∑_k enc⁻¹(n_k) z^k ∈ 𝔽_q[z]` of the integer index `n = ∑_k n_k q^k` (`sec:prelim`). -/
noncomputable def idxPolyD [NeZero q] (D : DigitCode F q) (n : ℕ) : F[X] :=
  ∑ k ∈ range (n + 1), monomial k (idxDigit D n k)

/-- The integer index `ι(V) = ∑_k enc(V_k) q^k` of a polynomial (`sec:prelim`). -/
noncomputable def polyIdxD (D : DigitCode F q) (V : F[X]) : ℕ :=
  ∑ k ∈ range (V.natDegree + 1), (D.enc (V.coeff k) : ℕ) * q ^ k

/-- The point with index `n` of the sequence with linear coordinates `Y_c` over `𝔽_q`, digits read through the
code: `y_c(n) = ∑_j enc(Y_c(V)_j) q^{-j-1}`, `V = idxPolyD D n`. -/
noncomputable def linPtD [NeZero q] (D : DigitCode F q) (Y : Fin s → F[X] → ℕ → F) (n : ℕ) : Fin s → ℝ :=
  fun c => ∑' j : ℕ, ((D.enc (Y c (idxPolyD D n) j) : ℕ) : ℝ) / (q : ℝ) ^ (j + 1)

/-- The scrambled frame of `cor:unscrambled` over any field: `C_ĉ = μ diag(β^n) P_{a_ĉ}`, `C_c = L_c P_{a_c}`
(`c ≠ ĉ`); with `μ = β = 1` and `L_c = I` the unscrambled frame. -/
def scrFrameF (a : Fin s → F) (ch : Fin s) (μ β : F) (L : Fin s → ℕ → ℕ → F) : Gen s F :=
  fun c n k => if c = ch then μ * β ^ n * pas (a ch) n k else ∑ j ∈ range (n + 1), L c n j * pas (a c) j k

end Fail

section Code
variable {F : Type*} [AddCommGroup F] {q : ℕ}

/-- **`eq:carrydigit`** as a hypothesis on a digit code: the top digit `ȳ` has code `q - 1`, and adding `-ȳ` to `y°`
raises its code by one (`enc(y° - ȳ) = enc(y°) + 1`). For the natural identification `ȳ = enc⁻¹(q-1)`,
`y° = enc⁻¹(q/p - 1)` (`carryPair_pb`). -/
def IsCarryPair (D : DigitCode F q) (yb yo : F) : Prop :=
  (D.enc yb : ℕ) = q - 1 ∧ (D.enc (yo - yb) : ℕ) = (D.enc yo : ℕ) + 1

/-- **A natural identification** (`sec:prelim`) of the digits of `F` with `{0, …, q-1}`: `enc y = ∑_i φ(y)_i p^i`
for an additive bijection `φ : F ≃+ 𝔽_p^{d+1}` (the coordinates in an `𝔽_p`-basis of `F`; Niederreiter's natural
identification also asks the basis to contain `1`, which is not needed for `eq:carrydigit`). -/
def IsNatCode {p : ℕ} (D : DigitCode F q) (d : ℕ) (φ : F ≃+ (Fin (d + 1) → ZMod p)) : Prop :=
  ∀ y, (D.enc y : ℕ) = ∑ i, (φ y i).val * p ^ (i : ℕ)

end Code

/-- The coefficient vector `PF.v` as an additive bijection `PF p d fc ≃+ 𝔽_p^{d+1}` (the coordinates of the
power-basis code). -/
def PF.vEquiv {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [Fact p.Prime] [NeZero p] : PF p d fc ≃+ (Fin (d + 1) → ZMod p) where
  toFun := PF.v
  invFun := PF.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end GeoSeq
