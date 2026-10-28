/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V9Defs

@[expose] public section

/-!
# GeoSeq stage V9-3 (paper V4, `sec:fail`): definitions for polynomial-base sequences

Shared by the statement file `GeoSeq/Statements/V93.lean` and the proof files `GeoSeq/V93*.lean`.
Prime base `q = p` only (`F = ℤ/pℤ` for the points; the polynomial algebra over any field).

* **Linear coordinates** (plan §2.3). A coordinate of a digital sequence over `𝔽_p` is an additive map
  `Y : 𝔽_p[z] → (ℕ → 𝔽_p)` (index polynomial `V` ↦ digit sequence; `IsLinCoord`). The point with index
  `n = ∑_k n_k p^k` is `y_c(n) = ∑_j Y_c(V)_j p^{-j-1}` with `V = ∑_k n_k z^k` (`idxPolyP`, `linPt`; a digit
  `y ∈ 𝔽_p` is read as `y.val`, the natural identification for prime `q`). Generator-matrix sequences are instances
  (`Y_c(V)_n = ∑_k C_c[n][k] V_k`); the one used here, the unscrambled frame, is identified with a Halton-type
  sequence directly (`frame_eq_haltonPt`).
* **`b`-adic digits** (`sec:polybases`): `a_Q = (V div b^Q) mod b` (`badicDigit`; Mathlib's polynomial
  division over a field, unique quotient and remainder of degree `< deg b`, also for non-monic `b`).
* **`def:radinv`**: `IsBAdic Y b` (the first `e Q` digits vanish on `b^Q 𝔽_p[z]`, `e = deg b`) and
  `IsRadInv Y b π` (digit block `Q` is `π(a_Q)`; `π` maps the polynomials of degree `< e` ONTO the digit
  blocks — surjectivity is all the proofs use; the paper's `π` is a linear bijection).
* **`thm:nonqu`**: the run of ones `S_n = 1 + b + ⋯ + b^{n-1}` (`runS`), `E = lcm(e_c)` (`lcmDeg`),
  `Θ = ∏_{c ≠ ĉ} b_c^{E/e_c}` (`thetaP`), `R = (1 - b) Θ` (`carryR`), and the lower point of the carry pair
  `V_1 = g̃ b^η + g' b^{η+1} S_{λ-η-1}` (`carryV1`, `lem:carrypair`).
* **Halton-type sequences** (`cor:halton`, Goda–Hofer–Suzuki Def. 2): the definitions `idxPolyP`, `badicDigit`,
  `haltonPt` have the same bodies as `idxPoly`, `badicDigit`, `haltonPt` of the Palomar statement
  `HeadlineSeqV4/Challenge_combined_explicit.lean`; the digit map `haltonPi` and the coordinate maps `haltonY`.
* `polyIdx`: the index `∑_k V_k.val p^k` of a polynomial (inverse of `idxPolyP` on polynomials of degree `< m`
  and indices `< p^m`).
-/

namespace GeoSeq

open Finset Polynomial

section Poly
variable {F : Type*} [Field F] {s : ℕ}

/-- The `Q`-th `b`-adic digit `a_Q = (V div b^Q) mod b` of `V = ∑_Q a_Q b^Q` (`deg a_Q < deg b`). -/
noncomputable def badicDigit (b V : F[X]) (Q : ℕ) : F[X] := V / b ^ Q % b

/-- A linear coordinate: `Y(V + W) = Y(V) + Y(W)` digitwise (over a prime field additivity is linearity). -/
def IsLinCoord (Y : F[X] → ℕ → F) : Prop := ∀ V W : F[X], ∀ n : ℕ, Y (V + W) n = Y V n + Y W n

/-- **`def:radinv`**, `b`-adic coordinate: for every `Q`, the first `e Q` digits (`e = deg b`) vanish for
`V ∈ b^Q 𝔽[z]` (by linearity: they depend only on `V mod b^Q`). -/
def IsBAdic (Y : F[X] → ℕ → F) (b : F[X]) : Prop :=
  ∀ Q : ℕ, ∀ V : F[X], b ^ Q ∣ V → ∀ n : ℕ, n < b.natDegree * Q → Y V n = 0

/-- **`def:radinv`**, `b`-adic radical inverse with digit map `π`: digit `Q e + i` (`i < e = deg b`) of `V` is
`π(a_Q)_i`, `a_Q` the `Q`-th `b`-adic digit of `V`; and `π` maps the polynomials of degree `< e` onto the digit
blocks `(u_0, …, u_{e-1})`. -/
def IsRadInv (Y : F[X] → ℕ → F) (b : F[X]) (π : F[X] → ℕ → F) : Prop :=
  (∀ u : ℕ → F, ∃ a : F[X], a.natDegree < b.natDegree ∧ ∀ i, i < b.natDegree → π a i = u i) ∧
    ∀ V : F[X], ∀ Q i : ℕ, i < b.natDegree → Y V (Q * b.natDegree + i) = π (badicDigit b V Q) i

/-- The run of ones `S_n = 1 + b + ⋯ + b^{n-1} = (b^n - 1)/(b - 1)`. -/
noncomputable def runS (b : F[X]) (n : ℕ) : F[X] := ∑ j ∈ range n, b ^ j

/-- `E = lcm(e_0, …, e_{s-1})`, `e_c = deg b_c`. -/
noncomputable def lcmDeg (b : Fin s → F[X]) : ℕ := univ.lcm fun c => (b c).natDegree

/-- `Θ = ∏_{c ≠ ĉ} b_c^{E/e_c}` (`thm:nonqu`). -/
noncomputable def thetaP (b : Fin s → F[X]) (ch : Fin s) : F[X] :=
  ∏ c ∈ univ.erase ch, b c ^ (lcmDeg b / (b c).natDegree)

/-- `R = (1 - b) Θ`, `b = b_ĉ` (`thm:nonqu`). -/
noncomputable def carryR (b : Fin s → F[X]) (ch : Fin s) : F[X] := (1 - b ch) * thetaP b ch

/-- The lower point of the carry pair (`lem:carrypair`): `V_1 = g̃ b^η + g' b^{η+1} S_{λ-η-1}`. -/
noncomputable def carryV1 (b gt g' : F[X]) (η l : ℕ) : F[X] :=
  gt * b ^ η + g' * b ^ (η + 1) * runS b (l - η - 1)

/-- The carry difference of `thm:nonqu`: `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}` (`b = b_ĉ`). -/
noncomputable def nonquD (b : Fin s → F[X]) (ch : Fin s) (g : F[X]) (ν k η Q : ℕ) : F[X] :=
  g * b ch ^ (Q * η) * runS (b ch) (Q * ν) * thetaP b ch ^ (Q * k)

/-- The lower point of the pair of `thm:nonqu`: `V_1` of `lem:carrypair` with `(η, λ) = (Qη, Q(η + ν))`. -/
noncomputable def nonquV1 (b : Fin s → F[X]) (ch : Fin s) (gt g' : F[X]) (ν η Q : ℕ) : F[X] :=
  carryV1 (b ch) gt g' (Q * η) (Q * (η + ν))

/-- The Halton digit map `π(a) = ([z^{e-1}] a, …, [z^0] a)` (GHS Def. 2; `sec:polybases`). -/
noncomputable def haltonPi (e : ℕ) (a : F[X]) (i : ℕ) : F := a.coeff (e - 1 - i)

/-- The coordinate maps of the Halton-type sequence in the bases `b_c`: digit `n = Q e_c + i` of coordinate
`c` is `[z^{e_c-1-i}] a_Q`, `a_Q` the `Q`-th `b_c`-adic digit. -/
noncomputable def haltonY (b : Fin s → F[X]) (c : Fin s) (V : F[X]) (n : ℕ) : F :=
  haltonPi (b c).natDegree (badicDigit (b c) V (n / (b c).natDegree)) (n % (b c).natDegree)

end Poly

section Pts
variable {s : ℕ}

/-- The index polynomial `V = ∑_k n_k z^k ∈ 𝔽_p[z]` of `n = ∑_k n_k p^k` (the body of the Palomar
statement's `idxPoly`). -/
noncomputable def idxPolyP (p n : ℕ) : Polynomial (ZMod p) :=
  ∑ k ∈ range (n + 1), Polynomial.monomial k (((n / p ^ k % p : ℕ) : ZMod p))

/-- The index `∑_k V_k.val p^k` of the polynomial `V` (`ι(V)` in `sec:prelim`). -/
noncomputable def polyIdx (p : ℕ) (V : Polynomial (ZMod p)) : ℕ :=
  ∑ k ∈ range (V.natDegree + 1), (V.coeff k).val * p ^ k

/-- The point with index `n` of the sequence with linear coordinates `Y_c`:
`y_c(n) = ∑_j Y_c(V)_j p^{-j-1}`, `V` the index polynomial of `n`. -/
noncomputable def linPt (p : ℕ) (Y : Fin s → Polynomial (ZMod p) → ℕ → ZMod p) (n : ℕ) : Fin s → ℝ :=
  fun c => ∑' j : ℕ, ((Y c (idxPolyP p n) j).val : ℝ) / (p : ℝ) ^ (j + 1)

/-- **The Halton-type sequence** in the bases `b_c` (GHS Def. 2; the body of the Palomar statement's
`haltonPt`): coordinate `c` of the point with index `n` is
`∑_Q ∑_{i<e_c} [z^{e_c-1-i}] a_Q · p^{-(Q e_c + i + 1)}`, `a_Q` the `b_c`-adic digits of `V(n)`. -/
noncomputable def haltonPt (p : ℕ) [Fact p.Prime] (b : Fin s → Polynomial (ZMod p)) (n : ℕ) :
    Fin s → ℝ :=
  fun c => ∑ Q ∈ range (n + 1), ∑ i ∈ range (b c).natDegree,
    (((badicDigit (b c) (idxPolyP p n) Q).coeff ((b c).natDegree - 1 - i)).val : ℝ) /
      (p : ℝ) ^ (Q * (b c).natDegree + i + 1)

end Pts

end GeoSeq
