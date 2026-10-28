/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V93Defs

@[expose] public section

/-!
# GeoSeq stage V9-5 (paper V4, `sec:fail`): definitions for the corollaries of `thm:nonqu`

Shared by the statement file `GeoSeq/Statements/V95.lean` and the proof files `GeoSeq/V95*.lean`. Prime base
`q = p` (the framework of stage V9-3: linear coordinates `Y_c : 𝔽_p[z] → (ℕ → 𝔽_p)`, points `linPt`).

* `genY`: the linear coordinate of a generator matrix, `Y_c(V)_n = ∑_k C_c[n][k] V_k` (so that
  `seqPoint (zcode p) C = linPt p (genY C)`, `seqPoint_eq_linPt`).
* `scrY`: a lower-triangular scramble `L` of a coordinate, `(LY)(V)_n = ∑_{j ≤ n} L[n][j] Y(V)_j`
  (`cor:unscrambled`).
* **Sobol' sequences** (`eq:sobrec`, `lem:sobol`, `cor:sobol`; base `2`): the binary digit `bitZ x j ∈ 𝔽_2` of
  `x ∈ ℕ`, the XOR of a finite family `xorSum`, admissible direction numbers satisfying Sobol's recurrence
  (`IsSobolDir b u`: `u_k` odd and `< 2^k` for `k ≤ e`, and `u_k = 2α_1u_{k-1} ⊕ … ⊕ 2^{e-1}α_{e-1}u_{k-e+1} ⊕
  2^e u_{k-e} ⊕ u_{k-e}` for `k > e`, where `b = z^e + α_1 z^{e-1} + … + α_{e-1} z + 1`), and the generator
  matrices `sobolGen u` (column `k - 1` holds the binary digits of `2^{-k} u_k`: `C[n][k-1] = bit_{k-1-n}(u_k)` for
  `n ≤ k - 1`). The Gray code `gray n = n XOR ⌊n/2⌋`.
* **Niederreiter sequences** (`lem:nied`, `cor:nied`): for a monic `b` of degree `e`,
  `[z^{-1}] ϑ V / b^{Q+1}` is the coefficient of `z^{(Q+1)e - 1}` in `ϑ V mod b^{Q+1}` (the polynomial part has no
  `z^{-1}` term; `R / b^{Q+1}` with `deg R < (Q+1)e` has `z^{-1}`-coefficient `[z^{(Q+1)e-1}] R`) — `niedDigit`;
  the coordinate `niedY b ϑ` (digit `Qe + i` is `[z^{-1}] ϑ_{Q,i} V / b^{Q+1}`) and its digit map `niedPi`
  (`π(a)_i = [z^{-1}] ϑ̄_i a / b`).
* **`rem:faurerate`**: the difference `faureD` and the lower point `faureV1` of the pair, in `Y = z - a_ĉ`.
-/

namespace GeoSeq

open Finset Polynomial

section Gen
variable {F : Type*} [Field F] {s : ℕ}

/-- The linear coordinate `c` of the generator matrices `C`: `Y_c(V)_n = ∑_k C_c[n][k] V_k`. -/
noncomputable def genY (C : Gen s F) (c : Fin s) (V : F[X]) (n : ℕ) : F := V.sum fun k a => C c n k * a

/-- A lower-triangular scramble `L` of the coordinate `Y`: `(LY)(V)_n = ∑_{j ≤ n} L[n][j] Y(V)_j`. -/
def scrY (L : ℕ → ℕ → F) (Y : F[X] → ℕ → F) (V : F[X]) (n : ℕ) : F :=
  ∑ j ∈ range (n + 1), L n j * Y V j

end Gen

section Sobol
variable {s : ℕ}

/-- The binary digit `j` of `x ∈ ℕ` as an element of `𝔽_2`. -/
def bitZ (x j : ℕ) : ZMod 2 := if x.testBit j then 1 else 0

/-- The XOR `f(0) ⊕ f(1) ⊕ ⋯ ⊕ f(n-1)` of binary expansions. -/
def xorSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => xorSum f n ^^^ f n

/-- **Admissible Sobol' direction numbers** for `b = z^e + α_1 z^{e-1} + ⋯ + α_{e-1} z + 1` (`eq:sobrec`): `u_k` is
odd and `u_k < 2^k` for `1 ≤ k ≤ e`, and for `k > e`
`u_k = 2α_1u_{k-1} ⊕ 2²α_2u_{k-2} ⊕ ⋯ ⊕ 2^{e-1}α_{e-1}u_{k-e+1} ⊕ 2^e u_{k-e} ⊕ u_{k-e}` (`α_i = [z^{e-i}] b`). -/
def IsSobolDir (b : (ZMod 2)[X]) (u : ℕ → ℕ) : Prop :=
  (∀ k, 1 ≤ k → k ≤ b.natDegree → u k % 2 = 1 ∧ u k < 2 ^ k) ∧
    ∀ k, b.natDegree < k →
      u k = xorSum (fun i => if i ≠ 0 ∧ b.coeff (b.natDegree - i) = 1 then 2 ^ i * u (k - i) else 0)
          b.natDegree ^^^ 2 ^ b.natDegree * u (k - b.natDegree) ^^^ u (k - b.natDegree)

/-- **The Sobol' generator matrices** (`sec:fail`, Sobol' sequences): column `k - 1` of `C_c` holds the binary
digits of `2^{-k} u_{c,k}`, i.e. `C_c[n][k-1] = bit_{k-1-n}(u_{c,k})` for `n ≤ k - 1` and `0` below. -/
def sobolGen (u : Fin s → ℕ → ℕ) : Gen s (ZMod 2) :=
  fun c n j => if n ≤ j then bitZ (u c (j + 1)) (j - n) else 0

/-- The column `j` of a Sobol' generator matrix: `C[n][j] = bit_{j-n}(u_{j+1})` for `n ≤ j`. -/
def scol (u : ℕ → ℕ) (n j : ℕ) : ZMod 2 := if n ≤ j then bitZ (u (j + 1)) (j - n) else 0

/-- The Sobol' coordinate as a linear coordinate: `Y(V)_n = ∑_j C[n][j] V_j`. -/
noncomputable def sobY (u : ℕ → ℕ) (V : (ZMod 2)[X]) (n : ℕ) : ZMod 2 := V.sum fun j a => scol u n j * a

/-- The admissible coordinates of a Sobol' sequence: the van der Corput coordinate (`b = z`, `u_k = 1`) or a
coordinate whose polynomial (degree `≥ 1`) has constant term `1`, with admissible direction numbers. -/
def SobolCoord (b : (ZMod 2)[X]) (u : ℕ → ℕ) : Prop :=
  (b = X ∧ ∀ k, 1 ≤ k → u k = 1) ∨ (1 ≤ b.natDegree ∧ b.coeff 0 = 1 ∧ IsSobolDir b u)

/-- The Gray code `n ↦ n XOR ⌊n/2⌋` (Antonov–Saleev order). -/
def gray (n : ℕ) : ℕ := n ^^^ (n / 2)

end Sobol

section Nied
variable {F : Type*} [Field F]

/-- `[z^{-1}] ϑ V / b^{Q+1}` for monic `b` of degree `e`: the coefficient of `z^{(Q+1)e - 1}` in `ϑ V mod b^{Q+1}`. -/
noncomputable def niedDigit (b ϑ V : F[X]) (Q : ℕ) : F :=
  ((ϑ * V) %ₘ b ^ (Q + 1)).coeff ((Q + 1) * b.natDegree - 1)

/-- **The Niederreiter coordinate** (generalized, Tezuka; `sec:fail`): digit `Q e + i` (`i < e = deg b`) is
`[z^{-1}] ϑ_{Q,i} V / b^{Q+1}`. The classical sequence has `ϑ_{Q,i} = z^i`. -/
noncomputable def niedY (b : F[X]) (ϑ : ℕ → ℕ → F[X]) (V : F[X]) (n : ℕ) : F :=
  niedDigit b (ϑ (n / b.natDegree) (n % b.natDegree)) V (n / b.natDegree)

/-- The digit map of `lem:nied`: `π(a)_i = [z^{-1}] ϑ̄_i a / b`, `ϑ̄_i = ϑ_{0,i}` (only `ϑ_{0,i} mod b` matters). -/
noncomputable def niedPi (b : F[X]) (ϑ0 : ℕ → F[X]) (a : F[X]) (i : ℕ) : F :=
  ((ϑ0 i * a) %ₘ b).coeff (b.natDegree - 1)

end Nied

section FaureRate
variable {p : ℕ} {s : ℕ}

/-- `rem:faurerate`: `D = -γ^{-1} (Y - 1)^{Q-1} ∏_{c ≠ ĉ, c₁} (Y - δ_c)^Q`, `Y = z - a_ĉ`, `δ_c = a_c - a_ĉ`,
`γ = ∏_{c ≠ ĉ} (-δ_c)`. -/
noncomputable def faureD (a : Fin s → ZMod p) (ch c1 : Fin s) (Q : ℕ) : (ZMod p)[X] :=
  -C (∏ c ∈ univ.erase ch, -(a c - a ch))⁻¹ * (X - C (a ch) - 1) ^ (Q - 1) *
    ∏ c ∈ (univ.erase ch).erase c1, (X - C (a ch) - C (a c - a ch)) ^ Q

/-- `rem:faurerate`: `V_1 = -(Y + Y² + ⋯ + Y^{Q-1})`, `Y = z - a_ĉ`. -/
noncomputable def faureV1 (a : Fin s → ZMod p) (ch : Fin s) (Q : ℕ) : (ZMod p)[X] :=
  -∑ j ∈ Finset.Ico 1 Q, (X - C (a ch)) ^ j

end FaureRate

section Scr
variable {p : ℕ} {s : ℕ}

/-- The scrambled frame of `cor:unscrambled`: `C_ĉ = μ diag(β^n) P_{a_ĉ}`, `C_c = L_c P_{a_c}` (`c ≠ ĉ`). -/
def scrFrame (a : Fin s → ZMod p) (ch : Fin s) (μ β : ZMod p) (L : Fin s → ℕ → ℕ → ZMod p) :
    Gen s (ZMod p) :=
  fun c n k => if c = ch then μ * β ^ n * pas (a ch) n k else ∑ j ∈ range (n + 1), L c n j * pas (a c) j k

end Scr

end GeoSeq
