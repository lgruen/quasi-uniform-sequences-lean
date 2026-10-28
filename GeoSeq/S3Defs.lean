/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.B3Defs

@[expose] public section

/-!
# GeoSeq stage S8: definitions for `thm:S3` (Artin–Schreier frame `H = 𝔽_3`, dimension `3`)

* `lem:frames`(a) for `H = 𝔽_3`: the series `U = -∑_{k≥0} x^{3^k}` (`U³ - U = x`), local roots
  `z_c = c + U` at the places `c ∈ 𝔽_3` (`w = z³ - z`, `θ = 1`).
* `thm:S3`: `g = (1 + x - U)/(1 - x)`, the generator matrices `S3gen`, and the inverse frame matrix
  `S3G = T^{-1} A^{-1} g^{-1}` (`M = diag(g) A T`, `A[c][m] = c^m`, `T[m][b] = C(b,m) U^{b-m}`).
* The automaton of `prop:automaton` in the Artin–Schreier case `ϑ = U`, `A = 1`, `B = -x`, `q = 3`:
  a state is a triple `(P_0, P_1, P_2)` standing for `x^{-8}(P_0 + P_1 U + P_2 U²)/Q_p`,
  `Q_p = (1 + x²)(1 - x)`; its coefficient `n` is `[x^{n+8}] (P_0 + P_1 U + P_2 U²) Q_p^{-1}` (`esemS`).
  With `U(x) = U(x³) - x` the Cartier step mixes the components by binomial coefficients:
  `(P_0, P_1, P_2) ↦ Λ_r(x^{16} Q_p² · (P_0 - x P_1 + x² P_2, P_1 - 2x P_2, P_2))` (`stepS`).
* Closed forms and the initial states of the carry responses of every source coordinate (depth
  `j = 8`).
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## The Artin–Schreier root over `𝔽_3` and the sequence of `thm:S3` -/

/-- `[x^n] U = -1 = 2` if `n` is a power of `3`, else `0` (`lem:frames`(a), `H = 𝔽_3`). -/
def u3c (n : ℕ) : ZMod 3 := if ∃ k < n + 1, 3 ^ k = n then 2 else 0

/-- **`thm:S3`**: `U = -∑_{k ≥ 0} x^{3^k} ∈ 𝔽_3[[x]]` (so `U³ - U = x`). -/
noncomputable def U3 : PowerSeries (ZMod 3) := PowerSeries.mk u3c

/-- **`thm:S3`**: the multiplier `g = (1 + x - U)/(1 - x)` (the same for every coordinate). -/
noncomputable def S3g : PowerSeries (ZMod 3) := (1 + X - U3) * (1 - X)⁻¹

/-- **`thm:S3`**: the local roots `z_c = c + U` at the places `c ∈ {0, 1, 2} = 𝔽_3`. -/
noncomputable def S3z : Fin 3 → PowerSeries (ZMod 3) := fun c => C ((c : ℕ) : ZMod 3) + U3

/-- **`thm:S3`**: generator matrices `y_{c,n}(v) = [x^n] g(x) V(c + U(x))`, `c ∈ 𝔽_3`. -/
noncomputable def S3gen : Gen 3 (ZMod 3) := ssGen (fun _ => S3g) S3z

/-- The polynomial part `T^{-1} A^{-1}` of the inverse frame matrix (`-1 = 2`). -/
noncomputable def S3Gp : Matrix (Fin 3) (Fin 3) (PowerSeries (ZMod 3)) :=
  !![1 + 2 * U3 ^ 2, U3 + 2 * U3 ^ 2, 2 * U3 + 2 * U3 ^ 2;
     2 * U3, 2 + 2 * U3, 1 + 2 * U3;
     2, 2, 2]

/-- The inverse of the frame matrix of `thm:S3`: `G = T^{-1} A^{-1} g^{-1}`. -/
noncomputable def S3G : Matrix (Fin 3) (Fin 3) (PowerSeries (ZMod 3)) :=
  fun b c' => S3Gp b c' * S3g⁻¹

/-! ## States of the automaton -/

/-- A state: numerators `(P_0, P_1, P_2)` of `x^{-8}(P_0 + P_1 U + P_2 U²)/Q_p`. -/
abbrev StS := List (ZMod 3) × List (ZMod 3) × List (ZMod 3)

/-- Decoding of a polynomial over `𝔽_3` stored as a natural number (base-3 digits, least significant
first, at most `40` digits). -/
def n2p3Aux : ℕ → ℕ → List (ZMod 3)
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else ((n % 3 : ℕ) : ZMod 3) :: n2p3Aux f (n / 3)

/-- A polynomial over `𝔽_3` stored as a natural number. -/
def n2p3 (n : ℕ) : List (ZMod 3) := n2p3Aux 40 n

/-- A state stored as three natural numbers. -/
def decS3 (t : ℕ × ℕ × ℕ) : StS := (n2p3 t.1, n2p3 t.2.1, n2p3 t.2.2)

/-- A vector of states stored as natural numbers. -/
def decV3 (L : List (ℕ × ℕ × ℕ)) : List StS := L.map decS3

/-- `Q_p = (1 + x²)(1 - x) = 1 + 2x + x² + 2x³`. -/
def QpS : List (ZMod 3) := [1, 2, 1, 2]

/-- `Q_p²`. -/
def QQS : List (ZMod 3) := [1, 1, 0, 2, 0, 1, 1]

/-- `P_0 + P_1 U + P_2 U²` as a power series. -/
noncomputable def tsemS (S : StS) : PowerSeries (ZMod 3) := lps S.1 + lps S.2.1 * U3 + lps S.2.2 * U3 ^ 2

/-- The power series `(P_0 + P_1 U + P_2 U²) Q_p^{-1}`; coefficient `n + 8` of it is coefficient `n`
of the state. -/
noncomputable def esemS (S : StS) : PowerSeries (ZMod 3) := tsemS S * (lps QpS)⁻¹

/-- The Cartier step `Λ_r` on numerators (`U(x) = U(x³) - x`):
`(P_0, P_1, P_2) ↦ Λ_r(x^{16} Q_p² (P_0 + 2x P_1 + x² P_2, P_1 + x P_2, P_2))` (trimmed). -/
def stepS (r : ℕ) (S : StS) : StS :=
  (trim (ev3 r (pshift 16 (pmul (padd S.1 (padd (pmul [0, 2] S.2.1) (pmul [0, 0, 1] S.2.2))) QQS))),
   trim (ev3 r (pshift 16 (pmul (padd S.2.1 (pmul [0, 1] S.2.2)) QQS))),
   trim (ev3 r (pshift 16 (pmul S.2.2 QQS))))

/-- The first `D` coefficients of `U`. -/
def UL3 (D : ℕ) : List (ZMod 3) := (List.range D).map u3c

/-- `P_0 + P_1 U + P_2 U²`, truncated to `D` coefficients. -/
def tsemLS (D : ℕ) (S : StS) : List (ZMod 3) :=
  tadd D S.1 (tadd D (tmul D S.2.1 (UL3 D)) (tmul D S.2.2 (tmul D (UL3 D) (UL3 D))))

/-- Coefficient `n` (`n < D`) of `esemS S`, computed with truncated series. -/
def acoefNS (D : ℕ) (S : StS) (n : ℕ) : ZMod 3 := lget (tmul D (tsemLS D S) (tinv D 1 QpS)) n

/-- `U`, `U²` and `Q_p^{-1}` to `x^8` (literal lists; checked against `UL3`, `tmul`, `tinv`). -/
def UL9 : List (ZMod 3) := [0, 2, 0, 2, 0, 0, 0, 0, 0]
/-- `U²` to `x^8`. -/
def U2L9 : List (ZMod 3) := [0, 0, 1, 0, 2, 0, 1, 0, 0]
/-- `Q_p^{-1}` to `x^8`. -/
def QiS9 : List (ZMod 3) := [1, 1, 0, 0, 1, 1, 0, 0, 1]

/-- The readout `[x^0]` of a state (coefficient `8` of `esemS`). -/
def acoefS (S : StS) : ZMod 3 :=
  lget (tmul 9 (tadd 9 S.1 (tadd 9 (tmul 9 S.2.1 UL9) (tmul 9 S.2.2 U2L9))) QiS9) 8

/-- The coefficients `n` of a vector of states. -/
noncomputable def valsS (V : List StS) (n : ℕ) : List (ZMod 3) :=
  V.map fun S => coeff (n + 8) (esemS S)

/-- One Cartier step on a vector of states. -/
def stepVS (r : ℕ) (V : List StS) : List StS := V.map (stepS r)

/-- Reading the base-3 digits of `n` (least significant first). -/
def readVS : List ℕ → List StS → List StS
  | [], V => V
  | r :: ds, V => readVS ds (stepVS r V)

/-! ## Closed forms and initial states (depth `j = 8`) -/

/-- Numerators of `(1 - x) M[c][b] = (1 + x - U)(c + U)^b` in the basis `{1, U, U²}` (`S3_M`). -/
def S3Mn : Fin 3 → Fin 3 → StS :=
  ![![([1, 1], [2], []), ([], [1, 1], [2]), ([0, 2], [2], [1, 1])],
    ![([1, 1], [2], []), ([1, 1], [0, 1], [2]), ([1], [0, 2], [2, 1])],
    ![([1, 1], [2], []), ([2, 2], [2, 1], [2]), ([1], [2, 1], [0, 1])]]

/-- Numerators of `x Q_p Ĝ[b][c']` (`Ĝ = G/(1 - x)`; `S3_ghat`). -/
def S3An : Fin 3 → Fin 3 → StS :=
  ![![([0, 1, 2], [0, 2, 1], [0, 1, 1, 1]), ([0, 0, 2, 1], [0, 0, 1, 2], [0, 2, 0, 1]),
      ([0, 1, 1, 1], [1, 1, 0, 1], [1, 2, 2, 1])],
    ![([0, 2, 1], [2, 2, 1, 1], [2, 0, 1]), ([0, 0, 2, 1], [1, 2, 2, 1], [1, 1, 1]),
      ([0, 1, 0, 2], [0, 2, 0, 1], [0, 2, 1])],
    ![([0, 1, 1, 1], [2, 0, 1], [2, 1]), ([0, 1, 1, 1], [2, 0, 1], [2, 1]),
      ([0, 1, 1, 1], [2, 0, 1], [2, 1])]]

/-- The coefficients `m_a[c][b] = [x^a] M[c][b] = ∑_{n ≤ a} [x^n] (1 - x) M[c][b]`, `a < 8`. -/
def S3mtab (c b : Fin 3) (a : ℕ) : ZMod 3 := lget (tmul 9 (tsemLS 9 (S3Mn c b)) (List.replicate 9 1)) a

/-- `M_{≤ i}[c][b] = ∑_{a ≤ i} m_a[c][b] x^a` as a list. -/
def S3Mle (i : ℕ) (c b : Fin 3) : List (ZMod 3) := (List.range (i + 1)).map (S3mtab c b)

/-- One numerator component of `x Q_p (δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c'])` (`-1 = 2`). -/
def initCS (i : ℕ) (c c' : Fin 3) (sel : StS → List (ZMod 3)) (δ : List (ZMod 3)) : List (ZMod 3) :=
  padd δ ((padd (pmul (S3Mle i c 0) (sel (S3An 0 c')))
    (padd (pmul (S3Mle i c 1) (sel (S3An 1 c'))) (pmul (S3Mle i c 2) (sel (S3An 2 c'))))).map (2 * ·))

/-- The initial state of entry `(c, c')`, depth `i < 8`: numerators of
`x^{-i}(δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c'])` over `x^8 Q_p`. -/
def initSS (i : ℕ) (c c' : Fin 3) : StS :=
  (trim (pshift (7 - i) (initCS i c c' (·.1) (if c = c' then [0, 1, 0, 1] else []))),
   trim (pshift (7 - i) (initCS i c c' (·.2.1) [])),
   trim (pshift (7 - i) (initCS i c c' (·.2.2) [])))

/-- The initial vector of source coordinate `c'`: entry `3i + c` is `initSS i c c'`. -/
def initVS (c' : Fin 3) : List StS :=
  (List.range 24).map fun k => initSS (k / 3) ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ c'

/-- The series `F_i[c][c'] = δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c']` (written with `-1 = 2`). -/
noncomputable def S3F (i : ℕ) (c c' : Fin 3) : PowerSeries (ZMod 3) :=
  (if c = c' then PowerSeries.mk 1 else 0) +
    2 * ∑ b : Fin 3, (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S3g) S3z c b)) * X ^ a) *
      (S3G b c' * PowerSeries.mk 1)

/-! ## Digit vectors over `𝔽_3` as words (base-3 integers `enc σ`) -/

/-- Digitwise addition in `𝔽_3` of two `j`-digit base-3 words (leading digit first). -/
def add3W : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | j + 1, a, b => ((a / 3 ^ j + b / 3 ^ j) % 3) * 3 ^ j + add3W j (a % 3 ^ j) (b % 3 ^ j)

/-- Digitwise negation in `𝔽_3` of a `j`-digit base-3 word. -/
def neg3W : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, a => ((3 - a / 3 ^ j % 3) % 3) * 3 ^ j + neg3W j (a % 3 ^ j)

/-- The bound of `B3Cert.top3` on words: for the leading nonzero digit `d` of `w` (with the word `ρ` of
the `k` digits after it), `3^k - enc(-ρ)` if `d = 1` and `3^k - enc(ρ)` if `d = 2`; `0` for `w = 0`. -/
def top3W : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, w => if w / 3 ^ j % 3 = 0 then top3W j (w % 3 ^ j)
      else if w / 3 ^ j % 3 = 1 then 3 ^ j - neg3W j (w % 3 ^ j) else 3 ^ j - w % 3 ^ j

end GeoSeq
