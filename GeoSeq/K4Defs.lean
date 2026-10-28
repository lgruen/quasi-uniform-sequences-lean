/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.F4
public import GeoSeq.B3Defs

@[expose] public section

/-!
# GeoSeq stage S8: definitions for `thm:K4` (Kummer frame over `𝔽_4`)

* `lem:frames`(b) for `q = 4`: the Kummer root `T4 = τ^{-1} = ∏_{i≥0}(1 + x^{4^i})` by its digit rule
  (`[x^n] T4 = 1` iff every base-4 digit of `n` is `0` or `1`), and `τ = T4^{-1}`.
* `thm:K4`: `g = ω²(τ + ω)/(τ + ω²)`, places `ω^c`, roots `z_c = ω^c τ`, the generator matrices
  `K4gen`, and the inverse frame matrix `K4G` (`G[b][c'] = ω^{-bc'} τ^{-b} g^{-1}`).
* The automaton of `prop:automaton` in the Kummer case `ϑ = τ^{-1}`, `A = 1 + x`, `B = 0`, `q = 4`:
  a state is a triple of numerator polynomials `(P_0, P_1, P_2)` standing for the Laurent series
  `x^{-8}(P_0 + P_1 τ^{-1} + P_2 τ^{-2})/(1 + x²)`; its coefficient `n` is
  `[x^{n+8}] (P_0 + P_1 T4 + P_2 T4²)(1 + x²)^{-1}` (`esem4`). The Cartier step on numerators is
  `P_k ↦ Λ_r(x^{24} (1+x)^{6+k} P_k)` (`stepP4`).
* The closed forms of the frame matrix and of `Ĝ` in the basis `{1, τ^{-1}, τ^{-2}}`, and the initial
  states of the carry responses of source coordinate `0` (`initV4`; depth `j = 8`; the pairs
  `(D_i(l), D_i(l-1))` needed by the carry change of `eq:carrychange`).
* Polynomials of the certificate data are stored as natural numbers (base-4 digits, least
  significant first, decoded by `n2p`), which gives exactly the trimmed lists.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## The Kummer root over `𝔽_4` and the sequence of `thm:K4` -/

/-- The digit rule of `lem:frames`(b) for `q = 4`, with fuel: `1` if every base-4 digit of `n` is
`0` or `1`. -/
def t4cAux : ℕ → ℕ → F4
  | 0, _ => 1
  | f + 1, n => if n = 0 then 1 else if 2 ≤ n % 4 then 0 else t4cAux f (n / 4)

/-- `[x^n] τ^{-1}` over `𝔽_4` (`lem:frames`(b)). -/
def t4c (n : ℕ) : F4 := t4cAux n n

/-- The Kummer root `τ^{-1} = ∏_{i ≥ 0} (1 + x^{4^i}) ∈ 𝔽_4[[x]]` (`lem:frames`(b), `q = 4`). -/
noncomputable def T4 : PowerSeries F4 := PowerSeries.mk t4c

/-- **`thm:K4`**: `τ`, defined by `τ^{-1} = ∏_{i≥0}(1 + x^{4^i})` (so `τ³ = 1 + x`). -/
noncomputable def tau4 : PowerSeries F4 := T4⁻¹

/-- **`thm:K4`**: the multiplier `g = ω²(τ + ω)/(τ + ω²)` (the same for every coordinate). -/
noncomputable def K4g : PowerSeries F4 := C F4.w2 * (tau4 + C F4.w) * (tau4 + C F4.w2)⁻¹

/-- **`thm:K4`**: the local roots `z_c = ω^c τ` at the places `a_c = ω^c` (`w = z³ - 1`, `θ = 1`). -/
noncomputable def K4z : Fin 3 → PowerSeries F4 := fun c => C (wpn c) * tau4

/-- **`thm:K4`**: generator matrices `y_{c,n}(v) = [x^n] g(x) V(ω^c τ(x))`, `c = 0, 1, 2`. -/
noncomputable def K4gen : Gen 3 F4 := ssGen (fun _ => K4g) K4z

/-- The inverse of the frame matrix of `thm:K4`: `G[b][c'] = ω^{-bc'} τ^{-b} g^{-1}`
(`ω^{-1} = ω²`). -/
noncomputable def K4G : Matrix (Fin 3) (Fin 3) (PowerSeries F4) :=
  fun b c' => C (wpn (2 * b * c')) * T4 ^ (b : ℕ) * K4g⁻¹

/-! ## Polynomials, Cartier operator for `q = 4`, states -/

section Lists

variable {R : Type*} [CommRing R]

/-- The coefficients `k, k+4, k+8, …` of a list (the Cartier operator `Λ_k` on polynomials, `k < 4`). -/
def ev4 : ℕ → List R → List R
  | _, [] => []
  | 0, x :: r => x :: ev4 3 r
  | k + 1, _ :: r => ev4 k r

/-- The Cartier operator `Λ_r F = ∑_k [x^{4k+r}] F · x^k` (base `4`). -/
noncomputable def lam4 (r : ℕ) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k => coeff (4 * k + r) F

end Lists

/-- Decoding of a base-4 digit. -/
def n2f (n : ℕ) : F4 := if n = 0 then 0 else if n = 1 then 1 else if n = 2 then F4.w else F4.w2

/-- Decoding of a polynomial stored as a natural number (base-4 digits, least significant first). -/
def n2pAux : ℕ → ℕ → List F4
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n2f (n % 4) :: n2pAux f (n / 4)

/-- A polynomial stored as a natural number (at most `40` digits). -/
def n2p (n : ℕ) : List F4 := n2pAux 40 n

/-- A state: numerators `(P_0, P_1, P_2)` of `x^{-8}(P_0 + P_1 τ^{-1} + P_2 τ^{-2})/(1 + x²)`. -/
abbrev St4 := List F4 × List F4 × List F4

/-- A state stored as three natural numbers. -/
def decS (t : ℕ × ℕ × ℕ) : St4 := (n2p t.1, n2p t.2.1, n2p t.2.2)

/-- A vector of states stored as natural numbers. -/
def decV (L : List (ℕ × ℕ × ℕ)) : List St4 := L.map decS

/-- `1 + x²`, the part of the common denominator prime to `x`. -/
def Qp4 : List F4 := [1, 0, 1]

/-- `P_0 + P_1 τ^{-1} + P_2 τ^{-2}` as a power series. -/
noncomputable def tsem4 (S : St4) : PowerSeries F4 := lps S.1 + lps S.2.1 * T4 + lps S.2.2 * T4 ^ 2

/-- The power series `(P_0 + P_1 T4 + P_2 T4²)(1 + x²)^{-1}`; coefficient `n + 8` of it is
coefficient `n` of the state. -/
noncomputable def esem4 (S : St4) : PowerSeries F4 := tsem4 S * (lps Qp4)⁻¹

/-- `(1 + x)^6`, `(1 + x)^7`, `(1 + x)^8` (the factors `(1+x)^k (1+x²)³` of the Cartier step). -/
def W4 : ℕ → List F4
  | 0 => [1, 0, 1, 0, 1, 0, 1]
  | 1 => [1, 1, 1, 1, 1, 1, 1, 1]
  | _ => [1, 0, 0, 0, 0, 0, 0, 0, 1]

/-- The Cartier step `Λ_r` on numerators:
`P_k ↦ Λ_r(x^{24} (1+x)^k (1+x²)³ P_k)` (trimmed). -/
def stepP4 (r : ℕ) (S : St4) : St4 :=
  (trim (ev4 r (pshift 24 (pmul S.1 (W4 0)))), trim (ev4 r (pshift 24 (pmul S.2.1 (W4 1)))),
    trim (ev4 r (pshift 24 (pmul S.2.2 (W4 2)))))

/-- The first `D` coefficients of `τ^{-1}`. -/
def T4L (D : ℕ) : List F4 := (List.range D).map t4c

/-- `P_0 + P_1 τ^{-1} + P_2 τ^{-2}`, truncated to `D` coefficients. -/
def tsemL (D : ℕ) (S : St4) : List F4 :=
  tadd D S.1 (tadd D (tmul D S.2.1 (T4L D)) (tmul D S.2.2 (tmul D (T4L D) (T4L D))))

/-- Coefficient `n` (`n < D`) of `esem4 S`, computed with truncated series. -/
def acoefN4 (D : ℕ) (S : St4) (n : ℕ) : F4 := lget (tmul D (tsemL D S) (tinv D 1 Qp4)) n

/-- The readout `[x^0]` of a state (coefficient `8` of `esem4`). -/
def acoef4 (S : St4) : F4 := acoefN4 9 S 8

/-- The coefficients `n` of a vector of states. -/
noncomputable def vals4 (V : List St4) (n : ℕ) : List F4 := V.map fun S => coeff (n + 8) (esem4 S)

/-- One Cartier step on a vector of states. -/
def stepV4 (r : ℕ) (V : List St4) : List St4 := V.map (stepP4 r)

/-- Reading the base-4 digits of `n` (least significant first). -/
def readV4 : List ℕ → List St4 → List St4
  | [], V => V
  | r :: ds, V => readV4 ds (stepV4 r V)

/-! ## Closed forms and initial states (source coordinate `0`, depth `j = 8`) -/

/-- Numerators of `x g τ^b` in the basis `{1, τ^{-1}, τ^{-2}}` (`K4_M`). -/
def K4Mn : Fin 3 → St4 :=
  ![([.e1, .ew2], [.ew2, .ew2], [.ew, .ew]),
    ([.ew2, .ew2], [.ew, .ew], [.e1, .ew, .ew2]),
    ([.ew, .ew], [.e1, .ew, .ew2], [.ew2, .e0, .ew2])]

/-- Numerators of `x (1 + x²) Ĝ[b][0]` (`Ĝ = G/(1 - x)`; `K4_ghat`). -/
def K4An : Fin 3 → St4 :=
  ![([.e1, .ew2, .ew], [.ew, .e0, .ew], [.ew2, .e0, .ew2]),
    ([.ew2, .ew2], [.e1, .ew2, .ew], [.ew, .e0, .ew]),
    ([.ew, .ew], [.ew2, .ew2], [.e1, .ew2, .ew])]

/-- The coefficients `m_a[c][b] = [x^a] M[c][b] = ω^{cb} [x^{a+1}] (x g τ^b)`, `a < 8` (computable). -/
def K4mtab (c b : Fin 3) (a : ℕ) : F4 := wpn ((c : ℕ) * b) * lget (tsemL 9 (K4Mn b)) (a + 1)

/-- `M_{≤ i}[c][b] = ∑_{a ≤ i} m_a[c][b] x^a` as a list. -/
def K4Mle (i : ℕ) (c b : Fin 3) : List F4 := (List.range (i + 1)).map (K4mtab c b)

/-- One numerator component of `x (1+x²)(δ_{c0}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][0])` (`-1 = 1`). -/
def initC (i : ℕ) (c : Fin 3) (sel : St4 → List F4) (δ : List F4) : List F4 :=
  padd δ (padd (pmul (K4Mle i c 0) (sel (K4An 0)))
    (padd (pmul (K4Mle i c 1) (sel (K4An 1))) (pmul (K4Mle i c 2) (sel (K4An 2)))))

/-- The initial state of entry `(c, 0)`, depth `i < 8`, shifted by `x^{sh}`: numerators of
`x^{sh-i}(δ_{c0}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][0])` over `x^8 (1 + x²)`. -/
def initS4 (i : ℕ) (c : Fin 3) (sh : ℕ) : St4 :=
  (trim (pshift (7 - i + sh) (initC i c (·.1) (if c = 0 then [0, 1, 1] else []))),
   trim (pshift (7 - i + sh) (initC i c (·.2.1) [])),
   trim (pshift (7 - i + sh) (initC i c (·.2.2) [])))

/-- The initial vector of source coordinate `0`: entry `3i + c` is `initS4 i c 0` (the response
`D_i(l)[c][0]`), entry `24 + 3i + c` is `initS4 i c 1` (the previous response `D_i(l-1)[c][0]`). -/
def initV4 : List St4 :=
  (List.range 48).map fun k => initS4 (k % 24 / 3) ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ (k / 24)

/-- The series `F_i[c][c'] = δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c']` (written with `-1 = 1`). -/
noncomputable def K4F (i : ℕ) (c c' : Fin 3) : PowerSeries F4 :=
  (if c = c' then PowerSeries.mk 1 else 0) +
    ∑ b : Fin 3, (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => K4g) K4z c b)) * X ^ a) *
      (K4G b c' * PowerSeries.mk 1)

/-- The carry responses of `thm:K4` with `D_i(0) = 0` (the convention of `sec:law`). -/
noncomputable def K4Dr (i l : ℕ) (c c' : Fin 3) : F4 :=
  if l = 0 then 0 else lawD (fun _ => K4g) K4z K4G i l c c'

end GeoSeq
