/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.F4
public import GeoSeq.K4Defs

@[expose] public section

/-!
# GeoSeq stage S8: definitions for `thm:S4` (Artin–Schreier frame `H = 𝔽_4`, dimension `4`)

* `lem:frames`(a) for `H = 𝔽_4`: `U = ∑_{k≥0} x^{4^k}` (`U⁴ + U = x`), places `a_c ∈ {0, 1, ω, ω²}` (in
  the order of the codes), local roots `z_c = a_c + U` (`w = z⁴ + z`, `θ = 1`).
* `thm:S4`: `g = 1 + ωU + U²`, the generator matrices `S4gen`, the inverse frame matrix
  `S4G = T^{-1} A^{-1} g^{-1}` (`A[c][m] = a_c^m`, `T[m][b] = C(b,m) U^{b-m}`).
* The automaton of `prop:automaton` in the Artin–Schreier case `ϑ = U`, `A = 1`, `B = x`, `q = 4`:
  a state is a quadruple `(P_0, …, P_3)` standing for `x^{-5}(∑_k P_k U^k)/Q_p`,
  `Q_p = (ω² + x²)(1 + x)` (`ω² + x²` is the norm of `g`); with `U(x) = U(x⁴) + x` the Cartier step is
  `P ↦ Λ_r(x^{15} Q_p³ · (P_0 + xP_1 + x²P_2 + x³P_3, P_1 + x²P_3, P_2 + xP_3, P_3))` (`stepU`).
* Closed forms and the initial states of the pairs `(D_i(l), D_i(l-1))` (depth `j = 5`) of every
  source coordinate.
-/

namespace GeoSeq

open Finset PowerSeries

/-- `[x^n] U = 1` if `n` is a power of `4`, else `0` (`lem:frames`(a), `H = 𝔽_4`). -/
def u4c (n : ℕ) : F4 := if ∃ k < n + 1, 4 ^ k = n then 1 else 0

/-- **`thm:S4`**: `U = ∑_{k ≥ 0} x^{4^k} ∈ 𝔽_4[[x]]` (so `U⁴ + U = x`). -/
noncomputable def U4 : PowerSeries F4 := PowerSeries.mk u4c

/-- **`thm:S4`**: the multiplier `g = 1 + ωU + U²` (the same for every coordinate). -/
noncomputable def S4g : PowerSeries F4 := 1 + C F4.w * U4 + U4 ^ 2

/-- The places `a_c = 0, 1, ω, ω²` (`c = 0, 1, 2, 3`, the order of the codes). -/
def S4a (c : Fin 4) : F4 := f4dec c

/-- **`thm:S4`**: the local roots `z_c = a_c + U`. -/
noncomputable def S4z : Fin 4 → PowerSeries F4 := fun c => C (S4a c) + U4

/-- **`thm:S4`**: generator matrices `y_{c,n}(v) = [x^n] g(x) V(a_c + U(x))`, `a_c ∈ 𝔽_4`. -/
noncomputable def S4gen : Gen 4 F4 := ssGen (fun _ => S4g) S4z

/-- A state: numerators `(P_0, P_1, P_2, P_3)` of `x^{-5}(∑_k P_k U^k)/Q_p`. -/
abbrev StU := List F4 × List F4 × List F4 × List F4

/-- `∑_k P_k U^k` as a power series. -/
noncomputable def tsemU (S : StU) : PowerSeries F4 :=
  lps S.1 + lps S.2.1 * U4 + lps S.2.2.1 * U4 ^ 2 + lps S.2.2.2 * U4 ^ 3

/-- Numerators of the polynomial part `T^{-1} A^{-1}` of the inverse frame matrix. -/
def S4GpN : Fin 4 → Fin 4 → StU :=
  ![![([.e1], [], [], [.e1]), ([], [.e1], [.e1], [.e1]), ([], [.ew2], [.ew], [.e1]), ([], [.ew], [.ew2], [.e1])],
    ![([], [], [.e1], []), ([.e1], [], [.e1], []), ([.ew2], [], [.e1], []), ([.ew], [], [.e1], [])],
    ![([], [.e1], [], []), ([.e1], [.e1], [], []), ([.ew], [.e1], [], []), ([.ew2], [.e1], [], [])],
    ![([.e1], [], [], []), ([.e1], [], [], []), ([.e1], [], [], []), ([.e1], [], [], [])]]

/-- The inverse of the frame matrix of `thm:S4`: `G = T^{-1} A^{-1} g^{-1}`. -/
noncomputable def S4G : Matrix (Fin 4) (Fin 4) (PowerSeries F4) := fun b c' => tsemU (S4GpN b c') * S4g⁻¹

/-- A state stored as four natural numbers (base-4 digits). -/
def decSU (t : ℕ × ℕ × ℕ × ℕ) : StU := (n2p t.1, n2p t.2.1, n2p t.2.2.1, n2p t.2.2.2)

/-- A vector of states stored as natural numbers. -/
def decVU (L : List (ℕ × ℕ × ℕ × ℕ)) : List StU := L.map decSU

/-- `Q_p = (ω² + x²)(1 + x)`. -/
def QpU : List F4 := [.ew2, .ew2, .e1, .e1]

/-- `Q_p³`. -/
def Q3U : List F4 := [.e1, .e1, .ew2, .ew2, .e1, .e1, .ew, .ew, .e1, .e1]

/-- The power series `(∑_k P_k U^k) Q_p^{-1}`; coefficient `n + 5` of it is coefficient `n` of the
state. -/
noncomputable def esemU (S : StU) : PowerSeries F4 := tsemU S * (lps QpU)⁻¹

/-- The Cartier step `Λ_r` on numerators (`U(x) = U(x⁴) + x`, binomial coefficients mod `2`). -/
def stepU (r : ℕ) (S : StU) : StU :=
  (trim (ev4 r (pshift 15 (pmul (padd S.1 (padd (pmul [0, 1] S.2.1)
      (padd (pmul [0, 0, 1] S.2.2.1) (pmul [0, 0, 0, 1] S.2.2.2)))) Q3U))),
   trim (ev4 r (pshift 15 (pmul (padd S.2.1 (pmul [0, 0, 1] S.2.2.2)) Q3U))),
   trim (ev4 r (pshift 15 (pmul (padd S.2.2.1 (pmul [0, 1] S.2.2.2)) Q3U))),
   trim (ev4 r (pshift 15 (pmul S.2.2.2 Q3U))))

/-- `U, U², U³, Q_p^{-1}` to `x^5` (literal lists, checked in `GeoSeq/S4Auto.lean`). -/
def UL6 : List F4 := [0, 1, 0, 0, 1, 0]
/-- `U²` to `x^5`. -/
def U2L6 : List F4 := [0, 0, 1, 0, 0, 0]
/-- `U³` to `x^5`. -/
def U3L6 : List F4 := [0, 0, 0, 1, 0, 0]
/-- `Q_p^{-1}` to `x^5`. -/
def QiU6 : List F4 := [.ew, .ew, .e1, .e1, .e0, .e0]

/-- The readout `[x^0]` of a state (coefficient `5` of `esemU`). -/
def acoefU (S : StU) : F4 :=
  lget (tmul 6 (tadd 6 S.1 (tadd 6 (tmul 6 S.2.1 UL6) (tadd 6 (tmul 6 S.2.2.1 U2L6) (tmul 6 S.2.2.2 U3L6))))
    QiU6) 5

/-- The coefficients `n` of a vector of states. -/
noncomputable def valsU (V : List StU) (n : ℕ) : List F4 := V.map fun S => coeff (n + 5) (esemU S)

/-- One Cartier step on a vector of states. -/
def stepVU (r : ℕ) (V : List StU) : List StU := V.map (stepU r)

/-- Reading the base-4 digits of `n` (least significant first). -/
def readVU : List ℕ → List StU → List StU
  | [], V => V
  | r :: ds, V => readVU ds (stepVU r V)

/-- Numerators of `M[c][b] = g (a_c + U)^b` in the basis `{1, U, U², U³}` (`S4_M`). -/
def S4Mn : Fin 4 → Fin 4 → StU :=
  ![![([.e1], [.ew], [.e1], []), ([], [.e1], [.ew], [.e1]), ([.e0, .e1], [.e1], [.e1], [.ew]), ([.e0, .ew], [.ew, .e1], [.e1], [.e1])],
    ![([.e1], [.ew], [.e1], []), ([.e1], [.ew2], [.ew2], [.e1]), ([.e1, .e1], [.ew2], [], [.ew]), ([.e1, .ew2], [.e0, .e1], [.ew2], [.ew])],
    ![([.e1], [.ew], [.e1], []), ([.ew], [.ew], [], [.e1]), ([.ew2, .e1], [], [.ew], [.ew]), ([.e1], [.e1, .e1], [.ew2], [.e1])],
    ![([.e1], [.ew], [.e1], []), ([.ew2], [], [.e1], [.e1]), ([.ew, .e1], [.ew], [.ew2], [.ew]), ([.e1, .e1], [.e1, .e1], [], [.ew])]]

/-- Numerators of `Q_p Ĝ[b][c']` (`Ĝ = G/(1 - x)`; `S4_ghat`). -/
def S4An : Fin 4 → Fin 4 → StU :=
  ![![([.ew2, .e1, .ew], [.e0, .ew, .e1], [], [.ew2, .ew]), ([.e0, .e1, .ew2], [.ew, .ew2, .e1], [.ew, .e1], [.ew, .e1]), ([], [.ew, .ew2, .e1], [.e1, .ew2], [.ew2, .ew]), ([.e0, .ew, .e1], [.ew2, .e0, .e1], [.e1, .ew2], [.ew, .e1])],
    ![([.e0, .ew, .e1], [.ew, .e1], [.ew2, .ew], [.ew2, .ew]), ([.ew2, .e0, .e1], [.e1, .ew2], [.e1, .ew2], [.ew2, .ew]), ([.ew, .ew2, .e1], [], [.ew, .e1], [.ew2, .ew]), ([.e1, .e1, .e1], [.ew2, .ew], [], [.ew2, .ew])],
    ![([], [.ew2, .ew], [.ew2, .ew], [.ew, .e1]), ([.ew2, .ew], [], [.e1, .ew2], [.ew, .e1]), ([.e1, .ew2], [.ew, .e1], [], [.ew, .e1]), ([.ew, .e1], [.e1, .ew2], [.ew, .e1], [.ew, .e1])],
    ![([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []), ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []), ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], []), ([.ew2, .ew], [.ew2, .ew], [.ew, .e1], [])]]

/-- `U, U², U³` to `x^6` (for the coefficient table). -/
def UL7 : List F4 := [.e0, .e1, .e0, .e0, .e1, .e0, .e0]
/-- `U²` to `x^6`. -/
def U2L7 : List F4 := [.e0, .e0, .e1, .e0, .e0, .e0, .e0]
/-- `U³` to `x^6`. -/
def U3L7 : List F4 := [.e0, .e0, .e0, .e1, .e0, .e0, .e1]

/-- The truncated series `∑_k P_k U^k` to `x^6`. -/
def tsemLU (S : StU) : List F4 :=
  tadd 7 S.1 (tadd 7 (tmul 7 S.2.1 UL7) (tadd 7 (tmul 7 S.2.2.1 U2L7) (tmul 7 S.2.2.2 U3L7)))

/-- The coefficients `m_a[c][b] = [x^a] M[c][b]`, `a < 5` (computable). -/
def S4mtab (c b : Fin 4) (a : ℕ) : F4 := lget (tsemLU (S4Mn c b)) a

/-- `M_{≤ i}[c][b]` as a list. -/
def S4Mle (i : ℕ) (c b : Fin 4) : List F4 := (List.range (i + 1)).map (S4mtab c b)

/-- One numerator component of `Q_p (δ_{cc'}/(1-x) + ∑_b M_{≤ i}[c][b] Ĝ[b][c'])` (`-1 = 1`). -/
def initCU (i : ℕ) (c c' : Fin 4) (sel : StU → List F4) (δ : List F4) : List F4 :=
  padd δ (padd (pmul (S4Mle i c 0) (sel (S4An 0 c'))) (padd (pmul (S4Mle i c 1) (sel (S4An 1 c')))
    (padd (pmul (S4Mle i c 2) (sel (S4An 2 c'))) (pmul (S4Mle i c 3) (sel (S4An 3 c'))))))

/-- The initial state of entry `(c, c')`, depth `i < 5`, shifted by `x^{sh}`: numerators of
`x^{sh-i}(δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c'])` over `x^5 Q_p`. -/
def initSU (i : ℕ) (c c' : Fin 4) (sh : ℕ) : StU :=
  (trim (pshift (5 - i + sh) (initCU i c c' (·.1) (if c = c' then [.ew2, .e0, .e1] else []))),
   trim (pshift (5 - i + sh) (initCU i c c' (·.2.1) [])),
   trim (pshift (5 - i + sh) (initCU i c c' (·.2.2.1) [])),
   trim (pshift (5 - i + sh) (initCU i c c' (·.2.2.2) [])))

/-- The initial vector of source coordinate `c'`: entry `4i + c` is `initSU i c c' 0` (`D_i(l)[c][c']`),
entry `20 + 4i + c` is `initSU i c c' 1` (`D_i(l-1)[c][c']`). -/
def initVU (c' : Fin 4) : List StU :=
  (List.range 40).map fun k => initSU (k % 20 / 4) ⟨k % 4, Nat.mod_lt _ (by norm_num)⟩ c' (k / 20)

/-- The series `F_i[c][c'] = δ_{cc'}/(1-x) - ∑_b M_{≤ i}[c][b] Ĝ[b][c']` (written with `-1 = 1`). -/
noncomputable def S4F (i : ℕ) (c c' : Fin 4) : PowerSeries F4 :=
  (if c = c' then PowerSeries.mk 1 else 0) +
    ∑ b : Fin 4, (∑ a ∈ range (i + 1), C (coeff a (frameM (fun _ => S4g) S4z c b)) * X ^ a) *
      (S4G b c' * PowerSeries.mk 1)

/-- The carry responses of `thm:S4` with `D_i(0) = 0`. -/
noncomputable def S4Dr (i l : ℕ) (c c' : Fin 4) : F4 :=
  if l = 0 then 0 else lawD (fun _ => S4g) S4z S4G i l c c'

end GeoSeq
