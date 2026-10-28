/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Defs

@[expose] public section

/-!
# GeoSeq stage S7: definitions of the steering route (`sec:windows`, dimension two)

* `intWin p lo hi`: the integer interval `[lo, hi]` read modulo `p` (the windows of the paper).
* `Covers κ Wo Wx`: condition (ii) of `thm:GA`, `κ (Wo - 1) - Wx = 𝔽_p`.
* `RespIn C Wo Wx`: every one-digit response of the sequence `C` at every level lies in its window
  (own response `O_{c'}^{(l)} = D(l)[c'][c']` in `Wo c'`, cross response `X_{1-c'←c'}^{(l)}` in `Wx c'`).
* `GAbound p Wo Wx LB`: `LB` is at most each of the four numbers of `thm:GA` (in pointwise form:
  the minimum of `f_1(e, ·)²` over a window sum is a minimum over its elements).
* `faureZ p θ`: the scaled local roots `z_c(θx)` of the Faure frame `w = z² - z` (places `0, 1`),
  `z_{0,1} = (1 ∓ √(1 + 4θx))/2`.
* `g2b`, `g2A`: the parameters `b = ⌈√p⌉`, `A = b - 2 + ⌈(p-1)/b⌉` of `cor:G2`.
* The data of the brick hybrid (`thm:HB`): `hbNu`, `hbK`, `hbMA`, `hbMB` and the windows `hbWo`, `hbWx`.
* `hbCheck`: the reflected integer checker of `cor:HB17` (finite range).
-/

namespace GeoSeq

open Finset PowerSeries

/-- The integer interval `[lo, hi]` read in `ℤ/pℤ`. -/
def intWin (p : ℕ) (lo hi : ℤ) : Set (ZMod p) := {x | ∃ z : ℤ, lo ≤ z ∧ z ≤ hi ∧ (z : ZMod p) = x}

/-- Condition (ii) of `thm:GA`: `κ (W_o - 1) - W_x = 𝔽_p`. -/
def Covers {p : ℕ} (κ : ZMod p) (Wo Wx : Set (ZMod p)) : Prop :=
  ∀ β : ZMod p, ∃ o ∈ Wo, ∃ x ∈ Wx, κ * (o - 1) - x = β

/-- Every one-digit response of `C` (`j = 1`, every level `K`, carry length `1 ≤ l ≤ K`) lies in its
window: column `c'` has the own response `D(l)[c'][c'] ∈ Wo c'` and the cross response
`D(l)[1-c'][c'] ∈ Wx c'`. -/
def RespIn {p : ℕ} (C : Gen 2 (ZMod p)) (Wo Wx : Fin 2 → Set (ZMod p)) : Prop :=
  ∀ K l : ℕ, 1 ≤ l → l ≤ K → ∀ d : ZMod p,
    (IsCarryEntry C K 0 l 0 0 d → d ∈ Wo 0) ∧ (IsCarryEntry C K 0 l 1 0 d → d ∈ Wx 0) ∧
    (IsCarryEntry C K 0 l 1 1 d → d ∈ Wo 1) ∧ (IsCarryEntry C K 0 l 0 1 d → d ∈ Wx 1)

/-- `LB` is at most each of the four numbers of `thm:GA`:
`f_1(1,W_o^{(0)})² + f_1(0,W_x^{(0)})²`, `f_1(1,W_o^{(1)})² + f_1(0,W_x^{(1)})²`,
`f_1(1,W_o^{(0)}+W_x^{(1)})² + f_1(1,W_o^{(1)}+W_x^{(0)})²`,
`f_1(1,W_o^{(0)}-W_x^{(1)})² + f_1(1,W_o^{(1)}-W_x^{(0)})²` (square roots taken; the minimum over a
sumset of a sum of two independent terms is the sum of the minima, so the pointwise form below is
the paper's), with `f_1(e, σ) = gapNum1 p e σ / p`. -/
def GAbound (p : ℕ) [NeZero p] (Wo Wx : Fin 2 → Set (ZMod p)) (LB : ℝ) : Prop :=
  (∀ o ∈ Wo 0, ∀ x ∈ Wx 0,
    LB ≤ Real.sqrt (((gapNum1 p 1 o : ℝ) / p) ^ 2 + ((gapNum1 p 0 x : ℝ) / p) ^ 2)) ∧
  (∀ o ∈ Wo 1, ∀ x ∈ Wx 1,
    LB ≤ Real.sqrt (((gapNum1 p 1 o : ℝ) / p) ^ 2 + ((gapNum1 p 0 x : ℝ) / p) ^ 2)) ∧
  (∀ o0 ∈ Wo 0, ∀ x1 ∈ Wx 1, ∀ o1 ∈ Wo 1, ∀ x0 ∈ Wx 0,
    LB ≤ Real.sqrt (((gapNum1 p 1 (o0 + x1) : ℝ) / p) ^ 2 + ((gapNum1 p 1 (o1 + x0) : ℝ) / p) ^ 2)) ∧
  (∀ o0 ∈ Wo 0, ∀ x1 ∈ Wx 1, ∀ o1 ∈ Wo 1, ∀ x0 ∈ Wx 0,
    LB ≤ Real.sqrt (((gapNum1 p 1 (o0 - x1) : ℝ) / p) ^ 2 + ((gapNum1 p 1 (o1 - x0) : ℝ) / p) ^ 2))

/-- The scaled local roots of the Faure frame `w = z² - z` with scale `θ`:
`z_0(θx) = (1 - ρ)/2`, `z_1(θx) = (1 + ρ)/2`, `ρ = √(1 + 4θx)` (so `z_c² - z_c = θx`). -/
noncomputable def faureZ (p : ℕ) [Fact p.Prime] (θ : ZMod p) : Fin 2 → PowerSeries (ZMod p) :=
  wfZ (rhoWF p (4 * θ))

/-! ## The responses of one column in its free series (`lem:gform`, `eq:steer`) -/

/-- The own partial sum `O^{(l)} = [x^l] (1 - a z_1 k)/(1 - x)` of a column with free series `k`. -/
noncomputable def ownR {F : Type*} [Field F] (z1 : PowerSeries F) (a : F) (k : PowerSeries F)
    (l : ℕ) : F :=
  coeff l ((1 - C a * z1 * k) * PowerSeries.mk 1)

/-- The cross partial sum `X^{(l)} = [x^l] a' z_0 k/(1 - x)` of a column with free series `k`. -/
noncomputable def crossR {F : Type*} [Field F] (z0 : PowerSeries F) (a : F) (k : PowerSeries F)
    (l : ℕ) : F :=
  coeff l (C a * z0 * k * PowerSeries.mk 1)

/-! ## Square-root windows (`cor:G2`) -/

/-- `b = ⌈√p⌉` (`cor:G2`; the scale `θ = b`). -/
noncomputable def g2b (p : ℕ) : ℕ := ⌈Real.sqrt p⌉₊

/-- `A = b - 2 + ⌈(p-1)/b⌉` (`cor:G2`). -/
noncomputable def g2A (p : ℕ) : ℕ := g2b p - 2 + (p - 1 + g2b p - 1) / g2b p

/-! ## The brick hybrid (`thm:HB`) -/

/-- `ν = 2b + 1`. -/
def hbNu (b : ℕ) : ℕ := 2 * b + 1

/-- `k = 2 ν e²`. -/
def hbK (b e : ℕ) : ℕ := 2 * hbNu b * e ^ 2

/-- `M_A = ⌈(p-3)/ν⌉ + 3` (for `p ≥ 3`). -/
def hbMA (p b : ℕ) : ℕ := (p - 3 + hbNu b - 1) / hbNu b + 3

/-- `M_B = ⌈(p-1)/k⌉ - 1`. -/
def hbMB (p b e : ℕ) : ℕ := (p - 1 + hbK b e - 1) / hbK b e - 1

/-- The scale of the brick hybrid, `θ = ν e`. -/
def hbTheta (p b e : ℕ) : ZMod p := ((hbNu b * e : ℕ) : ZMod p)

/-- `κ_{0←1} = -k`. -/
def hbK01 (p b e : ℕ) : ZMod p := -((hbK b e : ℕ) : ZMod p)

/-- `κ_{1←0} = -ν/2`. -/
def hbK10 (p b : ℕ) : ZMod p := -((hbNu b : ℕ) : ZMod p) * (2 : ZMod p)⁻¹

/-- The own windows of the brick hybrid: `W_o^{(0)} = [-(k+M_A-1), -k]`, `W_o^{(1)} = [-(M_B-1), 0]`. -/
def hbWo (p b e : ℕ) : Fin 2 → Set (ZMod p) :=
  ![intWin p (-((hbK b e + hbMA p b : ℕ) - 1 : ℤ)) (-(hbK b e : ℤ)),
    intWin p (-((hbMB p b e : ℤ) - 1)) 0]

/-- The cross windows of the brick hybrid: `W_x^{(0)} = 1/2 + [-b, b]` (`1/2 = (p+1)/2`),
`W_x^{(1)} = [-k, k]`. -/
def hbWx (p b e : ℕ) : Fin 2 → Set (ZMod p) :=
  ![intWin p (((p + 1) / 2 : ℕ) - (b : ℤ)) (((p + 1) / 2 : ℕ) + (b : ℤ)),
    intWin p (-(hbK b e : ℤ)) (hbK b e)]

/-- `(LB^HB)²` of `thm:HB`:
`min((1 - (k+M_A)/p)² + ((p-3-2b)/(2p))², (1 - M_B/p)², (1 - (2k+M_A)/p)² + η²)`,
`η = (p - 1 - 2b - 2M_B)/(2p)`. -/
noncomputable def hbLB2 (p b e : ℕ) : ℝ :=
  min ((1 - ((hbK b e : ℝ) + hbMA p b) / p) ^ 2 + (((p : ℝ) - 3 - 2 * b) / (2 * p)) ^ 2)
    (min ((1 - (hbMB p b e : ℝ) / p) ^ 2)
      ((1 - (2 * (hbK b e : ℝ) + hbMA p b) / p) ^ 2 +
        (((p : ℝ) - 1 - 2 * b - 2 * hbMB p b e) / (2 * p)) ^ 2))

/-- The integer conditions of `cor:HB17` at one `p` (`e = 1`, `b = ⌊p/68⌋`): the side conditions of
`thm:HB` and `LB^HB ≥ 1 - 17/p` in squared integer form (`M_B ≤ 17` for the axis term of coordinate 1,
and `4(p-k-M_A)² + (p-3-2b)² ≥ 4(p-17)²`, `4(p-2k-M_A)² + (p-1-2b-2M_B)² ≥ 4(p-17)²`). -/
def hbOK (p : ℕ) : Bool :=
  let b := p / 68
  let k := hbK b 1
  let ma := hbMA p b
  let mb := hbMB p b 1
  decide (hbNu b < p) && decide (3 * k < p) && decide (2 * k + ma < p) &&
    decide (2 * b + 2 * mb + 1 < p) && decide (mb ≤ 17) && decide (17 < p) &&
    decide (4 * (p - 17) ^ 2 ≤ 4 * (p - k - ma) ^ 2 + (p - 3 - 2 * b) ^ 2) &&
    decide (4 * (p - 17) ^ 2 ≤ 4 * (p - 2 * k - ma) ^ 2 + (p - 1 - 2 * b - 2 * mb) ^ 2)

/-- The integer content of `hbOK`. -/
def HBConds (p : ℕ) : Prop :=
  hbNu (p / 68) < p ∧ 3 * hbK (p / 68) 1 < p ∧ 2 * hbK (p / 68) 1 + hbMA p (p / 68) < p ∧
    2 * (p / 68) + 2 * hbMB p (p / 68) 1 + 1 < p ∧ hbMB p (p / 68) 1 ≤ 17 ∧ 17 < p ∧
    4 * (p - 17) ^ 2 ≤ 4 * (p - hbK (p / 68) 1 - hbMA p (p / 68)) ^ 2 + (p - 3 - 2 * (p / 68)) ^ 2 ∧
    4 * (p - 17) ^ 2 ≤
      4 * (p - 2 * hbK (p / 68) 1 - hbMA p (p / 68)) ^ 2 + (p - 1 - 2 * (p / 68) - 2 * hbMB p (p / 68) 1) ^ 2

/-- `n` has a divisor `d` with `2 ≤ d < 20`. -/
def smallDiv (n : ℕ) : Bool := (List.range 18).any fun i => n % (i + 2) == 0

/-- The reflected checker of `cor:HB17` on `[lo, lo + cnt)`: every `n` passes `hbOK` or has a small
divisor (so it is not a prime `> 20`). -/
def hbCheck (lo : ℕ) : ℕ → Bool
  | 0 => true
  | cnt + 1 => (hbOK lo || smallDiv lo) && hbCheck (lo + 1) cnt

end GeoSeq
