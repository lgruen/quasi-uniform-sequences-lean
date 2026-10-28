/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SteerDefs

@[expose] public section

/-!
# GeoSeq stage S9: definitions for `thm:L3` (`sec:windows`, dimension three)

* `cubeApprox`, `cubeRt a`: the cube root of a power series `a` with `a(0) = 1` (characteristic `≠ 3`),
  built coefficient by coefficient (the limit of the approximations `cubeApprox a n`).
* `kumTau p θ = (1 + θx)^{1/3}`, `kumZ p ζ θ c = ζ^c τ`: the scaled local roots of the Kummer frame
  `(1, ζ, ζ²; ∞)`, `w = z³ - 1` (`z_c³ - 1 = θx`, `z_c(0) = ζ^c`); `kumGen p ζ θ g`: the symmetric
  self-similar scramble with the multiplier `g` in all three coordinates.
* `kumU ζ θ d = θ/(3(1 - ζ^d))`: the depth direction `u_d` of `eq:steer3`.
* `sig`, `kresp`: the one-digit responses in the free series `k = 1/g` (formal proof of `prop:cover3`).
* `Covers3 u₁ u₂ W`: condition (ii) of `prop:cover3` (every line `β + 𝔽_p (1, u₁, u₂)` meets
  `W 0 × W 1 × W 2`); `RespIn3 C W`: every one-digit response `D(l)[c][c']` lies in `W (c - c')`
  (`W 0` = own window); `C3bound p W LB`: `LB` is below the certificate value `LB(W_o, W_1, W_2)` of
  `prop:cover3` (pointwise form: for every step and every choice of the responses in their windows).
* `prodWin`, `prodLB`: the interval windows and the value `LB_D` of `lem:prodbound`.
* The rule `R_p` (`thm:L3`): `cenAbs`, `cenInt` (representatives in `(-p/2, p/2)`), `l3Nst` (`n*`),
  `l3Bs` (`b_sweep`), `l3Aw` (`A`), `l3Cond` (side conditions), `l3LBD` (`LB_D` of a candidate, `0` if
  the side conditions fail), `l3Y2`, `l3Nu` (the pair `(ν_wrap, ν_sweep)` of the candidate `(y₁, wrap)`),
  `l3Val`, `l3Theta`, `l3Win`; `l3F` (`F(p)`).
* The reflected checker of the finite range `97 ≤ p < 2·10^5`: `l3SmallPrimes`, `hasDiv`, `l3NumOK`,
  `certOK`, `l3Check`.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Cube roots of power series -/

/-- The approximations of the cube root of `a`: `approx 0 = 1`, and step `n + 1` corrects the coefficient
`n + 1` by `[x^{n+1}](a - approx_n³)/3`. -/
noncomputable def cubeApprox {F : Type*} [Field F] (a : PowerSeries F) : ℕ → PowerSeries F
  | 0 => 1
  | n + 1 => cubeApprox a n + C (coeff (n + 1) (a - cubeApprox a n ^ 3) / 3) * X ^ (n + 1)

/-- The cube root of `a` (`a(0) = 1`, `3 ≠ 0`): coefficient `n` is that of `cubeApprox a n`. -/
noncomputable def cubeRt {F : Type*} [Field F] (a : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n => coeff n (cubeApprox a n)

/-! ## The Kummer frame `(1, ζ, ζ²; ∞)` with scale `θ` -/

/-- `τ = (1 + θx)^{1/3}`, `τ(0) = 1`. -/
noncomputable def kumTau (p : ℕ) [Fact p.Prime] (θ : ZMod p) : PowerSeries (ZMod p) := cubeRt (1 + C θ * X)

/-- The scaled local roots `z_c(θx) = ζ^c τ` of `w = z³ - 1`. -/
noncomputable def kumZ (p : ℕ) [Fact p.Prime] (ζ θ : ZMod p) : Fin 3 → PowerSeries (ZMod p) :=
  fun c => C (ζ ^ (c : ℕ)) * kumTau p θ

/-- The symmetric self-similar scramble of the Kummer frame (`def:selfsim`, `g_c = g` for all `c`). -/
noncomputable def kumGen (p : ℕ) [Fact p.Prime] (ζ θ : ZMod p) (g : PowerSeries (ZMod p)) : Gen 3 (ZMod p) :=
  ssGen (fun _ => g) (kumZ p ζ θ)

/-- The depth direction `u_d = θ/(3(1 - ζ^d))` of `eq:steer3`. -/
def kumU {F : Type*} [Field F] (ζ θ : F) (d : ℕ) : F := θ / (3 * (1 - ζ ^ d))

/-- `Σ_r = 1 + r τ⁻¹ + r² τ⁻²` (the response series of the offset with `r = ζ^{c - c'}`). -/
noncomputable def sig {F : Type*} [Field F] (τ : PowerSeries F) (r : F) : PowerSeries F :=
  1 + C r * τ⁻¹ + C (r ^ 2) * τ⁻¹ ^ 2

/-- A partial sum of a one-digit response in the free series `k`: `[x^l] (δ - E k)/(1 - x)`. -/
noncomputable def kresp {F : Type*} [Field F] (δ : F) (E k : PowerSeries F) (l : ℕ) : F :=
  coeff l ((C δ - E * k) * PowerSeries.mk 1)

/-! ## Covering windows in dimension three (`prop:cover3`) -/

/-- Condition (ii) of `prop:cover3`: every line `β + 𝔽 (1, u₁, u₂)` meets `W 0 × W 1 × W 2`. -/
def Covers3 {F : Type*} [CommRing F] (u1 u2 : F) (W : Fin 3 → Set F) : Prop :=
  ∀ β : Fin 3 → F, ∃ t : F, β 0 + t ∈ W 0 ∧ β 1 + t * u1 ∈ W 1 ∧ β 2 + t * u2 ∈ W 2

/-- Every one-digit response (`j = 1`, every level `K`, `1 ≤ l ≤ K`) lies in its window: `D(l)[c][c']`
in `W (c - c')` (`W 0` = own window `W_o`, `W d` = cross window `W_d`, indices modulo `3`). -/
def RespIn3 {p : ℕ} (C : Gen 3 (ZMod p)) (W : Fin 3 → Set (ZMod p)) : Prop :=
  ∀ K l : ℕ, 1 ≤ l → l ≤ K → ∀ c c' : Fin 3, ∀ d : ZMod p,
    IsCarryEntry C K 0 l c c' d → d ∈ W (c - c')

/-- `LB` is at most the certificate value `LB(W_o, W_1, W_2)` of `prop:cover3` (`lem:cert`, `j = 1`), in
pointwise form: for every step `e ∈ {-1,0,1}³ \ {0}` and every choice of entries `w c c' ∈ W (c - c')`,
`LB ≤ (∑_c f_1(e_c, ∑_{c'} e_{c'} w c c')²)^{1/2}`. -/
def C3bound (p : ℕ) [NeZero p] (W : Fin 3 → Set (ZMod p)) (LB : ℝ) : Prop :=
  ∀ e : Fin 3 → ℤ, (∀ c, -1 ≤ e c ∧ e c ≤ 1) → (∃ c, e c ≠ 0) →
    ∀ w : Fin 3 → Fin 3 → ZMod p, (∀ c c', w c c' ∈ W (c - c')) →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 p (e c) (∑ c', (e c' : ZMod p) * w c c') : ℝ) / p) ^ 2)

/-- The windows of `lem:prodbound`: `W_o = [-(S+A-1), -S]`, `W_d = [-b_d, b_d]`, `S = b₁ + b₂`. -/
def prodWin (p b1 b2 A : ℕ) : Fin 3 → Set (ZMod p) :=
  ![intWin p (-(((b1 + b2 + A : ℕ) : ℤ) - 1)) (-((b1 + b2 : ℕ) : ℤ)),
    intWin p (-(b1 : ℤ)) b1, intWin p (-(b2 : ℤ)) b2]

/-- `LB_D` of `lem:prodbound`: `min(1 - (S+A)/p, T₂, √3 (1 - (2S+A)/p))`,
`T₂² = (1 - (S+A+b₁)/p)² + (1 - (S+A+b₂)/p)²`. -/
noncomputable def prodLB (p b1 b2 A : ℕ) : ℝ :=
  min (1 - ((b1 + b2 + A : ℕ) : ℝ) / p)
    (min (Real.sqrt ((1 - ((b1 + b2 + A + b1 : ℕ) : ℝ) / p) ^ 2 +
        (1 - ((b1 + b2 + A + b2 : ℕ) : ℝ) / p) ^ 2))
      (Real.sqrt 3 * (1 - ((2 * (b1 + b2) + A : ℕ) : ℝ) / p)))

/-! ## The rule `R_p` (`thm:L3`) -/

/-- `|ȳ|` for the representative `ȳ ∈ (-p/2, p/2)` of `y ∈ [0, p)` (`p` odd). -/
def cenAbs (p y : ℕ) : ℕ := if 2 * y < p then y else p - y

/-- The representative `ȳ ∈ (-p/2, p/2)` of `y ∈ [0, p)` (`p` odd). -/
def cenInt (p y : ℕ) : ℤ := if 2 * y < p then (y : ℤ) else (y : ℤ) - p

/-- `n* = ⌈p/ν₁⌉`. -/
def l3Nst (p a : ℕ) : ℕ := (p + a - 1) / a

/-- `b_sweep = max(ν₂, ⌈(n* ν₂ - 1)/2⌉)` (`⌈(N-1)/2⌉ = ⌊N/2⌋`). -/
def l3Bs (p a b : ℕ) : ℕ := max b (l3Nst p a * b / 2)

/-- `A = n* + 1 + ⌈(p-2)/ν₂⌉`. -/
def l3Aw (p a b : ℕ) : ℕ := l3Nst p a + 1 + (p - 2 + b - 1) / b

/-- The side conditions of `lem:prodbound` for the candidate with `ν_wrap = a`, `ν_sweep = b`
(`b_wrap = a`): `2S + A < p`, `2 max(b_wrap, b_sweep) + 1 < p`. -/
abbrev l3Cond (p a b : ℕ) : Prop :=
  2 * (a + l3Bs p a b) + l3Aw p a b < p ∧ 2 * max a (l3Bs p a b) + 1 < p

/-- `LB_D` of the candidate with `ν_wrap = a`, `ν_sweep = b` (`0` if the side conditions fail). -/
noncomputable def l3LBD (p a b : ℕ) : ℝ :=
  if l3Cond p a b then prodLB p a (l3Bs p a b) (l3Aw p a b) else 0

/-- `y₂ ≡ -ζ y₁ (mod p)`, as a natural number in `[0, p)`. -/
def l3Y2 (p : ℕ) (ζ : ZMod p) (y : ℕ) : ℕ := (-(ζ * (y : ZMod p))).val

/-- The candidate `(y₁, wrap)` of `R_p` (`wrap ∈ {1, 2}`): `(ν_wrap, ν_sweep) = (|ȳ_wrap|, |ȳ_sweep|)`. -/
def l3Nu (p : ℕ) (ζ : ZMod p) (y w : ℕ) : ℕ × ℕ :=
  if w = 1 then (cenAbs p y, cenAbs p (l3Y2 p ζ y)) else (cenAbs p (l3Y2 p ζ y), cenAbs p y)

/-- The value `LB_D` of the candidate `(y₁, wrap)`. -/
noncomputable def l3Val (p : ℕ) (ζ : ZMod p) (y w : ℕ) : ℝ :=
  l3LBD p (l3Nu p ζ y w).1 (l3Nu p ζ y w).2

/-- The scale `θ = 3(1 - ζ) y₁` of the candidate (`lem:eis`(c)). -/
def l3Theta (p : ℕ) (ζ : ZMod p) (y : ℕ) : ZMod p := 3 * (1 - ζ) * (y : ZMod p)

/-- The windows of the candidate `(y₁, wrap)`: `W_wrap = [-ν_wrap, ν_wrap]`,
`W_sweep = [-b_sweep, b_sweep]`, `W_o = [-(S+A-1), -S]`. -/
def l3Win (p : ℕ) (ζ : ZMod p) (y w : ℕ) : Fin 3 → Set (ZMod p) :=
  if w = 1 then
    prodWin p (l3Nu p ζ y w).1 (l3Bs p (l3Nu p ζ y w).1 (l3Nu p ζ y w).2)
      (l3Aw p (l3Nu p ζ y w).1 (l3Nu p ζ y w).2)
  else
    prodWin p (l3Bs p (l3Nu p ζ y w).1 (l3Nu p ζ y w).2) (l3Nu p ζ y w).1
      (l3Aw p (l3Nu p ζ y w).1 (l3Nu p ζ y w).2)

/-- `F(p) = 1.9167 p^{3/4} + 4.25 p^{1/2} + 1.5 p^{1/4} + 4.5` (`thm:L3`). -/
noncomputable def l3F (p : ℕ) : ℝ :=
  19167 / 10000 * (p : ℝ) ^ ((3 : ℝ) / 4) + 425 / 100 * (p : ℝ) ^ ((1 : ℝ) / 2) +
    15 / 10 * (p : ℝ) ^ ((1 : ℝ) / 4) + 45 / 10

/-! ## The reflected checker of the finite range `97 ≤ p < 2·10^5` -/

/-- The primes below `448` (`448² > 2·10^5`). -/
def l3SmallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443]

/-- `n` has a divisor `d` with `d² ≤ n` in the list (so `n` is not prime). -/
def hasDiv (n : ℕ) : Bool := l3SmallPrimes.any fun d => d * d ≤ n && n % d == 0

/-- The integer test of one candidate with `ν_wrap = a`, `ν_sweep = b`, given `m` with
`m⁴ ≤ 10^16 p³` (so `m/10^4 ≤ p^{3/4}`): the side conditions and `LB_D ≥ 1 - 3.08 m/(10^4 p)`,
term by term (`√3 ≥ 1.73205`). -/
def l3NumOK (p a b m : ℕ) : Bool :=
  1 ≤ a && 1 ≤ b && 2 * (a + l3Bs p a b) + l3Aw p a b < p && 2 * max a (l3Bs p a b) + 1 < p &&
  m ^ 4 ≤ 10 ^ 16 * p ^ 3 && 308 * m < 10 ^ 6 * p &&
  10 ^ 6 * (a + l3Bs p a b + l3Aw p a b) ≤ 308 * m &&
  10 ^ 6 * p ≤ 1732050 * (p - 2 * (a + l3Bs p a b) - l3Aw p a b) + 308 * m &&
  (10 ^ 6 * p - 308 * m) ^ 2 ≤ 10 ^ 12 * ((p - (a + l3Bs p a b) - l3Aw p a b - a) ^ 2 +
    (p - (a + l3Bs p a b) - l3Aw p a b - l3Bs p a b) ^ 2)

/-- A certificate `(z, y₁, wrap, m)` for `p`: `z² + z + 1 ≡ 0 (mod p)` and the candidate `(y₁, wrap)` of
the cube root `z` passes `l3NumOK`. -/
def certOK (p : ℕ) : ℕ × ℕ × ℕ × ℕ → Bool
  | (z, y, w, m) => z < p && (z * z + z + 1) % p == 0 && 1 ≤ y && y < p &&
      (if w = 1 then l3NumOK p (cenAbs p y) (cenAbs p ((p - z * y % p) % p)) m
       else l3NumOK p (cenAbs p ((p - z * y % p) % p)) (cenAbs p y) m)

/-- The checker on `n, n+3, …, n+3(cnt-1)`: each `n` has a small divisor or the next certificate is
valid for it. -/
def l3Check : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | _, 0, _ => true
  | n, k + 1, l => match hasDiv n with
    | true => l3Check (n + 3) k l
    | false => match l with
      | [] => false
      | e :: t => certOK n e && l3Check (n + 3) k t

end GeoSeq
