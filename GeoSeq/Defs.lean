/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited), sequel to "Low-discrepancy
quasi-uniform digital nets in every dimension" (the nets paper (hexagon:2610.00217v1)).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import Mathlib
public import Z3Net.DGSDefs

@[expose] public section

/-!
# GeoSeq stage S0: core definitions (`sec:prelim`, `sec:law`)

Shared by the statement files `GeoSeq/Statements/*.lean` and the proof files, so statements and
proofs use the same constants (house convention of the geo formalization, `*Defs` modules).

* Digital sequences over a finite commutative ring `R` whose digits are read through a code
  `enc : R ≃ Fin q` with `enc 0 = 0` (`DigitCode`; `sec:prelim`). Generator matrices are infinite:
  `C c n k` = row `n` (output digit, `0` most significant) and column `k` (index digit) of `C_c`.
* The point with index `v` (`seqPoint`, a real point of `[0,1]^s`, all digits), its cells
  (`cellIdx`), the `(0,s)`-sequence property in the block form of the paper (`IsSeq0`), and the
  separation of the full level `P_{sK}` (`SepAtLevel`, the statement `c(P_{sK}) ≥ LB`).
* The level law: digits of an index VECTOR (`vecDigit`) and the carry responses `D_i(l)` (entry
  `(c, c')`, `IsCarryEntry`), defined semantically as in `sec:law`.
* The one-coordinate certificate quantity `f_j` of `lem:cert` as an integer numerator
  (`gapNum`: `f_j(e, σ) = gapNum / q^j`), and its one-digit form over `ℤ/qℤ` (`gapNum1`).
* Self-similar scrambles (`def:selfsim`, `ssGen`), the brick walls `W^±` (`def:WF`, `WFgen`), and the
  base-2 sequence of `thm:B2` (`B2gen`).

Box membership is read off the digits (an elementary box with `d_c` digits in coordinate `c` is
the set of points whose first `d_c` digits encode `a_c`), as in geo `lem:nie`; this avoids the
ambiguity of digit expansions ending in `q-1, q-1, …` and agrees with the paper's convention.
-/

namespace GeoSeq

open Finset PowerSeries

/-! ## Digit codes and digital sequences (`sec:prelim`) -/

/-- The fixed bijection `enc : R → {0, …, q-1}` of `sec:prelim`, with `enc 0 = 0`. -/
structure DigitCode (R : Type*) [Zero R] (q : ℕ) where
  enc : R ≃ Fin q
  enc_zero : ((enc 0 : Fin q) : ℕ) = 0

/-- The code of `ℤ/qℤ` for prime (or any positive) `q`: `enc r = r.val`. -/
def zcode (q : ℕ) [NeZero q] : DigitCode (ZMod q) q where
  enc :=
    { toFun := fun r => ⟨r.val, ZMod.val_lt r⟩
      invFun := fun i => (i : ℕ)
      left_inv := fun r => by simp
      right_inv := fun i => by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2] }
  enc_zero := by simp

variable {R : Type*} [CommRing R] {q s : ℕ}

/-- Generator matrices of an `s`-dimensional digital sequence over `R`: `C c n k = C_c[n][k]`. -/
abbrev Gen (s : ℕ) (R : Type*) := Fin s → ℕ → ℕ → R

/-- Base-`q` index digit `v_k` of the index `v = ∑_k v_k q^k`, as an element of `R`. -/
def idxDigit [NeZero q] (D : DigitCode R q) (v k : ℕ) : R :=
  D.enc.symm ⟨v / q ^ k % q, Nat.mod_lt _ (NeZero.pos q)⟩

/-- Digit `n` of coordinate `c` of the point with index `v`: `y_{c,n}(v) = ∑_k C_c[n][k] v_k`
(the sum is finite: `v_k = 0` for `k > v` when `q ≥ 2`). -/
def seqDigit [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) (n : ℕ) : R :=
  ∑ k ∈ range (v + 1), C c n k * idxDigit D v k

/-- Coordinate `c` of the point `y(v) ∈ [0,1]`: `y_c(v) = ∑_n enc(y_{c,n}(v)) q^{-n-1}`. -/
noncomputable def seqCoord [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) : ℝ :=
  ∑' n : ℕ, ((D.enc (seqDigit D C v c n) : ℕ) : ℝ) / (q : ℝ) ^ (n + 1)

/-- The point `y(v)` of the digital sequence. -/
noncomputable def seqPoint [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) : Fin s → ℝ :=
  fun c => seqCoord D C v c

/-- The cell index of coordinate `c` with `d` digits: `∑_{n<d} enc(y_{c,n}(v)) q^{d-1-n}`. -/
def cellIdx [NeZero q] (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s) (d : ℕ) : ℕ :=
  ∑ n : Fin d, (D.enc (seqDigit D C v c n) : ℕ) * q ^ (d - 1 - (n : ℕ))

/-- The block `{y(v) : k q^m ≤ v < (k+1) q^m}` is a `(0,m,s)`-net: for every `d` with `∑_c d_c = m`,
every elementary box with `d_c` digits in coordinate `c` contains exactly one point of the block. -/
def BlockNet0 [NeZero q] (D : DigitCode R q) (C : Gen s R) (m k : ℕ) : Prop :=
  ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ a : Fin s → ℕ, (∀ c, a c < q ^ d c) →
    ∃! v : ℕ, (k * q ^ m ≤ v ∧ v < (k + 1) * q ^ m) ∧ ∀ c, cellIdx D C v c (d c) = a c

/-- `(0,s)`-sequence in base `q` (`sec:prelim`): every block of `q^m` consecutive points starting at a
multiple of `q^m` is a `(0,m,s)`-net. -/
def IsSeq0 [NeZero q] (D : DigitCode R q) (C : Gen s R) : Prop :=
  ∀ m k : ℕ, BlockNet0 D C m k

/-- The leading `m × m` blocks of the generator matrices (stage S1): the generator matrices of the
prefix `P_m = {y(v) : v < q^m}`, read as a digital net in the sense of geo `lem:nie`
(`Z3NetF.IsNet0E`). -/
def truncGen (C : Gen s R) (m : ℕ) : Fin s → Matrix (Fin m) (Fin m) R :=
  fun c i j => C c i j

/-- The generator matrices with their columns shifted by `m`: `shiftCols C m c n k = C_c[n][m + k]`
(stage S1; the digital shift of block `k` of `q^m` points is the point `k` of this sequence). -/
def shiftCols (C : Gen s R) (m : ℕ) : Gen s R := fun c n k => C c n (m + k)

/-- `c(P_{sK}) ≥ LB`: any two distinct points of the full level `P_{sK} = {y(v) : v < q^{sK}}` have
toroidal Euclidean distance `≥ LB · q^{-K} = LB · N^{-1/s}` (`N = q^{sK}`; `sec:prelim`). -/
def SepAtLevel (q s K : ℕ) (pt : ℕ → Fin s → ℝ) (LB : ℝ) : Prop :=
  ∀ v w : ℕ, v < q ^ (s * K) → w < q ^ (s * K) → v ≠ w →
    LB ≤ (q : ℝ) ^ K * Z3NetDGS.torDist2 (pt v) (pt w)

/-- `δ(P_{[N]}) ≥ b · N^{-1/s}` for every `N ≥ 2` (the first `N` points; `lem:prefix`). -/
def SepAllN (s : ℕ) (pt : ℕ → Fin s → ℝ) (b : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ v w : ℕ, v < N → w < N → v ≠ w →
    b * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ Z3NetDGS.torDist2 (pt v) (pt w)

/-- The (non-toroidal) Euclidean distance, used for the covering radius `h` (`sec:prelim`). -/
noncomputable def euclDist (x y : Fin s → ℝ) : ℝ := Real.sqrt (∑ c, (x c - y c) ^ 2)

/-- The first `N` points `P_{[N]}` as a finite set of real points. -/
noncomputable def prefixSet (N : ℕ) (pt : ℕ → Fin s → ℝ) : Finset (Fin s → ℝ) :=
  (range N).image pt

/-! ## Frames and scrambles (`lem:t0`; moved here from `Statements/Prelim.lean` in stage S1) -/

/-- The Pascal matrix at the place `a`: `P_a[n][k] = C(k, n) a^{k-n}` (`0` for `n > k`). -/
def pas {R : Type*} [CommRing R] (a : R) (n k : ℕ) : R := (k.choose n : R) * a ^ (k - n)

/-- The scrambled frame `C_c = L_c P_{a_c}` with lower-triangular `L_c` (only the entries
`L_c[n][i]`, `i ≤ n`, are used). -/
def scrGen {R : Type*} [CommRing R] {s : ℕ} (a : Fin s → R) (L : Fin s → ℕ → ℕ → R) :
    Gen s R :=
  fun c n k => ∑ i ∈ range (n + 1), L c n i * pas (a c) i k

/-! ## The level law and the carry responses (`sec:law`) -/

/-- Digit `n` of coordinate `c` for an index VECTOR `V ∈ R^m` (`deg V < m`): `∑_{k<m} C_c[n][k] V_k`.
The level-`K` law is linear in `V`, so differences of digits are digits of differences of index
vectors. -/
def vecDigit {m : ℕ} (C : Gen s R) (V : Fin m → R) (c : Fin s) (n : ℕ) : R :=
  ∑ k : Fin m, C c n k * V k

/-- The carry pattern at level `K`: `1` on the `l` finest cell digits `K-l, …, K-1` of coordinate
`c'`, `0` on every other cell digit (`sec:law`; `1 ≤ l ≤ K`). -/
def carryPat (K l : ℕ) (c' c : Fin s) (n : ℕ) : R :=
  if c = c' ∧ K - l ≤ n ∧ n < K then 1 else 0

/-- `IsCarryEntry C K i l c c' d`: the entry `D_i(l)[c][c'] = d` of the carry response at level `K`
(`sec:law`): there is an index vector `V ∈ R^{sK}` whose cell digits (digits `0, …, K-1` of every
coordinate) are the carry pattern of coordinate `c'`, and every such `V` has the digit `K+i` of
coordinate `c` equal to `d`. (For a `(0, sK, s)`-net `V` is unique; by linearity, `d` is the change of
the geometric digit `K+i` of coordinate `c` when `1` is added to each of the `l` finest cell digits
of coordinate `c'`, which for prime `q` is the step of `n_{c'}` by `+1` with carry length `l`.) -/
def IsCarryEntry (C : Gen s R) (K i l : ℕ) (c c' : Fin s) (d : R) : Prop :=
  (∃ V : Fin (s * K) → R, ∀ c₁ : Fin s, ∀ n < K, vecDigit C V c₁ n = carryPat K l c' c₁ n) ∧
  ∀ V : Fin (s * K) → R, (∀ c₁ : Fin s, ∀ n < K, vecDigit C V c₁ n = carryPat K l c' c₁ n) →
    vecDigit C V c (K + i) = d

/-! ## The certificate quantity `f_j` (`lem:cert`) -/

/-- The integer `enc(R) = ∑_{i<j} enc(R_i) q^{j-1-i}` of a vector of `j` geometric digits. -/
def encVec (D : DigitCode R q) {j : ℕ} (r : Fin j → R) : ℕ :=
  ∑ i : Fin j, (D.enc (r i) : ℕ) * q ^ (j - 1 - (i : ℕ))

/-- Numerator of the guaranteed gap `f_j(e, σ)` of `lem:cert`:
`f_j(e, σ) = max(0, min_R |e q^j + enc(R ⊕ σ) - enc(R)| - 1) / q^j`, `⊕` digitwise in `R`
(truncated subtraction on `ℕ` gives the `max(0, ·)`). -/
def gapNum [Fintype R] [DecidableEq R] (D : DigitCode R q) (j : ℕ) (e : ℤ) (σ : Fin j → R) : ℕ :=
  ((univ.image fun r : Fin j → R =>
      ((e * (q : ℤ) ^ j + (encVec D (r + σ) : ℤ) - (encVec D r : ℤ)).natAbs)).min'
      (by simp)) - 1

/-- One geometric digit over `ℤ/qℤ` (`rem:onedigit`): `f_1(e, σ) = gapNum1 q e σ / q` with
`gapNum1 q e σ = max(0, min_{r ∈ ℤ/qℤ} |e q + val(r + σ) - val(r)| - 1)`. -/
def gapNum1 (q : ℕ) [NeZero q] (e : ℤ) (σ : ZMod q) : ℕ :=
  ((univ.image fun r : ZMod q =>
      ((e * (q : ℤ) + ((r + σ).val : ℤ) - (r.val : ℤ)).natAbs)).min' (by simp)) - 1

/-! ## The certificate in its point-set form (`lem:cert`, stage S2) -/

/-- `Δ(y)` of `rem:F4carry`: the change in `R` of the digit `y` when its code goes up by one
(modulo `q`), `Δ(y) = enc⁻¹((enc y + 1) mod q) - y`. For `ℤ/qℤ` with `enc = val` it is `1`. -/
def digInc [NeZero q] (D : DigitCode R q) (y : R) : R :=
  D.enc.symm ⟨((D.enc y : ℕ) + 1) % q, Nat.mod_lt _ (NeZero.pos q)⟩ - y

/-- The top digit `ȳ = enc⁻¹(q - 1)` (`rem:F4carry`). -/
def topDigit [NeZero q] (D : DigitCode R q) : R :=
  D.enc.symm ⟨q - 1, Nat.sub_lt (NeZero.pos q) Nat.one_pos⟩

/-- `δ_i(l, y)[c][c']` of `eq:carrychange`: the change of the geometric digit `K+i` of coordinate `c`
when the cell index of coordinate `c'` steps by `+1` with carry length `l`, stopping at a digit with
value `y`: `Δ(ȳ) D_i(l-1) + Δ(y) (D_i(l) - D_i(l-1))`, where `Dr i l = D_i(l)` (with `D_i(0) = 0`). -/
def carryChange [NeZero q] (D : DigitCode R q) (Dr : ℕ → ℕ → Fin s → Fin s → R) (i l : ℕ) (y : R)
    (c c' : Fin s) : R :=
  digInc D (topDigit D) * Dr i (l - 1) c c' + digInc D y * (Dr i l c c' - Dr i (l - 1) c c')

/-- `σ_c ∈ R^j` of `lem:cert` (general digit code): `σ_{c,i} = ∑_{c'} e_{c'} δ_i(l_{c'}, y_{c'})[c][c']`
(the terms with `e_{c'} = 0` vanish). -/
def certSigma [NeZero q] (D : DigitCode R q) (Dr : ℕ → ℕ → Fin s → Fin s → R) (j : ℕ)
    (e : Fin s → ℤ) (l : Fin s → ℕ) (y : Fin s → R) (c : Fin s) : Fin j → R :=
  fun i => ∑ c', (e c' : R) * carryChange D Dr i (l c') (y c') c c'

/-- `σ_c ∈ R^j` of `lem:cert` for prime `q` (every step adds `1` to the digits it changes):
`σ_{c,i} = ∑_{c'} e_{c'} D_i(l_{c'})[c][c']`. -/
def certSigmaP (Dr : ℕ → ℕ → Fin s → Fin s → R) (j : ℕ) (e : Fin s → ℤ) (l : Fin s → ℕ)
    (c : Fin s) : Fin j → R :=
  fun i => ∑ c', (e c' : R) * Dr i (l c') c c'

/-- The steps of `lem:cert` at level `K`: `e ∈ {-1,0,1}^s \ {0}` and carry lengths `l_c ∈ [1, K]`
(the carry lengths of the coordinates with `e_c = 0` do not enter `σ`). -/
def IsStep (K : ℕ) (e : Fin s → ℤ) (l : Fin s → ℕ) : Prop :=
  (∀ c, -1 ≤ e c ∧ e c ≤ 1) ∧ (∃ c, e c ≠ 0) ∧ ∀ c, 1 ≤ l c ∧ l c ≤ K

/-- One term of the certificate: `(∑_c f_j(e_c, σ_c)²)^{1/2}`, with `f_j = gapNum / q^j`. -/
noncomputable def certTerm [Fintype R] [DecidableEq R] (D : DigitCode R q) (j : ℕ) (e : Fin s → ℤ)
    (σ : Fin s → Fin j → R) : ℝ :=
  Real.sqrt (∑ c, ((gapNum D j (e c) (σ c) : ℝ) / (q : ℝ) ^ j) ^ 2)

/-! ## Self-similar scrambles and the constructions (`def:selfsim`, `def:WF`, `thm:B2`) -/

/-- **`def:selfsim`**: the generator matrices `C_c[n][k] = [x^n] g_c(x) · z_c(θx)^k` of the
self-similar scramble with multipliers `g_c` and scaled local roots `zθ c = z_c(θx)`. -/
noncomputable def ssGen (g zθ : Fin s → PowerSeries R) : Gen s R :=
  fun c n k => coeff n (g c * zθ c ^ k)

/-- The places of a self-similar scramble (stage S1): `a_c = z_c(θ·0)`, the constant term of the
scaled local root. -/
noncomputable def ssPlace (zθ : Fin s → PowerSeries R) : Fin s → R :=
  fun c => constantCoeff (zθ c)

/-- The scramble of a self-similar scramble (stage S1): `L_c[n][i] = [x^n] g_c (z_c(θx) - a_c)^i`, so
that `ssGen g zθ = scrGen (ssPlace zθ) (ssScr g zθ)`, i.e. `C_c = L_c P_{a_c}` (`def:selfsim`). -/
noncomputable def ssScr (g zθ : Fin s → PowerSeries R) : Fin s → ℕ → ℕ → R :=
  fun c n i => coeff n (g c * (zθ c - C (constantCoeff (zθ c))) ^ i)

/-- Coefficients of `√(1 + a x)` over `ℤ/pℤ` (`p` odd), by the recursion of `ρ² = 1 + a x`:
`ρ_0 = 1`, `2 ρ_{n+1} = [n = 0] a - ∑_{i=1}^{n} ρ_i ρ_{n+1-i}`. -/
def sqrtCoeff (p : ℕ) (a : ZMod p) : ℕ → ZMod p
  | 0 => 1
  | n + 1 => ((if n = 0 then a else 0) -
      ∑ i : Fin n, sqrtCoeff p a (i + 1) * sqrtCoeff p a (n - i)) * (2 : ZMod p)⁻¹
decreasing_by all_goals omega

/-- `ρ = √(1 + a x) ∈ 𝔽_p[[x]]`, `ρ(0) = 1` (`def:WF` with `a = ±1`). -/
noncomputable def rhoWF (p : ℕ) (a : ZMod p) : PowerSeries (ZMod p) := mk (sqrtCoeff p a)

/-- **`def:WF`**: the multipliers of the brick wall `W^±` (`a = ±1`, `θ = ±1/4`, `ρ = √(1 ± x)`):
`g_0 = 2ρ / ((1 - x)(1 + ρ))`, `g_1 = (1 + ρ)/ρ`. -/
noncomputable def WFg (p : ℕ) [Fact p.Prime] (a : ZMod p) : Fin 2 → PowerSeries (ZMod p) :=
  ![C (2 : ZMod p) * rhoWF p a * ((1 - X) * (1 + rhoWF p a))⁻¹,
    (1 + rhoWF p a) * (rhoWF p a)⁻¹]

/-- The scaled local roots of the Faure frame for `W^±`: `z_0(θx) = (1 - ρ)/2`, `z_1(θx) = (1 + ρ)/2`
(`u + u² = θx`, `ρ = 1 + 2u(θx)`). -/
noncomputable def WFz (p : ℕ) [Fact p.Prime] (a : ZMod p) : Fin 2 → PowerSeries (ZMod p) :=
  ![C (2 : ZMod p)⁻¹ * (1 - rhoWF p a), C (2 : ZMod p)⁻¹ * (1 + rhoWF p a)]

/-- **`def:WF`**: generator matrices of the brick wall `W^-` (`a = -1`) and `W^+` (`a = 1`). -/
noncomputable def WFgen (p : ℕ) [Fact p.Prime] (a : ZMod p) : Gen 2 (ZMod p) :=
  ssGen (WFg p a) (WFz p a)

/-- The lacunary series `u = ∑_{k≥0} x^{2^k} ∈ 𝔽_2[[x]]` of `thm:B2` (`u² + u = x`): coefficient `1`
exactly at the powers of two. -/
def uB2coeff (n : ℕ) : ZMod 2 := if ∃ k < n + 1, 2 ^ k = n then 1 else 0

/-- `u = ∑_k x^{2^k}`. -/
noncomputable def uB2 : PowerSeries (ZMod 2) := mk uB2coeff

/-- **`thm:B2`**: multipliers `g_0 = (1 + x)(1 + u)`, `g_1 = u/x` (scale `θ = 1`). -/
noncomputable def B2g : Fin 2 → PowerSeries (ZMod 2) :=
  ![(1 + X) * (1 + uB2), mk fun n => uB2coeff (n + 1)]

/-- **`thm:B2`**: local roots `z_0 = u`, `z_1 = 1 + u` of the Faure frame `w = z² + z` over `𝔽_2`. -/
noncomputable def B2z : Fin 2 → PowerSeries (ZMod 2) := ![uB2, 1 + uB2]

/-- **`thm:B2`**: generator matrices `C_0 = L_0`, `C_1 = L_1 P_1`,
`y_{0,n} = [x^n](1+x)(1+u)V(u)`, `y_{1,n} = [x^n](u/x)V(1+u)`. -/
noncomputable def B2gen : Gen 2 (ZMod 2) := ssGen B2g B2z

/-- **`eq:B2G`** (stage S5): the inverse of the frame matrix of `thm:B2`,
`G = ((1/(1+x), x), (u/(x(1+x)), 1+u))` (`u/x = B2g 1`). -/
noncomputable def B2G : Matrix (Fin 2) (Fin 2) (PowerSeries (ZMod 2)) :=
  !![(1 + X)⁻¹, X; B2g 1 * (1 + X)⁻¹, 1 + uB2]

/-! ## The base-3 sequence (`thm:B3`, stage S6) -/

/-- `3` is prime (the base of `thm:B3`). -/
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `τ = √(1 + x) ∈ 𝔽_3[[x]]`, `τ(0) = 1` (`thm:B3`; the recursion of `sqrtCoeff`). -/
noncomputable def tau3 : PowerSeries (ZMod 3) := rhoWF 3 1

/-- **`thm:B3`**: multipliers `g_0 = -(1+x)(1-x+τ)/(1-x)`, `g_1 = -(1+τ)/τ` (scale `θ = 1`). -/
noncomputable def B3g : Fin 2 → PowerSeries (ZMod 3) :=
  ![-((1 + X) * (1 - X + tau3)) * (1 - X)⁻¹, -(1 + tau3) * tau3⁻¹]

/-- **`thm:B3`**: local roots `z_0 = τ - 1`, `z_1 = 2 - τ` of the Faure frame `w = z² - z` over `𝔽_3`. -/
noncomputable def B3z : Fin 2 → PowerSeries (ZMod 3) := ![tau3 - 1, 2 - tau3]

/-- **`thm:B3`**: generator matrices `y_{c,n}(v) = [x^n] g_c V(z_c)`. -/
noncomputable def B3gen : Gen 2 (ZMod 3) := ssGen B3g B3z

/-- The digit rule of `lem:frames`(b) with fuel: `1` if every base-3 digit of `n` is `0` or `1`. -/
def t3cAux : ℕ → ℕ → ZMod 3
  | 0, _ => 1
  | f + 1, n => if n = 0 then 1 else if n % 3 = 2 then 0 else t3cAux f (n / 3)

/-- `[x^n] τ^{-1}` over `𝔽_3` (`lem:frames`(b)): `1` if all base-3 digits of `n` are `0` or `1`,
`0` otherwise. -/
def t3c (n : ℕ) : ZMod 3 := t3cAux n n

/-- The Kummer root `τ^{-1} = ∏_{i ≥ 0} (1 + x^{3^i}) ∈ 𝔽_3[[x]]` (`lem:frames`(b), `q = 3`). -/
noncomputable def T3 : PowerSeries (ZMod 3) := PowerSeries.mk t3c

/-! ## The law of a self-similar scramble (`prop:law`, stage S3) -/

/-- The frame matrix of `prop:law`: `M(x)[c][b] = g_c(x) · z_c(θx)^b` (`0 ≤ c, b < s`), a matrix of
power series. -/
noncomputable def frameM (g zθ : Fin s → PowerSeries R) : Matrix (Fin s) (Fin s) (PowerSeries R) :=
  fun c b => g c * zθ c ^ (b : ℕ)

/-- The carry response of `prop:law` (second form):
`D_i(l)[c][c'] = δ_{cc'} - ∑_{a ≤ i} ∑_b [x^a] M[c][b] · [x^{l+i-a}] Ĝ[b][c']`, i.e.
`D_i(l) = I - ∑_{a≤i} M_a Ĝ_{l+i-a}`, with `Ĝ = G/(1-x)` (`G · mk 1`, `mk 1 = 1/(1-x)`) for a right
inverse `G` of the frame matrix. It does not involve the level `K`. -/
noncomputable def lawD (g zθ : Fin s → PowerSeries R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (i l : ℕ) (c c' : Fin s) : R :=
  (if c = c' then 1 else 0) -
    ∑ a ∈ range (i + 1), ∑ b, coeff a (frameM g zθ c b) * coeff (l + i - a) (G b c' * PowerSeries.mk 1)

/-- The tail `M_{>i} = M - ∑_{a ≤ i} M_a x^a` of the frame matrix (`prop:law`, first form). -/
noncomputable def frameTail (g zθ : Fin s → PowerSeries R) (i : ℕ) :
    Matrix (Fin s) (Fin s) (PowerSeries R) :=
  fun c b => PowerSeries.mk fun n => if i < n then coeff n (frameM g zθ c b) else 0

/-! ## The Faure frame and the brick walls over a general field (stage S3) -/

/-- The inverse of the Faure frame matrix (`lem:gform`): `G = ((z_1 k_0, -z_0 k_1), (-k_0, k_1))` with
`k_c = 1/(ρ g_c)`, `ρ = z_1 - z_0`. -/
noncomputable def faureG {F : Type*} [Field F] (z0 z1 k0 k1 : PowerSeries F) :
    Matrix (Fin 2) (Fin 2) (PowerSeries F) :=
  !![z1 * k0, -(z0 * k1); -k0, k1]

/-- The scaled local roots of `W^±` over a field `F` (`def:WF` with `ρ` abstract):
`z_0 = (1 - ρ)/2`, `z_1 = (1 + ρ)/2`. -/
noncomputable def wfZ {F : Type*} [Field F] (ρ : PowerSeries F) : Fin 2 → PowerSeries F :=
  ![C (2 : F)⁻¹ * (1 - ρ), C (2 : F)⁻¹ * (1 + ρ)]

/-- The multipliers of `W^±` over a field `F` (`def:WF` with `ρ` abstract):
`g_0 = 2ρ/((1-x)(1+ρ))`, `g_1 = (1+ρ)/ρ`. -/
noncomputable def wfG {F : Type*} [Field F] (ρ : PowerSeries F) : Fin 2 → PowerSeries F :=
  ![C (2 : F) * ρ * ((1 - X) * (1 + ρ))⁻¹, (1 + ρ) * ρ⁻¹]

/-- `k_c = 1/((z_1 - z_0) g_c)` (`lem:gform`) for `thm:B3` (stage S6). -/
noncomputable def B3k (c : Fin 2) : PowerSeries (ZMod 3) := ((B3z 1 - B3z 0) * B3g c)⁻¹

/-- The inverse of the frame matrix of `thm:B3` in the Faure form of `lem:gform`. -/
noncomputable def B3G : Matrix (Fin 2) (Fin 2) (PowerSeries (ZMod 3)) :=
  faureG (B3z 0) (B3z 1) (B3k 0) (B3k 1)

/-! ## Fidelity data (stage S1): the running example and `tab:B2dir` -/

/-- `7` is prime (the base of the running example `ex:running`). -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- **`tab:B2dir`**: the 32-bit direction numbers `M_c[k] = ∑_{n<32} C_c[n][k] 2^{31-n}` of the
base-2 sequence of `thm:B2`, as printed in the paper (hexadecimal), `k = 0, …, 31`. -/
def B2dirTab : Fin 2 → List ℕ :=
  ![[0x9cc0c000, 0x60000000, 0x2e606000, 0x1e606000, 0x09505000, 0x06606000, 0x02c84800, 0x01f87800,
     0x009c5c00, 0x00606000, 0x002e4e00, 0x001e7e00, 0x00095900, 0x00066600, 0x0002ca80, 0x0001f980,
     0x00009cc0, 0x00006000, 0x00002e60, 0x00001e60, 0x00000950, 0x00000660, 0x000002c8, 0x000001f8,
     0x0000009c, 0x00000060, 0x0000002e, 0x0000001e, 0x00000009, 0x00000006, 0x00000002, 0x00000001],
    [0xd1010001, 0x80000000, 0xe8808000, 0xa8808000, 0xdcc0c000, 0x88808000, 0xe6e0e000, 0xa2a0a000,
     0xd1d0d000, 0x80808000, 0xe868e800, 0xa828a800, 0xdc1cdc00, 0x88088800, 0xe606e600, 0xa202a200,
     0xd101d100, 0x80008000, 0xe8806880, 0xa8802880, 0xdcc01cc0, 0x88800880, 0xe6e006e0, 0xa2a002a0,
     0xd1d001d0, 0x80800080, 0xe8680068, 0xa8280028, 0xdc1c001c, 0x88080008, 0xe6060006, 0xa2020002]]

end GeoSeq
