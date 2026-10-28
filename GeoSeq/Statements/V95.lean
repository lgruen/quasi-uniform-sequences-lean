/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Defs

@[expose] public section

/-!
# Statements: stage V95 (paper V4)

Corollaries of `thm:nonqu` over prime fields: generator-matrix sequences as linear coordinates, scrambles (`cor:unscrambled`), reorderings and the Gray code (`rem:randomize`(b)), Sobol' sequences (`eq:sobrec`, `lem:sobol`, `cor:sobol` with explicit pairs), Niederreiter sequences (`lem:nied`, `cor:nied`) and `rem:faurerate`.
PROVED (`GeoSeq/V95Gen.lean`, `GeoSeq/V95Nied.lean`, `GeoSeq/V95Rate.lean`, `GeoSeq/V95Sobol.lean`, `GeoSeq/V95SobolPair.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v9x_statements.py V95`
(definitions in `GeoSeq/V95Defs.lean`). Paper: V4 (`paper/sections/03-fail.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository Configuration:
`comparatorGeoSeqV95.json`.
-/

namespace GeoSeq

section G0
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

theorem genY_lin (C : Gen s F) (c : Fin s) : IsLinCoord (genY C c) := by
  sorry

/-- The Taylor coordinate at `a`: `Y(V)_n = [(z - a)^n] V` is the coordinate of the frame row `P_a`. -/
theorem pas_sum (a : F) (V : F[X]) (n : ℕ) :
    V.sum (fun k r => pas a n k * r) = (taylor a V).coeff n := by
  sorry

theorem scrY_lin (L : ℕ → ℕ → F) (Y : F[X] → ℕ → F) (hY : IsLinCoord Y) : IsLinCoord (scrY L Y) := by
  sorry

/-- A lower-triangular scramble of a `b`-adic coordinate is `b`-adic (`sec:polybases`). -/
theorem scrY_isBAdic (L : ℕ → ℕ → F) (Y : F[X] → ℕ → F) (b : F[X]) (hY : IsBAdic Y b) :
    IsBAdic (scrY L Y) b := by
  sorry

/-- `μ` times a radical inverse with digit map `π` is a radical inverse with digit map `μπ` (`μ ≠ 0`). -/
theorem smul_isRadInv (μ : F) (hμ : μ ≠ 0) (Y : F[X] → ℕ → F) (b : F[X]) (π : F[X] → ℕ → F)
    (h : IsRadInv Y b π) : IsRadInv (fun V n => μ * Y V n) b (fun a i => μ * π a i) := by
  sorry

/-- The Taylor coordinate is `(z - a)`-adic. -/
theorem taylor_isBAdic (a : F) : IsBAdic (fun V n => (taylor a V).coeff n) (X - C a) := by
  sorry

/-- The `β^{-1}(z - a)`-adic digits are `β^Q [(z-a)^Q] V` (constants). -/
theorem badicDigit_scaled (a β : F) (hβ : β ≠ 0) :
    ∀ (Q : ℕ) (V : F[X]), badicDigit (C β⁻¹ * (X - C a)) V Q = C (β ^ Q * (taylor a V).coeff Q) := by
  sorry

/-- The diagonally scaled frame coordinate `μ β^n [(z - a)^n] V` is the `β^{-1}(z - a)`-adic radical inverse with
digit map `a ↦ μ [z^0] a` (`cor:unscrambled`). -/
theorem scaledFrame_isRadInv (a μ β : F) (hμ : μ ≠ 0) (hβ : β ≠ 0) :
    IsRadInv (fun V n => μ * β ^ n * (taylor a V).coeff n) (C β⁻¹ * (X - C a))
      (fun r _ => μ * r.coeff 0) := by
  sorry

end G0

section G1
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- A generator-matrix sequence over `ℤ/pℤ` is the linear-coordinate sequence of its rows. -/
theorem seqPoint_eq_linPt (C : Gen s (ZMod p)) : seqPoint (zcode p) C = linPt p (genY C) := by
  sorry

end G1

section G2
open Finset Polynomial
variable {s : ℕ}

/-- **Close pairs exclude quasi-uniformity** (last step of `thm:nonqu`): if for every `ε > 0` some prefix `P_m`
(`N = p^m` points, `p ≥ 2`) contains two distinct points closer than `ε p^{-m/s}`, the sequence is not quasi-uniform
(the covering radius of `p^m` points is `≥ p^{-m/s}/(2p)`). -/
theorem not_qu_of_close {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform pt := by
  sorry

/-- Reorderings that permute every prefix `{0, …, p^m - 1}` keep the close pairs (`rem:randomize`(b)). -/
theorem close_comp {p : ℕ} (pt : ℕ → Fin s → ℝ) (σ : ℕ → ℕ)
    (hσ : ∀ m v, v < p ^ m → ∃ v', v' < p ^ m ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist ((pt ∘ σ) v) ((pt ∘ σ) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
  sorry

/-- `rem:randomize`(b): a sequence with close pairs stays non-quasi-uniform under every reordering that permutes
each prefix `{0, …, p^m - 1}`. -/
theorem not_qu_comp {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (σ : ℕ → ℕ)
    (hσ : ∀ m v, v < p ^ m → ∃ v', v' < p ^ m ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (pt ∘ σ) := by
  sorry

theorem gray_injective : Function.Injective gray := by
  sorry

/-- The Gray code permutes every prefix `{0, …, 2^m - 1}`. -/
theorem gray_surj (m v : ℕ) (hv : v < 2 ^ m) : ∃ v', v' < 2 ^ m ∧ gray v' = v := by
  sorry

end G2

section G3
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`cor:unscrambled`** (linear-coordinate form): let `b_0, …, b_{s-1}` be pairwise coprime of degrees `≥ 1`; let
coordinate `ĉ` be `μ` times a `b_ĉ`-adic radical inverse `Y_ĉ` (`μ ≠ 0`) and every other coordinate `c` be the
lower-triangular scramble `L_c` (arbitrary, fixed) of a `b_c`-adic coordinate `Y_c`. Then the sequence is not
quasi-uniform. -/
theorem unscrambled (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (μ : ZMod p) (hμ : μ ≠ 0) (L : Fin s → ℕ → ℕ → ZMod p) :
    ¬ IsQuasiUniform (linPt p fun c => if c = ch then fun V n => μ * Y ch V n else scrY (L c) (Y c)) := by
  sorry

/-- **`cor:unscrambled`**, "in particular": for distinct places, the scrambled frame `C_ĉ = μ diag(β^n) P_{a_ĉ}`,
`C_c = L_c P_{a_c}` (`c ≠ ĉ`, any `L_c`) is not quasi-uniform for any `μ, β ∈ 𝔽_p^*`. -/
theorem unscrambled_frame (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (ch : Fin s)
    (μ β : ZMod p) (hμ : μ ≠ 0) (hβ : β ≠ 0) (L : Fin s → ℕ → ℕ → ZMod p) :
    ¬ IsQuasiUniform (seqPoint (zcode p) (scrFrame a ch μ β L)) := by
  sorry

end G3

section G4
open Finset Polynomial
variable {b : (ZMod 2)[X]} {u : ℕ → ℕ}

/-- Admissible direction numbers satisfy `u_k < 2^k` for every `k ≥ 1`. -/
theorem sobolDir_lt (hb : 1 ≤ b.natDegree) (h : IsSobolDir b u) : ∀ k, 1 ≤ k → u k < 2 ^ k := by
  sorry

/-- **`eq:sobrec` in digit form**: for `j ≥ e`, column `j` is `∑_{0<i<e} α_i col_{j-i} + col_{j-e} + 2^{-e} col_{j-e}`
(the last term shifted down by `e` digits). -/
theorem scol_rec (hb : 1 ≤ b.natDegree) (h : IsSobolDir b u) (j : ℕ) (hj : b.natDegree ≤ j) (n : ℕ) :
    scol u n j = (∑ i ∈ range b.natDegree,
        if i ≠ 0 ∧ b.coeff (b.natDegree - i) = 1 then scol u n (j - i) else 0) +
      scol u n (j - b.natDegree) +
      (if b.natDegree ≤ n then scol u (n - b.natDegree) (j - b.natDegree) else 0) := by
  sorry

/-- `eq:sobrec` over `𝔽_2` in the form `∑_{t ≤ e} b_t col_{j-e+t} = 2^{-e} col_{j-e}` (`b_0 = b_e = 1`). -/
theorem scol_rec_t (hb : 1 ≤ b.natDegree) (hb0 : b.coeff 0 = 1) (h : IsSobolDir b u) (j : ℕ)
    (hj : b.natDegree ≤ j) (n : ℕ) :
    ∑ t ∈ range (b.natDegree + 1), b.coeff t * scol u n (j - b.natDegree + t) =
      if b.natDegree ≤ n then scol u (n - b.natDegree) (j - b.natDegree) else 0 := by
  sorry

/-- **`lem:sobol`(a)**: multiplication by `b` shifts the digits by `e` places, `y(b V) = 2^{-e} y(V)`. -/
theorem sobY_mul_b (hb : 1 ≤ b.natDegree) (hb0 : b.coeff 0 = 1) (h : IsSobolDir b u) (V : (ZMod 2)[X])
    (n : ℕ) : sobY u (b * V) n = if b.natDegree ≤ n then sobY u V (n - b.natDegree) else 0 := by
  sorry

/-- **`lem:sobol`(b)**: for `deg a < e` the point `y(a)` has no digits beyond position `e - 1`. -/
theorem sobY_low (a : (ZMod 2)[X]) (e : ℕ) (ha : a.natDegree < e) (n : ℕ) (hn : e ≤ n) :
    sobY u a n = 0 := by
  sorry

/-- The digit map of `lem:sobol` is upper unitriangular: `π(z^j)_i = 0` for `i > j` and `π(z^j)_j = 1` (`j < e`). -/
theorem sobol_pi_unitri (hb : 1 ≤ b.natDegree) (h : IsSobolDir b u) (j i : ℕ) (hj : j < b.natDegree) :
    sobY u (X ^ j) i = if j < i then 0 else if i = j then 1 else sobY u (X ^ j) i := by
  sorry

/-- **`lem:sobol`**: a Sobol' coordinate whose polynomial `b` (degree `e ≥ 1`) has constant term `1`, with admissible
direction numbers, is a `b`-adic radical inverse; the digit map is `π(a)_i = y(a)_i` (upper unitriangular,
`sobol_pi_unitri`). Primitivity is not used. -/
theorem sobol_radInv (hb : 1 ≤ b.natDegree) (hb0 : b.coeff 0 = 1) (h : IsSobolDir b u) :
    IsRadInv (sobY u) b (sobY u) := by
  sorry

end G4

section G5
open Finset Polynomial

/-- The van der Corput coordinate (`C = I`, direction numbers `u_k = 1`) is the `z`-adic radical inverse with digit
map `a ↦ [z^0] a`. -/
theorem vdc_radInv (u : ℕ → ℕ) (hu : ∀ k, 1 ≤ k → u k = 1) :
    IsRadInv (sobY u) X (fun a _ => a.coeff 0) := by
  sorry

end G5

section G6
open Finset Polynomial
variable {s : ℕ}

/-- **`cor:sobol`**: every Sobol' sequence is not quasi-uniform — in every dimension `s ≥ 2`, for all admissible
direction numbers, for any pairwise coprime polynomials with constant term `1` (with or without the van der
Corput coordinate), in the natural order and in the Gray-code order; and there are close pairs:
for every `ε > 0` some prefix `P_m` has two points closer than `ε 2^{-m/s}`. -/
theorem sobol_not_qu (hs : 2 ≤ s) (b : Fin s → (ZMod 2)[X]) (u : Fin s → ℕ → ℕ)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (hco : ∀ c, SobolCoord (b c) (u c)) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < 2 ^ m ∧ w < 2 ^ m ∧ v ≠ w ∧
        euclDist (seqPoint (zcode 2) (sobolGen u) v) (seqPoint (zcode 2) (sobolGen u) w) <
          ε * ((2 : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (seqPoint (zcode 2) (sobolGen u)) ∧
      ¬ IsQuasiUniform (seqPoint (zcode 2) (sobolGen u) ∘ gray) := by
  sorry

/-- **`cor:sobol`**, projections: the projection of a Sobol' sequence to any `s' ≥ 2` of its coordinates
(`ι : Fin s' → Fin s` injective) is not quasi-uniform. -/
theorem sobol_proj {s' : ℕ} (hs' : 2 ≤ s') (b : Fin s → (ZMod 2)[X]) (u : Fin s → ℕ → ℕ)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (hco : ∀ c, SobolCoord (b c) (u c))
    (ι : Fin s' → Fin s) (hι : Function.Injective ι) :
    ¬ IsQuasiUniform (fun v (c' : Fin s') => seqPoint (zcode 2) (sobolGen u) v (ι c')) := by
  sorry

/-- Distinct irreducible polynomials over `𝔽_2` (e.g. Sobol's primitive polynomials) are pairwise coprime. -/
theorem sobol_primitive (b : Fin s → (ZMod 2)[X]) (hirr : ∀ c, Irreducible (b c))
    (hinj : Function.Injective b) : Pairwise fun c c' => IsCoprime (b c) (b c') := by
  sorry

end G6

section G7
open Finset Polynomial
variable {s : ℕ}

/-- Addition in `𝔽_2[z]` is the XOR of the integer indices. -/
theorem polyIdx_add_two (V W : (ZMod 2)[X]) : polyIdx 2 (V + W) = polyIdx 2 V ^^^ polyIdx 2 W := by
  sorry

/-- **`cor:sobol`, the explicit pairs** (van der Corput coordinate as `ĉ`): let `b_ĉ = z`, let `ν ≥ 1` with
`(1 + z) Θ ∣ z^ν - 1` (`carryR`), `ν ≤ 2^j`, `η = E(2^j+1) - ν`, `Q = 2^w`. Then for every Sobol' sequence with these
polynomials (any admissible direction numbers) the indices `ι(V_1)` and `ι(V_1 + D_Q) = ι(V_1) XOR ι(D_Q)`,
`V_1 = ∑_{i = Qη+1}^{L_Q - 1} z^i`, `D_Q = z^{Qη} S_{Qν} Θ^{Q 2^j}`, are distinct and `< 2^{m_Q}`, and the two points
are at Euclidean distance `< √(s+3) 2^{-L_Q}`. -/
theorem sobol_pair (hs : 2 ≤ s) (b : Fin s → (ZMod 2)[X]) (u : Fin s → ℕ → ℕ)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (hco : ∀ c, SobolCoord (b c) (u c)) (ch : Fin s)
    (hch : b ch = X) (ν j η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ X ^ ν - 1) (hνj : ν ≤ 2 ^ j)
    (hη : η + ν = lcmDeg b * (2 ^ j + 1)) (w : ℕ) :
    polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w)) <
        2 ^ (2 ^ w * (s * lcmDeg b * (2 ^ j + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) <
        2 ^ (2 ^ w * (s * lcmDeg b * (2 ^ j + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w)) ≠
        polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) ∧
      polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) =
        polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w)) ^^^ polyIdx 2 (nonquD b ch 1 ν (2 ^ j) η (2 ^ w)) ∧
      euclDist (seqPoint (zcode 2) (sobolGen u) (polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w))))
        (seqPoint (zcode 2) (sobolGen u)
          (polyIdx 2 (nonquV1 b ch 0 (-1) ν η (2 ^ w) + nonquD b ch 1 ν (2 ^ j) η (2 ^ w)))) <
        Real.sqrt (s + 3) / (2 : ℝ) ^ (2 ^ w * lcmDeg b * (2 ^ j + 1)) := by
  sorry

end G7

section G8
open Finset Polynomial
variable {F : Type*} [Field F]

theorem niedY_lin (b : F[X]) (ϑ : ℕ → ℕ → F[X]) : IsLinCoord (niedY b ϑ) := by
  sorry

/-- **`lem:nied`** (first sentence): a Niederreiter coordinate with monic base `b` (degree `≥ 1`) is `b`-adic. -/
theorem nied_isBAdic (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (ϑ : ℕ → ℕ → F[X]) :
    IsBAdic (niedY b ϑ) b := by
  sorry

/-- The coefficient computation of `lem:nied`: for monic `b` of degree `e`, `deg f ≤ (Q+1)e - 2` (or `f = 0`) and
`deg r < e`, the coefficient of `z^{(Q+1)e - 1}` in `(f + b^Q r) mod b^{Q+1}` is `[z^{e-1}] r`. -/
theorem nied_top (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (Q : ℕ) (f r : F[X])
    (hf : f = 0 ∨ f.natDegree + 2 ≤ (Q + 1) * b.natDegree) (hr : r.natDegree < b.natDegree) :
    ((f + b ^ Q * r) %ₘ b ^ (Q + 1)).coeff ((Q + 1) * b.natDegree - 1) = r.coeff (b.natDegree - 1) := by
  sorry

/-- **`lem:nied`** (second sentence, digit computation): if `ϑ_{Q,i} ≡ ϑ̄_i (mod b^{Q+1})` for all `Q` and `i < e`,
`ϑ̄_i = ϑ_{0,i} mod b`, then digit `Q e + i` is `π(a_Q)_i = [z^{-1}] ϑ̄_i a_Q / b`, `a_Q` the `Q`-th `b`-adic digit. -/
theorem nied_digit (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (ϑ : ℕ → ℕ → F[X])
    (hcong : ∀ Q i, i < b.natDegree → b ^ (Q + 1) ∣ ϑ Q i - ϑ 0 i %ₘ b) (V : F[X]) (Q i : ℕ)
    (hi : i < b.natDegree) :
    niedY b ϑ V (Q * b.natDegree + i) = niedPi b (ϑ 0) (badicDigit b V Q) i := by
  sorry

end G8

section G9
open Finset Polynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The pairing of `lem:nied` is nondegenerate**: for irreducible monic `b` of degree `e ≥ 1` over a finite field and
`ϑ_{0,0}, …, ϑ_{0,e-1}` linearly independent modulo `b`, the digit map `π(a)_i = [z^{-1}] ϑ_{0,i} a / b` maps the
polynomials of degree `< e` onto `𝔽^e`. -/
theorem niedPi_onto (b : F[X]) (hb : b.Monic) (hirr : Irreducible b) (he : 1 ≤ b.natDegree)
    (ϑ0 : ℕ → F[X]) (hind : ∀ κ : Fin b.natDegree → F, b ∣ ∑ i, C (κ i) * ϑ0 i → κ = 0) (w : ℕ → F) :
    ∃ a : F[X], a.natDegree < b.natDegree ∧ ∀ i, i < b.natDegree → niedPi b ϑ0 a i = w i := by
  sorry

/-- **`lem:nied`** (second sentence): under the congruence, with `b` monic irreducible and `ϑ_{0,i}` (`i < e`)
linearly independent modulo `b`, the Niederreiter coordinate is a `b`-adic radical inverse with digit map
`π(a)_i = [z^{-1}] ϑ_{0,i} a / b`. -/
theorem nied_radInv (b : F[X]) (hb : b.Monic) (hirr : Irreducible b) (he : 1 ≤ b.natDegree)
    (ϑ : ℕ → ℕ → F[X]) (hcong : ∀ Q i, i < b.natDegree → b ^ (Q + 1) ∣ ϑ Q i - ϑ 0 i %ₘ b)
    (hind : ∀ κ : Fin b.natDegree → F, b ∣ ∑ i, C (κ i) * ϑ 0 i → κ = 0) :
    IsRadInv (niedY b ϑ) b (niedPi b (ϑ 0)) := by
  sorry

/-- The classical Niederreiter coordinate (`ϑ_{Q,i} = z^i`) satisfies the congruence of `lem:nied`. -/
theorem classical_cong (b : F[X]) (hb : b.Monic) (Q i : ℕ) (hi : i < b.natDegree) :
    b ^ (Q + 1) ∣ (fun (_ i : ℕ) => (X : F[X]) ^ i) Q i - (fun (_ i : ℕ) => (X : F[X]) ^ i) 0 i %ₘ b := by
  sorry

/-- `1, z, …, z^{e-1}` are linearly independent modulo `b` (`deg b = e`). -/
theorem classical_ind (b : F[X]) (hb : b.Monic) (he : 1 ≤ b.natDegree) (κ : Fin b.natDegree → F)
    (h : b ∣ ∑ i, C (κ i) * (fun (_ i : ℕ) => (X : F[X]) ^ i) 0 i) : κ = 0 := by
  sorry

end G9

section G10
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- Distinct monic irreducible polynomials are pairwise coprime. -/
theorem monic_irred_coprime {F : Type*} [Field F] (b : Fin s → F[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) :
    Pairwise fun c c' => IsCoprime (b c) (b c') := by
  sorry

/-- **`cor:nied`** (generalized form): let the bases `b_c ∈ 𝔽_p[z]` be distinct monic irreducible, let every
coordinate be a generalized Niederreiter coordinate `niedY b_c ϑ_c` (arbitrary polynomials `ϑ_c`), and let one
coordinate `ĉ` satisfy `ϑ_{ĉ,Q,i} ≡ ϑ̄_{ĉ,i} (mod b_ĉ^{Q+1})` with `ϑ_{ĉ,0,i}` linearly independent modulo `b_ĉ`.
Then the sequence is not quasi-uniform (and has close pairs at prefixes `P_m`). -/
theorem niedGen_not_qu (hs : 2 ≤ s) (b : Fin s → (ZMod p)[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) (ϑ : Fin s → ℕ → ℕ → (ZMod p)[X])
    (ch : Fin s) (hcong : ∀ Q i, i < (b ch).natDegree → b ch ^ (Q + 1) ∣ ϑ ch Q i - ϑ ch 0 i %ₘ b ch)
    (hind : ∀ κ : Fin (b ch).natDegree → ZMod p, b ch ∣ ∑ i, C (κ i) * ϑ ch 0 i → κ = 0) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (linPt p (fun c => niedY (b c) (ϑ c)) v) (linPt p (fun c => niedY (b c) (ϑ c)) w) <
          ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPt p fun c => niedY (b c) (ϑ c)) := by
  sorry

/-- **`cor:nied`** (classical): every classical Niederreiter sequence over `𝔽_p` (`s ≥ 2`, distinct monic
irreducible bases, `ϑ_{c,Q,i} = z^i`, natural identification) is not quasi-uniform. -/
theorem nied_not_qu (hs : 2 ≤ s) (b : Fin s → (ZMod p)[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) :
    ¬ IsQuasiUniform (linPt p fun c => niedY (b c) (fun _ i => X ^ i)) := by
  sorry

end G10

section G11
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}
variable (a : Fin s → ZMod p) (ch c1 : Fin s)

/-- The first `Q = p^w` Taylor digits of `D` at `a_ĉ` are all `1`. -/
theorem faureD_taylor (ha : Function.Injective a) (hc1 : c1 ≠ ch) (h1 : a c1 = a ch + 1) (w : ℕ)
    (hw : 1 ≤ w) (n : ℕ) (hn : n < p ^ w) : (taylor (a ch) (faureD a ch c1 (p ^ w))).coeff n = 1 := by
  sorry

theorem faureD_dvd_c1 (h1 : a c1 = a ch + 1) (Q : ℕ) : (X - C (a c1)) ^ (Q - 1) ∣ faureD a ch c1 Q := by
  sorry

theorem faureD_dvd (c : Fin s) (hc : c ≠ ch) (hc1 : c ≠ c1) (Q : ℕ) :
    (X - C (a c)) ^ Q ∣ faureD a ch c1 Q := by
  sorry

theorem faureD_natDegree (hc1 : c1 ≠ ch) (Q : ℕ) (hQ : 1 ≤ Q) :
    (faureD a ch c1 Q).natDegree ≤ (s - 1) * Q - 1 := by
  sorry

end G11

section G12
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`rem:faurerate`**: for the unscrambled frame with two places one apart (`a_{c₁} = a_ĉ + 1`) and `Q = p^w`
(`w ≥ 1`), the indices of `V_1` and `V_1 + D` are distinct and `< N = p^{(s-1)Q}`, and the two points are at
Euclidean distance `< √(p² + s + 2) p^{-Q} = √(p² + s + 2) N^{-1/(s-1)}`. -/
theorem faurerate (a : Fin s → ZMod p) (ha : Function.Injective a) (ch c1 : Fin s) (hc1 : c1 ≠ ch)
    (h1 : a c1 = a ch + 1) (w : ℕ) (hw : 1 ≤ w) :
    polyIdx p (faureV1 a ch (p ^ w)) < p ^ ((s - 1) * p ^ w) ∧
      polyIdx p (faureV1 a ch (p ^ w) + faureD a ch c1 (p ^ w)) < p ^ ((s - 1) * p ^ w) ∧
      polyIdx p (faureV1 a ch (p ^ w)) ≠ polyIdx p (faureV1 a ch (p ^ w) + faureD a ch c1 (p ^ w)) ∧
      euclDist (seqPoint (zcode p) (fun c n k => pas (a c) n k) (polyIdx p (faureV1 a ch (p ^ w))))
        (seqPoint (zcode p) (fun c n k => pas (a c) n k)
          (polyIdx p (faureV1 a ch (p ^ w) + faureD a ch c1 (p ^ w)))) <
        Real.sqrt ((p : ℝ) ^ 2 + s + 2) / (p : ℝ) ^ (p ^ w) := by
  sorry

/-- **`rem:faurerate`** (separation): `δ(P_{(s-1)Q}) < √(p² + s + 2) N^{-1/(s-1)}` with `N = p^{(s-1)Q}`
(`N^{-1/(s-1)} = p^{-Q}`). -/
theorem faurerate_sep (a : Fin s → ZMod p) (ha : Function.Injective a) (ch c1 : Fin s) (hc1 : c1 ≠ ch)
    (h1 : a c1 = a ch + 1) (w : ℕ) (hw : 1 ≤ w) :
    sepDistIdx (seqPoint (zcode p) (fun c n k => pas (a c) n k)) (p ^ ((s - 1) * p ^ w)) <
      Real.sqrt ((p : ℝ) ^ 2 + s + 2) / (p : ℝ) ^ (p ^ w) := by
  sorry

end G12

end GeoSeq
