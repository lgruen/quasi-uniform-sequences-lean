/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/

module
public import GeoSeq.V10_3Fields

@[expose] public section

/-!
# Statements: stage V10_3 (paper V4, stage V10-3)

Prime-power bases (stage V10-3): explicit models of `F_q = F_p[x]/(f)` with the power-basis code; `prop:primepower` (soundness of the one-digit certificate for every finite field and every digit code, proved once; the 13 rows of `tab:primepower` by kernel evaluation); `thm:coverage` with the prime-power rows; `sec:fail` over `F_q` with any digit code having a carry pair (`lem:carrypair`, `thm:nonqu`, `eq:carrydigit` for every natural identification, `cor:unscrambled`, `cor:faure`, `cor:nied` for prime powers).
PROVED (`GeoSeq/V10_3Beta.lean`, `GeoSeq/V10_3Cov.lean`, `GeoSeq/V10_3Fail.lean`, `GeoSeq/V10_3Rows.lean`); generated verbatim from the proof files' signatures by `scripts/gen_v10_statements.py V10_3`
(definitions in `GeoSeq/V10_3Fields.lean`). Paper: V4 (`paper/sections/10-frames.tex, 03-fail.tex, 02-prelim.tex, A-machinery.tex`); label → Lean map in
the formalization notes of the research repository, plan the formalization notes of the research repository (stage V10-3). Configuration:
`comparatorGeoSeqV10_3.json`.
-/

namespace GeoSeq

section G0
open Finset

/-- Every vector with entries in `L` is listed by `vecsOf`. -/
theorem mem_vecsOf {α : Type*} (L : List α) (n : ℕ) (v : Fin n → α) (h : ∀ i, v i ∈ L) : v ∈ vecsOf n L := by
  sorry

/-- Every vector with entry `i` in `L i` is listed by `vecsOfL`. -/
theorem mem_vecsOfL {α : Type*} (n : ℕ) (L : Fin n → List α) (v : Fin n → α) (h : ∀ i, v i ∈ L i) :
    v ∈ vecsOfL n L := by
  sorry

/-- `smul3 e x = e x` for `e ∈ {-1, 0, 1}`. -/
theorem smul3_eq {F : Type*} [Ring F] (e : ℤ) (he : -1 ≤ e ∧ e ≤ 1) (x : F) : smul3 e x = ((e : ℤ) : F) * x := by
  sorry

/-- What the certificate says, one step at a time. -/
theorem ppCheck_spec {F : Type*} [CommRing F] [DecidableEq F] {enc : F → ℕ} {q : ℕ} {elems Δs : List F} {n : ℕ}
    {w : Fin n → F} {prods : Fin n → List F} {S : List F} {N : ℕ}
    (hchk : ppCheck enc q elems Δs n w prods S N = true) (es : ℤ) (hes : -1 ≤ es ∧ es ≤ 1)
    (e' : Fin n → ℤ) (he' : ∀ i, -1 ≤ e' i ∧ e' i ≤ 1) (Δ : Fin n → F) (hΔ : ∀ i, Δ i ∈ Δs)
    (hnz : ¬ (es = 0 ∧ ∀ i, e' i = 0)) (r : F) (hr : r ∈ elems) :
    N + 1 ≤ ((es * q + (enc (r + ∑ i, ((e' i : ℤ) : F) * w i * Δ i) : ℤ) - enc r).natAbs) := by
  sorry

/-- `q f_1(e, σ) ≥ N` (`gapNum` with one digit, any digit code) from the bound at every digit. -/
theorem gapNum_one_ge {F : Type*} [CommRing F] [Fintype F] [DecidableEq F] {q : ℕ} (D : DigitCode F q)
    (e : ℤ) (σ : Fin 1 → F) (N : ℕ)
    (h : ∀ r : F, N + 1 ≤ ((e * q + ((D.enc (r + σ 0) : ℕ) : ℤ) - ((D.enc r : ℕ) : ℤ)).natAbs)) :
    N ≤ gapNum D 1 e σ := by
  sorry

end G0

section G1
open Finset
variable {F : Type*} [Field F] {s : ℕ}

/-- The carry change of the staggered coordinate (proof of `prop:primepower`): with the one-digit responses
`D(0) = 0` and `D(l)[c⋆][c'] = k'_{c'}` (`l ≥ 1`), `δ_0(l, y)[c⋆][c'] = Δ k'_{c'}` with `Δ = Δ(y)` for `l = 1`
and `Δ = Δ(ȳ)` for `l ≥ 2` (`eq:carrychange`). -/
theorem carryChange_const {q : ℕ} [NeZero q] (D : DigitCode F q) (Dr : ℕ → ℕ → Fin s → Fin s → F)
    (cs c' : Fin s) (kc : F) (hDr : ∀ l, Dr 0 l cs c' = if l = 0 then 0 else kc) (l : ℕ) (hl : 1 ≤ l) (y : F) :
    carryChange D Dr 0 l y cs c' = (if l = 1 then digInc D y else digInc D (topDigit D)) * kc := by
  sorry

end G1

section G2
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {q : ℕ} [NeZero q]

/-- **`prop:primepower`, separation** (soundness of the certificate, every finite field and every digit code). Let
`s = n + 1`, `q ≥ 4`, the places distinct, `θ, μ⋆ ≠ 0`, the weights `k_{c⋆.succAbove i} = w_i ≠ 0`, `elems` a list of
all digits, `Δs` a list containing every digit increment `Δ(y)` (`rem:F4carry`), and `ppCheck … N = true`. Then
`sep(P_{sK}) ≥ N/q` for every `K ≥ 1`. -/
theorem pp_sep (D : DigitCode F q) (hq : 4 ≤ q) {n : ℕ} (a : Fin (n + 1) → F) (ha : Function.Injective a)
    (θ : F) (hθ : θ ≠ 0) (cs : Fin (n + 1)) (μs : F) (hμ : μs ≠ 0) (k : Fin (n + 1) → F) (w : Fin n → F)
    (hw : ∀ i, w i ≠ 0) (hk : ∀ i, k (cs.succAbove i) = w i) (elems Δs : List F) (hel : ∀ y, y ∈ elems)
    (hΔ : ∀ y, digInc D y ∈ Δs) (prods : Fin n → List F) (S : List F) (N : ℕ)
    (hchk : ppCheck (fun y => (D.enc y : ℕ)) q elems Δs n w prods S N = true)
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel q (n + 1) K (seqPoint D (resStar a θ cs μs k)) ((N : ℝ) / q) := by
  sorry

/-- **`prop:primepower`** (soundness, the whole conclusion): with the hypotheses of `pp_sep` and `N ≥ 1`, the staggered
residue sequence over `F` is a digital `(0,s)`-sequence with `sep(P_{sK}) ≥ N/q` for every `K ≥ 1`,
`δ(P_{[N']}) ≥ (N/q²) N'^{-1/s}` for every `N' ≥ 2`, and quasi-uniform. -/
theorem primepower_of_check (D : DigitCode F q) (hq : 4 ≤ q) {n : ℕ} (a : Fin (n + 1) → F)
    (ha : Function.Injective a) (θ : F) (hθ : θ ≠ 0) (cs : Fin (n + 1)) (μs : F) (hμ : μs ≠ 0)
    (k : Fin (n + 1) → F) (w : Fin n → F) (hw : ∀ i, w i ≠ 0) (hk : ∀ i, k (cs.succAbove i) = w i)
    (elems Δs : List F) (hel : ∀ y, y ∈ elems) (hΔ : ∀ y, digInc D y ∈ Δs) (prods : Fin n → List F) (S : List F) (N : ℕ)
    (hN : 1 ≤ N) (hchk : ppCheck (fun y => (D.enc y : ℕ)) q elems Δs n w prods S N = true) :
    PPConcl D (n + 1) (resStar a θ cs μs k) ((N : ℝ) / q) := by
  sorry

end G2

section G3
open Finset Polynomial
variable {F : Type*} [Field F] {q : ℕ} [NeZero q]

/-- The coefficients of the index polynomial are the index digits. -/
theorem coeff_idxPolyD (D : DigitCode F q) (n k : ℕ) :
    (idxPolyD D n).coeff k = if k < n + 1 then idxDigit D n k else 0 := by
  sorry

/-- `deg idxPolyD D n ≤ n`. -/
theorem natDegree_idxPolyD (D : DigitCode F q) (n : ℕ) : (idxPolyD D n).natDegree ≤ n := by
  sorry

/-- The base-`q` digits of `ι(V)` are the codes of the coefficients of `V`. -/
theorem polyIdxD_digit (D : DigitCode F q) (V : F[X]) (k : ℕ) :
    polyIdxD D V / q ^ k % q = if k < V.natDegree + 1 then (D.enc (V.coeff k) : ℕ) else 0 := by
  sorry

/-- `idxPolyD D (ι(V)) = V`. -/
theorem idxPolyD_polyIdxD (D : DigitCode F q) (hq : 2 ≤ q) (V : F[X]) : idxPolyD D (polyIdxD D V) = V := by
  sorry

theorem polyIdxD_lt (D : DigitCode F q) (V : F[X]) {m : ℕ} (hV : V.natDegree < m) : polyIdxD D V < q ^ m := by
  sorry

theorem polyIdxD_injective (D : DigitCode F q) (hq : 2 ≤ q) : Function.Injective (polyIdxD D) := by
  sorry

/-- The point with index `ι(V)` reads the digits of `Y_c(V)`. -/
theorem linPtD_polyIdxD {s : ℕ} (D : DigitCode F q) (hq : 2 ≤ q) (Y : Fin s → F[X] → ℕ → F) (V : F[X])
    (c : Fin s) :
    linPtD D Y (polyIdxD D V) c = ∑' j : ℕ, ((D.enc (Y c V j) : ℕ) : ℝ) / (q : ℝ) ^ (j + 1) := by
  sorry

/-- The coordinates of the points lie in `[0, 1]`. -/
theorem linPtD_mem {s : ℕ} (D : DigitCode F q) (hq : 2 ≤ q) (Y : Fin s → F[X] → ℕ → F) (n : ℕ) (c : Fin s) :
    0 ≤ linPtD D Y n c ∧ linPtD D Y n c ≤ 1 := by
  sorry

end G3

section G4
open Finset Polynomial
variable {F : Type*} [Field F] {q : ℕ}

/-- `enc x = 0 ↔ x = 0`. -/
theorem enc_eq_zero_iff (D : DigitCode F q) (x : F) : (D.enc x : ℕ) = 0 ↔ x = 0 := by
  sorry

end G4

section G5
open Finset Polynomial
variable {F : Type*} [Field F] {q s : ℕ} [NeZero q]

/-- **`lem:carrypair`** over `𝔽_q` with a general digit code `D` (`q ≥ 2`) having a carry pair `(ȳ, y°)`
(`eq:carrydigit`). Coordinate `ĉ` is a `b`-adic radical inverse with digit map `π`, every other coordinate `c` is
`b_c`-adic; `deg g, deg g̃, deg g' < e` with `π(g) = -ȳ(1, …, 1)`, `π(g̃) = (y°, ȳ, …, ȳ)`, `π(g') = ȳ(1, …, 1)`;
`D ≠ 0`, `η < λ`, (i) `D ≡ g b^η S_{λ-η} (mod b^λ)`, (ii) `b_c^{j_c} ∣ D` with `e_c j_c ≥ L = eλ`, (iii) `deg D < m`.
Then the indices `ι(V_1)`, `ι(V_1 + D)` are `< q^m`, distinct, and the points are at distance `< √(s+3) q^{-L}`. -/
theorem carrypairD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : F[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = -yb)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then yo else yb)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = yb)
    (D : F[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    polyIdxD Dc (carryV1 (b ch) gt g' η l) < q ^ m ∧
      polyIdxD Dc (carryV1 (b ch) gt g' η l + D) < q ^ m ∧
      polyIdxD Dc (carryV1 (b ch) gt g' η l) ≠ polyIdxD Dc (carryV1 (b ch) gt g' η l + D) ∧
      euclDist (linPtD Dc Y (polyIdxD Dc (carryV1 (b ch) gt g' η l)))
        (linPtD Dc Y (polyIdxD Dc (carryV1 (b ch) gt g' η l + D))) <
        Real.sqrt (s + 3) / (q : ℝ) ^ ((b ch).natDegree * l) := by
  sorry

end G5

section G6
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- `thm:nonqu`, existence of `ν` and `k`, over every finite field. -/
theorem nonqu_existsD [Finite F] (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s) :
    ∃ ν k η : ℕ, 1 ≤ ν ∧ 1 ≤ k ∧ carryR b ch ∣ b ch ^ ν - 1 ∧ b ch ^ ν ∣ thetaP b ch ^ k - 1 ∧
      η + ν = lcmDeg b / (b ch).natDegree * (k + 1) := by
  sorry

end G6

section G7
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable {p : ℕ} [Fact p.Prime] [CharP F p] {q : ℕ} [NeZero q]

/-- **`thm:nonqu`** over `𝔽_q` (characteristic `p`, any digit code with a carry pair), the explicit pairs: for
`Q = p^w`, `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}`, the indices `ι(V_1)`, `ι(V_1 + D_Q)` are `< q^{m_Q}`,
`m_Q = Q(sE(k+1) - (s-1)E)`, distinct, and the points are at distance `< √(s+3) q^{-L_Q}`, `L_Q = QE(k+1)`. -/
theorem nonqu_pairD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : F[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = -yb)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then yo else yb)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = yb)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w)) <
        q ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) <
        q ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w)) ≠
        polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) ∧
      euclDist (linPtD Dc Y (polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w))))
        (linPtD Dc Y (polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)))) <
        Real.sqrt (s + 3) / (q : ℝ) ^ (p ^ w * lcmDeg b * (k + 1)) := by
  sorry

end G7

section G8
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable {p : ℕ} [Fact p.Prime] [CharP F p] {q : ℕ} [NeZero q]
include p

/-- **`thm:nonqu`** over `𝔽_q` (every finite field `F` of characteristic `p`, `q ≥ 2` elements read through a digit
code with a carry pair, e.g. the natural identification `carryPair_pb`). Let `s ≥ 2`, the bases `b_c ∈ 𝔽_q[z]`
pairwise coprime of degrees `≥ 1`, coordinate `ĉ` a `b_ĉ`-adic radical inverse, every other coordinate `b_c`-adic.
Then for every `ε > 0` some prefix `P_m` contains two points at distance `< ε q^{-m/s}`, and the sequence is not
quasi-uniform. -/
theorem nonqu_code [Finite F] (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo)
    (hs : 2 ≤ s) (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < q ^ m ∧ w < q ^ m ∧ v ≠ w ∧
        euclDist (linPtD Dc Y v) (linPtD Dc Y w) < ε * ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPtD Dc Y) := by
  sorry

end G8

section G9
open Finset Polynomial
variable {F : Type*} [AddCommGroup F] {q : ℕ}

/-- `∑_{i<d} (p-1) p^i + 1 = p^d`. -/
theorem geom_aux (p : ℕ) (hp : 1 ≤ p) (d : ℕ) : (∑ i : Fin d, (p - 1) * p ^ (i : ℕ)) + 1 = p ^ d := by
  sorry

/-- `val(-1) = p - 1` in `ℤ/pℤ`. -/
theorem val_neg_one_eq {p : ℕ} [NeZero p] : (-1 : ZMod p).val = p - 1 := by
  sorry

/-- **`eq:carrydigit` for every natural identification**: if `enc y = ∑_i φ(y)_i p^i` for an additive bijection
`φ : F ≃+ 𝔽_p^{d+1}` (`p ≥ 2`), then `ȳ = φ⁻¹(-1, …, -1)` has code `p^{d+1} - 1 = q - 1`,
`y° = φ⁻¹(-1, …, -1, 0)` has code `p^d - 1 = q/p - 1`, and `(ȳ, y°)` is a carry pair: `enc(y° - ȳ) = p^d`. -/
theorem carryPair_nat {p : ℕ} [NeZero p] (hp : 2 ≤ p) (D : DigitCode F q) (d : ℕ) (φ : F ≃+ (Fin (d + 1) → ZMod p))
    (hnat : IsNatCode D d φ) :
    (D.enc (φ.symm fun _ => -1) : ℕ) = p ^ (d + 1) - 1 ∧
      (D.enc (φ.symm fun i => if (i : ℕ) = d then 0 else -1) : ℕ) = p ^ d - 1 ∧
      IsCarryPair D (φ.symm fun _ => -1) (φ.symm fun i => if (i : ℕ) = d then 0 else -1) := by
  sorry

/-- The power-basis code of `PF p d fc` is a natural identification (`φ = PF.v`, `PF.vEquiv`). -/
theorem PF.code_isNat {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [Fact p.Prime] [NeZero p] :
    IsNatCode (PF.code : DigitCode (PF p d fc) (p ^ (d + 1))) d PF.vEquiv := by
  sorry

/-- **`eq:carrydigit` for the power-basis code** of every model `PF p d fc` (`sec:primepower`):
`ȳ = (-1, …, -1)` (code `q - 1`), `y° = (-1, …, -1, 0)` (code `q/p - 1`) is a carry pair. -/
theorem carryPair_pb {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [Fact p.Prime] [NeZero p] :
    IsCarryPair (PF.code : DigitCode (PF p d fc) (p ^ (d + 1))) ⟨fun _ => -1⟩
      ⟨fun i => if (i : ℕ) = d then 0 else -1⟩ := by
  sorry

end G9

section G10
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}

/-- The rows of the generator matrices read the index polynomial (any digit code). -/
theorem genY_idxD {q : ℕ} [NeZero q] (Dc : DigitCode F q) (C : Gen s F) (c : Fin s) (v n : ℕ) :
    genY C c (idxPolyD Dc v) n = seqDigit Dc C v c n := by
  sorry

/-- A generator-matrix sequence over `𝔽_q` is the linear-coordinate sequence of its rows (any digit code). -/
theorem seqPoint_eq_linPtD {q : ℕ} [NeZero q] (Dc : DigitCode F q) (C : Gen s F) :
    seqPoint Dc C = linPtD Dc (genY C) := by
  sorry

end G10

section G11
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p] {q : ℕ} [NeZero q]
include p

/-- **`cor:unscrambled`** over `𝔽_q` (linear-coordinate form, any digit code with a carry pair). -/
theorem unscrambledD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) (μ : F) (hμ : μ ≠ 0) (L : Fin s → ℕ → ℕ → F) :
    ¬ IsQuasiUniform (linPtD Dc fun c => if c = ch then fun V n => μ * Y ch V n else scrY (L c) (Y c)) := by
  sorry

/-- **`cor:unscrambled`**, frames, over `𝔽_q` (any digit code with a carry pair): for distinct places the scrambled
frame `C_ĉ = μ diag(β^n) P_{a_ĉ}`, `C_c = L_c P_{a_c}` (`c ≠ ĉ`) is not quasi-uniform, for all `μ, β ∈ 𝔽_q^*`. -/
theorem unscrambled_frameD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo)
    (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (ch : Fin s)
    (μ β : F) (hμ : μ ≠ 0) (hβ : β ≠ 0) (L : Fin s → ℕ → ℕ → F) :
    ¬ IsQuasiUniform (seqPoint Dc (scrFrameF a ch μ β L)) := by
  sorry

/-- **`cor:faure` for prime powers**: for every finite field `𝔽_q` of characteristic `p`, every digit code with a carry
pair (every natural identification, `carryPair_nat`), every `s ≥ 2` and all distinct places `a_c ∈ 𝔽_q`, the
unscrambled frame `(P_{a_0}, …, P_{a_{s-1}})` is not quasi-uniform. -/
theorem faure_code (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (a : Fin s → F) (ha : Function.Injective a) :
    ¬ IsQuasiUniform (seqPoint Dc (fun c n k => pas (a c) n k)) := by
  sorry

end G11

section G12
open Finset Polynomial
variable {F : Type*} [Field F] {s : ℕ}
variable [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p] {q : ℕ} [NeZero q]
variable [DecidableEq F]
include p

/-- **`cor:nied` for prime powers** (generalized form): distinct monic irreducible bases `b_c ∈ 𝔽_q[z]`,
generalized Niederreiter coordinates, one coordinate `ĉ` with `ϑ_{ĉ,Q,i} ≡ ϑ̄_{ĉ,i} (mod b_ĉ^{Q+1})` and
`ϑ_{ĉ,0,i}` linearly independent modulo `b_ĉ`; digits read through any code with a carry pair. -/
theorem niedGen_not_quD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo)
    (hs : 2 ≤ s) (b : Fin s → F[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) (ϑ : Fin s → ℕ → ℕ → F[X])
    (ch : Fin s) (hcong : ∀ Q i, i < (b ch).natDegree → b ch ^ (Q + 1) ∣ ϑ ch Q i - ϑ ch 0 i %ₘ b ch)
    (hind : ∀ κ : Fin (b ch).natDegree → F, b ch ∣ ∑ i, C (κ i) * ϑ ch 0 i → κ = 0) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < q ^ m ∧ w < q ^ m ∧ v ≠ w ∧
        euclDist (linPtD Dc (fun c => niedY (b c) (ϑ c)) v) (linPtD Dc (fun c => niedY (b c) (ϑ c)) w) <
          ε * ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPtD Dc fun c => niedY (b c) (ϑ c)) := by
  sorry

/-- **`cor:nied` for prime powers** (classical): every classical Niederreiter sequence over `𝔽_q` (`s ≥ 2`, distinct
monic irreducible bases, `ϑ_{c,Q,i} = z^i`, digits read through any code with a carry pair, in particular every
natural identification) is not quasi-uniform. -/
theorem nied_not_quD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (b : Fin s → F[X]) (hm : ∀ c, (b c).Monic) (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) :
    ¬ IsQuasiUniform (linPtD Dc fun c => niedY (b c) (fun _ i => X ^ i)) := by
  sorry

end G12

section G13
open Finset

/-- `s2_q8`: the digit increments of the power-basis code of `GF8` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q8 : ∀ y : GF8, digInc PF.code y ∈ PF.pbDelta 2 2 ![1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q8`** (`s = 2`, `q = 8`, `f = x^3+x+1`, weights `(2)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF8` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 1/8` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/8²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q8 (a : Fin 2 → GF8) (ha : Function.Injective a) (θ : GF8) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF8) (hμ : μs ≠ 0) (k : Fin 2 → GF8) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 2] : Fin 1 → GF8) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (1 / 8) := by
  sorry

/-- `s2_q9`: the digit increments of the power-basis code of `GF9` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q9 : ∀ y : GF9, digInc PF.code y ∈ PF.pbDelta 3 1 ![1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q9`** (`s = 2`, `q = 9`, `f = x^2+1`, weights `(3)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF9` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 1/9` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/9²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q9 (a : Fin 2 → GF9) (ha : Function.Injective a) (θ : GF9) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF9) (hμ : μs ≠ 0) (k : Fin 2 → GF9) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 3] : Fin 1 → GF9) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (1 / 9) := by
  sorry

/-- `s2_q16`: the digit increments of the power-basis code of `GF16` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q16 : ∀ y : GF16, digInc PF.code y ∈ PF.pbDelta 2 3 ![1, 1, 0, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q16`** (`s = 2`, `q = 16`, `f = x^4+x+1`, weights `(2)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF16` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 1/16` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/16²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q16 (a : Fin 2 → GF16) (ha : Function.Injective a) (θ : GF16) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF16) (hμ : μs ≠ 0) (k : Fin 2 → GF16) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 2] : Fin 1 → GF16) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (1 / 16) := by
  sorry

/-- `s2_q25`: the digit increments of the power-basis code of `GF25` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q25 : ∀ y : GF25, digInc PF.code y ∈ PF.pbDelta 5 1 ![2, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q25`** (`s = 2`, `q = 25`, `f = x^2+2`, weights `(10)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF25` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 5/25` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (5/25²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q25 (a : Fin 2 → GF25) (ha : Function.Injective a) (θ : GF25) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF25) (hμ : μs ≠ 0) (k : Fin 2 → GF25) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 10] : Fin 1 → GF25) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (5 / 25) := by
  sorry

/-- `s2_q27`: the digit increments of the power-basis code of `GF27` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q27 : ∀ y : GF27, digInc PF.code y ∈ PF.pbDelta 3 2 ![1, 2, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q27`** (`s = 2`, `q = 27`, `f = x^3+2x+1`, weights `(11)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF27` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 3/27` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (3/27²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q27 (a : Fin 2 → GF27) (ha : Function.Injective a) (θ : GF27) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF27) (hμ : μs ≠ 0) (k : Fin 2 → GF27) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 11] : Fin 1 → GF27) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (3 / 27) := by
  sorry

/-- `s2_q49`: the digit increments of the power-basis code of `GF49` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s2_q49 : ∀ y : GF49, digInc PF.code y ∈ PF.pbDelta 7 1 ![1, 0] := by
  sorry

/-- **`prop:primepower`, row `s2_q49`** (`s = 2`, `q = 49`, `f = x^2+1`, weights `(21)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF49` with the power-basis code is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ 17/49` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (17/49²) N^{-1/2}`, and quasi-uniform. -/
theorem primepower_s2_q49 (a : Fin 2 → GF49) (ha : Function.Injective a) (θ : GF49) (hθ : θ ≠ 0) (cs : Fin 2)
    (μs : GF49) (hμ : μs ≠ 0) (k : Fin 2 → GF49) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 21] : Fin 1 → GF49) i) :
    PPConcl PF.code 2 (resStar a θ cs μs k) (17 / 49) := by
  sorry

/-- `s3_q25`: the digit increments of the power-basis code of `GF25` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q25 : ∀ y : GF25, digInc PF.code y ∈ PF.pbDelta 5 1 ![2, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q25`** (`s = 3`, `q = 25`, `f = x^2+2`, weights `(7, 2)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF25` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 1/25` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/25²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q25 (a : Fin 3 → GF25) (ha : Function.Injective a) (θ : GF25) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF25) (hμ : μs ≠ 0) (k : Fin 3 → GF25) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 7, PF.dec 2] : Fin 2 → GF25) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (1 / 25) := by
  sorry

/-- `s3_q32`: the digit increments of the power-basis code of `GF32` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q32 : ∀ y : GF32, digInc PF.code y ∈ PF.pbDelta 2 4 ![1, 1, 1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q32`** (`s = 3`, `q = 32`, `f = x^5+x^3+x^2+x+1`, weights `(12, 2)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF32` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 1/32` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/32²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q32 (a : Fin 3 → GF32) (ha : Function.Injective a) (θ : GF32) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF32) (hμ : μs ≠ 0) (k : Fin 3 → GF32) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 12, PF.dec 2] : Fin 2 → GF32) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (1 / 32) := by
  sorry

/-- `s3_q49`: the digit increments of the power-basis code of `GF49` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q49 : ∀ y : GF49, digInc PF.code y ∈ PF.pbDelta 7 1 ![1, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q49`** (`s = 3`, `q = 49`, `f = x^2+1`, weights `(21, 7)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF49` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 5/49` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (5/49²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q49 (a : Fin 3 → GF49) (ha : Function.Injective a) (θ : GF49) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF49) (hμ : μs ≠ 0) (k : Fin 3 → GF49) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 21, PF.dec 7] : Fin 2 → GF49) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (5 / 49) := by
  sorry

/-- `s3_q64`: the digit increments of the power-basis code of `GF64` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q64 : ∀ y : GF64, digInc PF.code y ∈ PF.pbDelta 2 5 ![1, 1, 0, 0, 0, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q64`** (`s = 3`, `q = 64`, `f = x^6+x+1`, weights `(42, 23)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF64` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 2/64` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (2/64²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q64 (a : Fin 3 → GF64) (ha : Function.Injective a) (θ : GF64) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF64) (hμ : μs ≠ 0) (k : Fin 3 → GF64) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 42, PF.dec 23] : Fin 2 → GF64) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (2 / 64) := by
  sorry

/-- `s3_q81`: the digit increments of the power-basis code of `GF81` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q81 : ∀ y : GF81, digInc PF.code y ∈ PF.pbDelta 3 3 ![2, 1, 0, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q81`** (`s = 3`, `q = 81`, `f = x^4+x+2`, weights `(17, 3)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF81` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 1/81` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (1/81²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q81 (a : Fin 3 → GF81) (ha : Function.Injective a) (θ : GF81) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF81) (hμ : μs ≠ 0) (k : Fin 3 → GF81) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 17, PF.dec 3] : Fin 2 → GF81) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (1 / 81) := by
  sorry

/-- `s3_q121`: the digit increments of the power-basis code of `GF121` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q121 : ∀ y : GF121, digInc PF.code y ∈ PF.pbDelta 11 1 ![1, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q121`** (`s = 3`, `q = 121`, `f = x^2+1`, weights `(55, 22)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF121` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 19/121` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (19/121²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q121 (a : Fin 3 → GF121) (ha : Function.Injective a) (θ : GF121) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF121) (hμ : μs ≠ 0) (k : Fin 3 → GF121) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 55, PF.dec 22] : Fin 2 → GF121) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (19 / 121) := by
  sorry

/-- `s3_q125`: the digit increments of the power-basis code of `GF125` lie in `{1, 1+x, …}`. -/
theorem pp_delta_s3_q125 : ∀ y : GF125, digInc PF.code y ∈ PF.pbDelta 5 2 ![1, 1, 0] := by
  sorry

/-- **`prop:primepower`, row `s3_q125`** (`s = 3`, `q = 125`, `f = x^3+x+1`, weights `(35, 26)`): for all distinct places,
`θ, μ⋆ ≠ 0`, every staggered coordinate `c⋆` and the weights in the order `c⋆.succAbove`, the staggered residue
sequence over `GF125` with the power-basis code is a digital `(0,3)`-sequence with `sep(P_{3K}) ≥ 8/125` for every
`K ≥ 1`, `δ(P_{[N]}) ≥ (8/125²) N^{-1/3}`, and quasi-uniform. -/
theorem primepower_s3_q125 (a : Fin 3 → GF125) (ha : Function.Injective a) (θ : GF125) (hθ : θ ≠ 0) (cs : Fin 3)
    (μs : GF125) (hμ : μs ≠ 0) (k : Fin 3 → GF125) (hk : ∀ i, k (cs.succAbove i) = (![PF.dec 35, PF.dec 26] : Fin 2 → GF125) i) :
    PPConcl PF.code 3 (resStar a θ cs μs k) (8 / 125) := by
  sorry

end G13

section G14

/-- The conclusion of `prop:primepower` gives `Covered` on the full levels (`lem:prefix`). -/
theorem covered_of_concl {R : Type*} [CommRing R] {q : ℕ} [NeZero q] (D : DigitCode R q) (hq : 2 ≤ q) (s : ℕ)
    (hs : 1 ≤ s) (C : Gen s R) (β : ℝ) (hβ : 0 < β) (h : PPConcl D s C β) : Covered D s C (levFull s) := by
  sorry

/-- Distinct codes below `q` give distinct elements (the places `a_c = dec c`). -/
theorem PF.dec_fin_injective {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [NeZero p] {s : ℕ} (hs : s ≤ p ^ (d + 1)) :
    Function.Injective (fun c : Fin s => (PF.dec (c : ℕ) : PF p d fc)) := by
  sorry

/-- **`thm:coverage`, the prime-power rows** of (a) (`q = 8, 9, 16, 25, 27, 49`, `s = 2`) and (b)
(`q = 25, 32, 49, 64, 81, 121, 125`, `s = 3`), full levels `sℕ` (`prop:primepower`, `tab:primepower`): explicit
staggered residue sequences over the power-basis models `GF<q>` (places `dec 0, …, dec (s-1)`, `θ = μ⋆ = 1`,
`c⋆ = s - 1`, the weights of the table). -/
theorem coverage_pp_rows :
    ((∃ C : Gen 2 GF8, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF9, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF16, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF25, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF27, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF49, Covered PF.code 2 C (levFull 2))) ∧
    ((∃ C : Gen 3 GF25, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF32, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF49, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF64, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF81, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF121, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF125, Covered PF.code 3 C (levFull 3))) := by
  sorry

/-- **`thm:coverage`** (a)-(e) with the prime-power rows, modular form: the hypotheses are those of
`coverage_of_parts` (V9-9; the computer-assisted statements of `thm:S3`, `thm:K4`, `thm:S4` and `Blk5CA`, each
compared in its own configuration). -/
theorem coverage_pp_of_parts (hS3n : IsSeq0 (zcode 3) S3gen)
    (hS3s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 3 3 K (seqPoint (zcode 3) S3gen) (Real.sqrt 134917 / 6561))
    (hK4n : IsSeq0 f4code K4gen)
    (hK4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 3 K (seqPoint f4code K4gen) (Real.sqrt 54774953 / 65536))
    (hS4n : IsSeq0 f4code S4gen)
    (hS4s : ∀ K : ℕ, 1 ≤ K → SepAtLevel 4 4 K (seqPoint f4code S4gen) (Real.sqrt 952 / 1024)) (hca : Blk5CA) :
    ((∀ (p : ℕ) [Fact p.Prime], ∃ C : Gen 2 (ZMod p), Covered (zcode p) 2 C (levFull 2)) ∧
    (Covered (zcode 3) 3 S3gen (levFull 3) ∧ Covered f4code 3 K4gen (levFull 3) ∧
      (∃ C : Gen 3 (ZMod 7), Covered (zcode 7) 3 C (levFull 3)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 11 ≤ p → ∃ C : Gen 3 (ZMod p), Covered (zcode p) 3 C (levFull 3)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∃ C : Gen 3 (ZMod p), Covered (zcode p) 3 C (levSq 3))) ∧
    (Covered f4code 4 S4gen (levFull 4) ∧
      (∀ (p : ℕ) [Fact p.Prime], 17 ≤ p → ∃ C : Gen 4 (ZMod p), Covered (zcode p) 4 C (levFull 4)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∃ C : Gen 4 (ZMod p), Covered (zcode p) 4 C (levSq 4))) ∧
    ((∀ (p : ℕ) [Fact p.Prime], 37 ≤ p → ∃ C : Gen 5 (ZMod p), Covered (zcode p) 5 C (levFull 5)) ∧
      (∀ (p : ℕ) [Fact p.Prime], 19 ≤ p → ∃ C : Gen 5 (ZMod p), Covered (zcode p) 5 C (levSq 5))) ∧
    (∀ s : ℕ, 2 ≤ s → ∀ (p : ℕ) [Fact p.Prime], 2 ^ s < p →
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levFull s)) ∧
      (∃ C : Gen s (ZMod p), Covered (zcode p) s C (levPre s)))) ∧
    ((∃ C : Gen 2 GF8, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF9, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF16, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF25, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF27, Covered PF.code 2 C (levFull 2)) ∧
      (∃ C : Gen 2 GF49, Covered PF.code 2 C (levFull 2))) ∧
    ((∃ C : Gen 3 GF25, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF32, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF49, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF64, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF81, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF121, Covered PF.code 3 C (levFull 3)) ∧
      (∃ C : Gen 3 GF125, Covered PF.code 3 C (levFull 3))) := by
  sorry

end G14

end GeoSeq
