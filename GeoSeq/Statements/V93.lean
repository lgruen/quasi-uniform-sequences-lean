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
# Statements: stage V9-3 (paper V4: `sec:fail`, prime base)

Polynomial-base digital sequences over prime fields: `b`-adic digits and radical inverses (`def:radinv`), `eq:carrydigit` and `lem:carrypair` (prime `q`), `thm:nonqu` (prime `q`), the pigeonhole covering bound, `cor:halton` (Goda–Hofer–Suzuki Open Problem 2) and `cor:faure` (prime `q`).
PROVED (`GeoSeq/V93Poly.lean`, `V93Carry.lean`, `V93Thm.lean`, `V93Halton.lean`); generated verbatim from the proof
files' signatures by `scripts/gen_v93_statements.py` (definitions in `GeoSeq/V93Defs.lean`). Paper: V4
(`paper/sections/03-fail.tex`); label → Lean map in the formalization notes of the research repository, plan
the formalization notes of the research repository Configuration: `comparatorGeoSeqV93.json`.
-/

namespace GeoSeq
open Finset Polynomial

section G0
variable {F : Type*} [Field F]

theorem badicDigit_add (b V W : F[X]) (Q : ℕ) :
    badicDigit b (V + W) Q = badicDigit b V Q + badicDigit b W Q := by
  sorry

/-- `a_0(a + b W) = a` for `deg a < deg b`. -/
theorem badicDigit_base {b a : F[X]} (ha : a.natDegree < b.natDegree) (W : F[X]) :
    badicDigit b (a + b * W) 0 = a := by
  sorry

/-- `a_{Q+1}(a + b W) = a_Q(W)` for `deg a < deg b`. -/
theorem badicDigit_succ {b a : F[X]} (ha : a.natDegree < b.natDegree) (W : F[X]) (Q : ℕ) :
    badicDigit b (a + b * W) (Q + 1) = badicDigit b W Q := by
  sorry

/-- High digits vanish: `a_Q(V) = 0` if `deg V < e Q`. -/
theorem badicDigit_high {b V : F[X]} (hb : 1 ≤ b.natDegree) {Q : ℕ}
    (hV : V.natDegree < b.natDegree * Q) : badicDigit b V Q = 0 := by
  sorry

/-- The digits of `b^η W`: `0` below `η`, then those of `W`. -/
theorem badicDigit_pow_mul {b : F[X]} (hb : 1 ≤ b.natDegree) (W : F[X]) (η Q : ℕ) :
    badicDigit b (b ^ η * W) Q = if Q < η then 0 else badicDigit b W (Q - η) := by
  sorry

/-- The digits of the run `g S_n` (`deg g < deg b`): `g` at the positions `< n`, `0` beyond. -/
theorem badicDigit_run {b g : F[X]} (hg : g.natDegree < b.natDegree) (n Q : ℕ) :
    badicDigit b (g * runS b n) Q = if Q < n then g else 0 := by
  sorry

/-- Digits below `λ` depend only on `V mod b^λ`. -/
theorem badicDigit_congr {b : F[X]} (hb : 1 ≤ b.natDegree) {V V' : F[X]} {l Q : ℕ}
    (h : b ^ l ∣ V - V') (hQ : Q < l) : badicDigit b V Q = badicDigit b V' Q := by
  sorry

theorem runS_mul (b : F[X]) (n : ℕ) : (b - 1) * runS b n = b ^ n - 1 := by
  sorry

theorem runS_ne_zero {b : F[X]} (hb : 1 ≤ b.natDegree) {n : ℕ} (hn : 1 ≤ n) : runS b n ≠ 0 := by
  sorry

end G0

section G1
variable {p : ℕ} [Fact p.Prime]

/-- `idxPolyP p (ι(V)) = V`. -/
theorem idxPolyP_polyIdx (V : Polynomial (ZMod p)) : idxPolyP p (polyIdx p V) = V := by
  sorry

theorem polyIdx_lt (V : Polynomial (ZMod p)) {m : ℕ} (hV : V.natDegree < m) : polyIdx p V < p ^ m := by
  sorry

theorem polyIdx_injective : Function.Injective (polyIdx p) := by
  sorry

end G1

section G2

/-- A shared prefix of `L` digits: the two values differ by at most `p^{-L}`. -/
theorem real_prefix {p : ℕ} (hp : 2 ≤ p) (d d' : ℕ → ℕ) (hd : ∀ j, d j < p) (hd' : ∀ j, d' j < p)
    (L : ℕ) (h : ∀ j, j < L → d j = d' j) :
    |∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1) - ∑' j, (d' j : ℝ) / (p : ℝ) ^ (j + 1)| ≤ 1 / (p : ℝ) ^ L := by
  sorry

/-- The carry: digits `x = 0^k · a · (p-1)^{L-k-1} ⋯` and `x' = 0^k · (a+1) · 0^{L-k-1} ⋯` (equal before
position `k`), with a strict tail for `x'`: `|y(x') - y(x)| < 2 p^{-L}`. -/
theorem real_carry {p : ℕ} (hp : 2 ≤ p) (d d' : ℕ → ℕ) (hd : ∀ j, d j < p) (hd' : ∀ j, d' j < p)
    {k L : ℕ} (hkL : k < L) (h0 : ∀ j, j < k → d j = d' j) (h1 : d' k = d k + 1)
    (h2 : ∀ j, k < j → j < L → d j = p - 1 ∧ d' j = 0) (ht : ∃ M, L ≤ M ∧ d' M + 1 < p) :
    |∑' j, (d' j : ℝ) / (p : ℝ) ^ (j + 1) - ∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1)| < 2 / (p : ℝ) ^ L := by
  sorry

end G2

section G3
variable {F : Type*} [Field F]

/-- `sec:polybases`: a radical inverse is `b`-adic. -/
theorem IsRadInv.isBAdic {Y : F[X] → ℕ → F} {b : F[X]} {π : F[X] → ℕ → F} (hb : 1 ≤ b.natDegree)
    (hY : IsLinCoord Y) (hr : IsRadInv Y b π) : IsBAdic Y b := by
  sorry

end G3

section G4
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- `eq:carrydigit` for prime `q = p`: `ȳ = -1` has digit `p - 1`, `y° = 0`, and adding `-ȳ = 1` to
`y° ȳ ⋯ ȳ` digitwise gives `1 0 ⋯ 0`, one unit of the last digit more. -/
theorem carrydigit_prime :
    (-1 : ZMod p).val = p - 1 ∧ (0 : ZMod p).val = 0 ∧ (1 : ZMod p).val = (0 : ZMod p).val + 1 ∧
      (0 : ZMod p) + 1 = 1 ∧ (-1 : ZMod p) + 1 = 0 := by
  sorry

/-- **`lem:carrypair`** (prime `q = p`). Coordinate `ĉ` is a `b`-adic radical inverse with digit map `π`
(`b = b_ĉ`, `e = deg b`), every other coordinate `c` is `b_c`-adic. Let `deg g, deg g̃, deg g' < e` with
`π(g) = (1, …, 1)`, `π(g̃) = (0, -1, …, -1)`, `π(g') = (-1, …, -1)`, and let `D ≠ 0`, `η < λ` with
(i) `D ≡ g b^η S_{λ-η} (mod b^λ)`, (ii) `b_c^{j_c} ∣ D` with `e_c j_c ≥ L = e λ` for every `c ≠ ĉ`,
(iii) `deg D < m`. Then the indices `ι(V_1)`, `ι(V_1 + D)` (`V_1 = g̃ b^η + g' b^{η+1} S_{λ-η-1}`) are `< p^m`,
distinct, and the two points are at Euclidean distance `< √(s+3) p^{-L}`. -/
theorem carrypair (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (D : (ZMod p)[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    polyIdx p (carryV1 (b ch) gt g' η l) < p ^ m ∧
      polyIdx p (carryV1 (b ch) gt g' η l + D) < p ^ m ∧
      polyIdx p (carryV1 (b ch) gt g' η l) ≠ polyIdx p (carryV1 (b ch) gt g' η l + D) ∧
      euclDist (linPt p Y (polyIdx p (carryV1 (b ch) gt g' η l)))
        (linPt p Y (polyIdx p (carryV1 (b ch) gt g' η l + D))) <
        Real.sqrt (s + 3) / (p : ℝ) ^ ((b ch).natDegree * l) := by
  sorry

/-- `lem:carrypair`, "in particular": `δ(P_m) < √(s+3) p^{-L}`. -/
theorem carrypair_sep (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (D : (ZMod p)[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    sepDistIdx (linPt p Y) (p ^ m) < Real.sqrt (s + 3) / (p : ℝ) ^ ((b ch).natDegree * l) := by
  sorry

end G4

section G5

theorem exists_pow_sub_one_dvd {F : Type*} [Field F] [Finite F] {R a : F[X]} (hR : R ≠ 0)
    (hc : IsCoprime a R) : ∃ ν, 1 ≤ ν ∧ R ∣ a ^ ν - 1 := by
  sorry

end G5

section G6
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- `thm:nonqu`, existence of `ν` and `k`: `R ∣ b^ν - 1` with `ν ≥ 1`, and `b^ν ∣ Θ^k - 1` with
`k ≥ 1` and `(E/e)(k + 1) ≥ ν`; then `η = (E/e)(k + 1) - ν`. -/
theorem nonqu_exists (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s) :
    ∃ ν k η : ℕ, 1 ≤ ν ∧ 1 ≤ k ∧ carryR b ch ∣ b ch ^ ν - 1 ∧ b ch ^ ν ∣ thetaP b ch ^ k - 1 ∧
      η + ν = lcmDeg b / (b ch).natDegree * (k + 1) := by
  sorry

/-- `s L_Q = m_Q + Q (s-1) E`: the excess `s L - m` of `lem:carrypair` is `Q (s-1) E`. -/
theorem nonqu_excess (s E k Q : ℕ) (hs : 1 ≤ s) :
    s * (Q * E * (k + 1)) = Q * (s * E * (k + 1) - (s - 1) * E) + Q * ((s - 1) * E) := by
  sorry

/-- **`thm:nonqu`** (prime `q = p`), the explicit pairs. Let the bases `b_c` have degrees `e_c ≥ 1` (pairwise
coprimality is used only for the existence of `ν`, `k`, `nonqu_exists`), coordinate `ĉ` a `b_ĉ`-adic radical inverse with digit map `π`, every other coordinate `b_c`-adic,
`g, g̃, g'` as in `lem:carrypair`, `R ∣ b^ν - 1` (`ν ≥ 1`), `b^ν ∣ Θ^k - 1`, `η + ν = (E/e)(k + 1)`. For
`Q = p^w` put `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}`, `L_Q = Q E (k+1)`, `m_Q = Q (s E (k+1) - (s-1) E)`. Then the
indices `ι(V_1)`, `ι(V_1 + D_Q)` of `lem:carrypair` (with `(η, λ) = (Qη, Q(η+ν))`) are `< p^{m_Q}` and
distinct, and the two points are at Euclidean distance `< √(s+3) p^{-L_Q}`. -/
theorem nonqu_pair (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    polyIdx p (nonquV1 b ch gt g' ν η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch gt g' ν η (p ^ w)) ≠
        polyIdx p (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) ∧
      euclDist (linPt p Y (polyIdx p (nonquV1 b ch gt g' ν η (p ^ w))))
        (linPt p Y (polyIdx p (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)))) <
        Real.sqrt (s + 3) / (p : ℝ) ^ (p ^ w * lcmDeg b * (k + 1)) := by
  sorry

/-- `thm:nonqu`, the normalized separations along the levels `m_Q`: with `X_Q = Q (s-1) E`,
`sep(P_{m_Q}) = δ(P_{m_Q}) p^{m_Q/s} < √(s+3) p^{-X_Q/s}`, and for `K_Q = ⌈m_Q/s⌉` the full level `P_{s K_Q}`:
`sep(P_{s K_Q}) = δ(P_{s K_Q}) p^{K_Q} < √(s+3) p^{1 - X_Q/s}`. -/
theorem nonqu_sep (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    sepDistIdx (linPt p Y) (p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b))) *
        ((p : ℝ) ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b))) ^ ((1 : ℝ) / s) <
        Real.sqrt (s + 3) * (p : ℝ) ^ (-((p ^ w * ((s - 1) * lcmDeg b) : ℕ) : ℝ) / s) ∧
      sepDistIdx (linPt p Y)
          (p ^ (s * ((p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) + s - 1) / s))) *
        (p : ℝ) ^ ((p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) + s - 1) / s) <
        Real.sqrt (s + 3) * (p : ℝ) ^ (1 - ((p ^ w * ((s - 1) * lcmDeg b) : ℕ) : ℝ) / s) := by
  sorry

theorem linPt_mem (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (n : ℕ) (c : Fin s) :
    0 ≤ linPt p Y n c ∧ linPt p Y n c ≤ 1 := by
  sorry

end G6

section G7
variable {p : ℕ} {s : ℕ}

/-- Pigeonhole lower bound for the covering radius: if `N < M^s`, some cell of the grid of side `1/M` contains
none of the first `N` points, and its centre is at distance `≥ 1/(2M)` from all of them. -/
theorem covRadIdx_ge (pt : ℕ → Fin s → ℝ) (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : N < M ^ s) : 1 / (2 * (M : ℝ)) ≤ covRadIdx pt N := by
  sorry

/-- `h(P_m) ≥ p^{-m/s}/(2p)` (grid of side `p^{-(⌊m/s⌋+1)}`). -/
theorem covRadIdx_ge_pow (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (m : ℕ) :
    ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) / (2 * p) ≤ covRadIdx pt (p ^ m) := by
  sorry

end G7

section G8
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`thm:nonqu`** (prime `q = p`). Let `s ≥ 2`, let the bases `b_0, …, b_{s-1} ∈ 𝔽_p[z]` be pairwise coprime
of degrees `≥ 1`, coordinate `ĉ` a `b_ĉ`-adic radical inverse, and every other coordinate `b_c`-adic. Then for
every `ε > 0` some prefix `P_m` contains two points at Euclidean distance `< ε p^{-m/s}` (the explicit pairs of
`nonqu_pair`), and the sequence is not quasi-uniform. -/
theorem nonqu (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (linPt p Y v) (linPt p Y w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPt p Y) := by
  sorry

end G8

section G9
variable {F : Type*} [Field F] {s : ℕ}

theorem haltonY_lin (b : Fin s → F[X]) (c : Fin s) : IsLinCoord (haltonY b c) := by
  sorry

theorem haltonY_radInv (b : Fin s → F[X]) (c : Fin s) (hb : 1 ≤ (b c).natDegree) :
    IsRadInv (haltonY b c) (b c) (haltonPi (b c).natDegree) := by
  sorry

end G9

section G10
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- The Palomar statement's finite-sum `haltonPt` is the point of the linear-coordinate sequence `haltonY`. -/
theorem haltonPt_eq_linPt (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) :
    haltonPt p b = linPt p (haltonY b) := by
  sorry

end G10

section G11

/-- **`cor:halton`** (Goda–Hofer–Suzuki, Open Problem 2). For every prime `p`, every `s ≥ 2` and all pairwise
coprime `b_0, …, b_{s-1} ∈ 𝔽_p[z]` of degrees `≥ 1` (not necessarily monic or irreducible), the Halton-type
sequence in these bases has, for every `ε > 0`, a prefix of `p^m` points containing two points at Euclidean
distance `< ε p^{-m/s}`; and it is not quasi-uniform. -/
theorem halton_not_quasiUniform (p : ℕ) [Fact p.Prime] (s : ℕ) (hs : 2 ≤ s)
    (b : Fin s → Polynomial (ZMod p)) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (haltonPt p b v) (haltonPt p b w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (haltonPt p b) := by
  sorry

/-- **`cor:halton`**, the explicit pairs. For any coordinate `ĉ` (`b = b_ĉ`, `e = deg b`), with
`Σ = 1 + z + ⋯ + z^{e-1}`, `Σ' = 1 + z + ⋯ + z^{e-2}`, admissible `ν, k, η` of `thm:nonqu` and `Q = p^w`: the indices
`ι(V_1)`, `ι(V_2)`, `V_1 = -Σ' b^{Qη} - Σ b^{Qη+1} S_{Qν-1}`, `V_2 = V_1 + Σ b^{Qη} S_{Qν} Θ^{Qk}`, are distinct and
`< p^{m_Q}`, and the two points of the Halton-type sequence are at distance `< √(s+3) p^{-L_Q}`. -/
theorem halton_pair (p : ℕ) [Fact p.Prime] (s : ℕ) (hs : 2 ≤ s)
    (b : Fin s → Polynomial (ZMod p)) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    let Sg : Polynomial (ZMod p) := ∑ j ∈ range (b ch).natDegree, X ^ j
    let Sg' : Polynomial (ZMod p) := ∑ j ∈ range ((b ch).natDegree - 1), X ^ j
    polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w) + nonquD b ch Sg ν k η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w)) ≠
        polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w) + nonquD b ch Sg ν k η (p ^ w)) ∧
      euclDist (haltonPt p b (polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w))))
        (haltonPt p b (polyIdx p (nonquV1 b ch (-Sg') (-Sg) ν η (p ^ w) + nonquD b ch Sg ν k η (p ^ w)))) <
        Real.sqrt (s + 3) / (p : ℝ) ^ (p ^ w * lcmDeg b * (k + 1)) := by
  sorry

end G11

section G12
variable {F : Type*} [Field F]

/-- The Taylor digits at `a` are the `(z - a)`-adic digits: `[(z-a)^n] V = [z^0] a_n(V)`. -/
theorem taylor_coeff_eq_badicDigit (a : F) (V : F[X]) (n : ℕ) :
    (taylor a V).coeff n = (badicDigit (X - C a) V n).coeff 0 := by
  sorry

end G12

section G13
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- The unscrambled frame `(P_{a_0}, …, P_{a_{s-1}})` is the Halton-type sequence in the bases `z - a_c`. -/
theorem frame_eq_haltonPt (a : Fin s → ZMod p) :
    seqPoint (zcode p) (fun c n k => pas (a c) n k) = haltonPt p (fun c => X - C (a c)) := by
  sorry

/-- **`cor:faure`** (prime `q = p`). For every `s ≥ 2` and all distinct places `a_0, …, a_{s-1} ∈ 𝔽_p` (so
`s ≤ p`), the unscrambled frame sequence `(P_{a_0}, …, P_{a_{s-1}})` has, for every `ε > 0`, a prefix `P_m` with two
points at distance `< ε p^{-m/s}`, and is not quasi-uniform. -/
theorem faure_not_quasiUniform (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (seqPoint (zcode p) (fun c n k => pas (a c) n k) v)
          (seqPoint (zcode p) (fun c n k => pas (a c) n k) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (seqPoint (zcode p) (fun c n k => pas (a c) n k)) := by
  sorry

/-- **`cor:faure`**, "in particular": the Faure sequence `(P^0, P^1, …, P^{s-1})` in prime base `p`
(`P^c[n][k] = C(k, n) c^{k-n}`, the frame at the places `0, 1, …, s-1`) is not quasi-uniform for every
`2 ≤ s ≤ p`. -/
theorem faureSeq_not_quasiUniform (hs : 2 ≤ s) (hsp : s ≤ p) :
    ¬ IsQuasiUniform (seqPoint (zcode p) (fun (c : Fin s) n k => pas (faurePlace p c : ZMod p) n k)) := by
  sorry

end G13

end GeoSeq
