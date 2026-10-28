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
# Statements: the steering route in dimension two (GeoSeq stage S7)

`rem:onedigit` closed forms used by the windows, the window certificate (`thm:GA`, certificate part)
and `lem:dom`; the depth direction and the covering step (`prop:depthdir`, `eq:steer`, in the free
series `k = 1/((z_1 - z_0) g)`); **`thm:GA`** (`GA_step`, `GA_exists`, `GA_sep`, `GA`); **`cor:G2`**;
**`lem:HBcov`**, **`thm:HB`**, the reflected checker of `cor:HB17` and **`cor:HB17`**. PROVED
(`GeoSeq/Window.lean`, `Steer.lean`, `G2.lean`, `HB.lean`); generated verbatim from the proof files'
signatures.

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset PowerSeries

variable {F : Type*} [Field F]

/-- `f_1(1, σ)`: numerator `(σ = 0 ? p : val σ) - 1`. -/
theorem f1_one_val (p : ℕ) [NeZero p] (σ : ZMod p) :
    gapNum1 p 1 σ = (if σ = 0 then p else σ.val) - 1 := by
  sorry

/-- `f_1(0, σ)`: numerator `min(val σ, p - val σ) - 1`. -/
theorem f1_zero_val (p : ℕ) [NeZero p] (σ : ZMod p) :
    gapNum1 p 0 σ = min σ.val (p - σ.val) - 1 := by
  sorry

/-- `f_1(0, -σ) = f_1(0, σ)`. -/
theorem F0_neg (p : ℕ) [NeZero p] (σ : ZMod p) : gapNum1 p 0 (-σ) = gapNum1 p 0 σ := by
  sorry

/-- `f_1(1, z)` for an integer `-p < z ≤ 0`: numerator `p - 1 + z`. -/
theorem f1_int_nonpos (p : ℕ) [NeZero p] (z : ℤ) (h0 : -(p : ℤ) < z) (h1 : z ≤ 0) :
    (gapNum1 p 1 (z : ZMod p) : ℤ) = p - 1 + z := by
  sorry

/-- `f_1(1, z)` for an integer `1 ≤ z ≤ p - 1`: numerator `z - 1`. -/
theorem f1_int_pos (p : ℕ) [NeZero p] (z : ℤ) (h0 : 1 ≤ z) (h1 : z < p) :
    (gapNum1 p 1 (z : ZMod p) : ℤ) = z - 1 := by
  sorry

/-- `f_1(0, z)` for an integer `0 ≤ z ≤ p - 1`: numerator `min(z, p - z) - 1`. -/
theorem f0_int (p : ℕ) [NeZero p] (z : ℤ) (h0 : 0 ≤ z) (h1 : z < p) :
    gapNum1 p 0 (z : ZMod p) = min z.toNat (p - z.toNat) - 1 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:GA`, certificate part** (with `lem:cert`, `j = 1`): a `(0,2)`-sequence over `𝔽_p`,
`p ≥ 5`, whose one-digit responses lie in the windows `Wo`, `Wx` at every level, has
`c(P_{2K}) ≥ min(1, LB)` for every `K ≥ 1`, for every `LB` below the four numbers of `thm:GA`. -/
theorem win_cert (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (C : Gen 2 (ZMod p))
    (hseq : IsSeq0 (zcode p) C) (Wo Wx : Fin 2 → Set (ZMod p)) (hW : RespIn C Wo Wx) (LB : ℝ)
    (hLB : GAbound p Wo Wx LB) (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) C) (min 1 LB) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:dom`** (window dominance): if every own response lies in `[-A, -B]` and every cross response in
`[-B, B]` (`0 ≤ B ≤ A`, `A + B < p`), then `c(P_{2K}) ≥ min(1 - (A+1)/p, √2 (1 - (A+B+1)/p))` for every
`K ≥ 1`. -/
theorem dom (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (C : Gen 2 (ZMod p)) (hseq : IsSeq0 (zcode p) C)
    (A B : ℕ) (hBA : B ≤ A) (hAB : A + B < p)
    (hW : RespIn C (fun _ => intWin p (-(A : ℤ)) (-(B : ℤ))) (fun _ => intWin p (-(B : ℤ)) B))
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) C)
      (min (1 - ((A : ℝ) + 1) / p) (Real.sqrt 2 * (1 - ((A : ℝ) + B + 1) / p))) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **Depth direction, own part**: `O^{(n)}` of `k + x^m e` is `O^{(n)}` of `k` for `n < m`, and
`O^{(m)}` moves by `-a e(0)` (`z_1(0) = 1`). -/
theorem ownR_add (z1 : PowerSeries F) (hz1 : constantCoeff z1 = 1) (a : F) (k e : PowerSeries F)
    (m n : ℕ) :
    ownR z1 a (k + X ^ m * e) n =
      ownR z1 a k n - (if m ≤ n then coeff (n - m) (C a * z1 * e * PowerSeries.mk 1) else 0) ∧
    ownR z1 a (k + X ^ m * e) m = ownR z1 a k m - a * constantCoeff e := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **Depth direction, cross part**: `X^{(n)}` of `k + x^m e` is `X^{(n)}` of `k` for `n ≤ m`, and
`X^{(m+1)}` moves by `-a' θ e(0)` (`z_0(0) = 0`, `[x]z_0 = -θ`). -/
theorem crossR_add (z0 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0) (hz01 : coeff 1 z0 = -θ)
    (a : F) (k e : PowerSeries F) (m : ℕ) :
    (∀ n, n ≤ m → crossR z0 a (k + X ^ m * e) n = crossR z0 a k n) ∧
    crossR z0 a (k + X ^ m * e) (m + 1) = crossR z0 a k (m + 1) - a * θ * constantCoeff e := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** `X^{(1)} = -a' θ k(0)`. -/
theorem crossR_one (z0 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0) (hz01 : coeff 1 z0 = -θ)
    (a : F) (k : PowerSeries F) : crossR z0 a k 1 = -(a * θ * constantCoeff k) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The covering step** (condition (ii) of `thm:GA`): for every series `k` (every history) and every
depth `m`, some value `t` of the coefficient `m` puts `(O^{(m)}, X^{(m+1)})` into `Wo × Wx`. -/
theorem steer_step (z0 z1 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0)
    (hz01 : coeff 1 z0 = -θ) (hz1 : constantCoeff z1 = 1) (a a' : F) (ha : a ≠ 0)
    (Wo Wx : Set F) (hcov : ∀ β : F, ∃ o ∈ Wo, ∃ x ∈ Wx, (a' * θ / a) * (o - 1) - x = β)
    (k : PowerSeries F) (m : ℕ) :
    ∃ t : F, ownR z1 a (k + X ^ m * C t) m ∈ Wo ∧ crossR z0 a' (k + X ^ m * C t) (m + 1) ∈ Wx := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The rule never stops** (`thm:GA`, existence by induction over the depth): there is a series `k`
with the prescribed constant term such that every own partial sum `O^{(l)}`, `l ≥ 1`, lies in `Wo` and every
cross partial sum `X^{(l)}`, `l ≥ 1`, lies in `Wx` (`X^{(1)} = -κ ∈ Wx` is condition (i)). -/
theorem steer_exists (z0 z1 : PowerSeries F) (θ : F) (hz0 : constantCoeff z0 = 0)
    (hz01 : coeff 1 z0 = -θ) (hz1 : constantCoeff z1 = 1) (a a' : F) (ha : a ≠ 0)
    (Wo Wx : Set F) (hi : -(a' * θ / a) ∈ Wx)
    (hcov : ∀ β : F, ∃ o ∈ Wo, ∃ x ∈ Wx, (a' * θ / a) * (o - 1) - x = β) :
    ∃ k : PowerSeries F, constantCoeff k = a⁻¹ ∧
      ∀ l, 1 ≤ l → ownR z1 a k l ∈ Wo ∧ crossR z0 a' k l ∈ Wx := by
  sorry

/-- The scaled local roots `faureZ p θ`: `z_0(0) = 0`, `z_1(0) = 1`, `[x]z_0 = -θ`, `[x]z_1 = θ`,
`z_0 + z_1 = 1`. -/
theorem faureZ_facts (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (θ : ZMod p) :
    constantCoeff (faureZ p θ 0) = 0 ∧ constantCoeff (faureZ p θ 1) = 1 ∧
      coeff 1 (faureZ p θ 0) = -θ ∧ coeff 1 (faureZ p θ 1) = θ ∧
      faureZ p θ 0 + faureZ p θ 1 = 1 := by
  sorry

/-- `eq:roots` for `faureZ p θ`: `z_c² - z_c = θ x`. -/
theorem faureZ_root (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (θ : ZMod p) (c : Fin 2) :
    Polynomial.aeval (faureZ p θ c) (Polynomial.X ^ 2 - Polynomial.X : Polynomial (ZMod p)) =
      C θ * X := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **The responses of a self-similar scramble of the Faure frame** (`prop:law` + `lem:gform`): with
`k_c = 1/((z_1 - z_0) g_c)`, column `c'` has the own response `ownR z_1 g_{c'}(0) k_{c'}` and the cross
response `crossR z_0 g_{1-c'}(0) k_{c'}`, at every level `K ≥ l ≥ 1`. -/
theorem ga_resp (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ : ZMod p) (hθ : θ ≠ 0)
    (g : Fin 2 → PowerSeries (ZMod p)) (hg : ∀ c, constantCoeff (g c) ≠ 0) (K l : ℕ) (hl : 1 ≤ l)
    (hlK : l ≤ K) :
    IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 0 0 (ownR (faureZ p θ 1) (constantCoeff (g 0))
        ((faureZ p θ 1 - faureZ p θ 0) * g 0)⁻¹ l) ∧
      IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 1 0 (crossR (faureZ p θ 0) (constantCoeff (g 1))
        ((faureZ p θ 1 - faureZ p θ 0) * g 0)⁻¹ l) ∧
      IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 1 1 (ownR (faureZ p θ 1) (constantCoeff (g 1))
        ((faureZ p θ 1 - faureZ p θ 0) * g 1)⁻¹ l) ∧
      IsCarryEntry (ssGen g (faureZ p θ)) K 0 l 0 1 (crossR (faureZ p θ 0) (constantCoeff (g 0))
        ((faureZ p θ 1 - faureZ p θ 0) * g 1)⁻¹ l) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:GA`, the choices exist at every depth for every history**: for every pair of multipliers `g`
(normalised by `κ_{0←1} g_1(0) = θ g_0(0)`) and every depth `l ≥ 1` there are multipliers `g'` that agree
with `g` in the coefficients `< l` and put the depth-`l` responses of both columns into the windows:
`O_{c'}^{(l)} ∈ W_o^{(c')}`, `X_{1-c'←c'}^{(l+1)} ∈ W_x^{(c')}` (at every level where they are defined). -/
theorem GA_step (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 κ10 : ZMod p) (hθ : θ ≠ 0)
    (h01 : κ01 ≠ 0) (hκ : κ01 * κ10 = θ ^ 2) (Wo Wx : Fin 2 → Set (ZMod p))
    (hc0 : Covers κ10 (Wo 0) (Wx 0)) (hc1 : Covers κ01 (Wo 1) (Wx 1))
    (g : Fin 2 → PowerSeries (ZMod p)) (hg1 : constantCoeff (g 1) ≠ 0)
    (hgr : κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0)) (l : ℕ) (hl : 1 ≤ l) :
    ∃ g' : Fin 2 → PowerSeries (ZMod p), (∀ c, ∀ j < l, coeff j (g' c) = coeff j (g c)) ∧
      (∀ K d, l ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 0 0 d → d ∈ Wo 0) ∧
        (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 1 1 d → d ∈ Wo 1)) ∧
      (∀ K d, l + 1 ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 1 0 d → d ∈ Wx 0) ∧
        (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 0 1 d → d ∈ Wx 1)) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:GA`, existence**: under conditions (i), (ii) there are multipliers `g` (normalised by
`κ_{0←1} g_1(0) = θ g_0(0)`, i.e. `λ_0/λ_1 = κ_{0←1}/θ`) all of whose responses lie in the windows at
every level. -/
theorem GA_exists (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 κ10 : ZMod p) (hθ : θ ≠ 0)
    (h01 : κ01 ≠ 0) (hκ : κ01 * κ10 = θ ^ 2) (Wo Wx : Fin 2 → Set (ZMod p))
    (hi0 : -κ10 ∈ Wx 0) (hi1 : -κ01 ∈ Wx 1)
    (hc0 : Covers κ10 (Wo 0) (Wx 0)) (hc1 : Covers κ01 (Wo 1) (Wx 1)) :
    ∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p θ)) Wo Wx := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:GA`, every choice**: a self-similar scramble of the Faure frame with scale `θ` and multipliers
`g` (`g_1(0) ≠ 0`, `κ_{0←1} g_1(0) = θ g_0(0)`) whose responses lie in the windows is a `(0,2)`-sequence,
and `c(P_{2K}) ≥ min(1, LB)` for every `K ≥ 1` and every `LB` below the four numbers of `thm:GA`. -/
theorem GA_sep (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 : ZMod p) (hθ : θ ≠ 0) (h01 : κ01 ≠ 0)
    (Wo Wx : Fin 2 → Set (ZMod p)) (g : Fin 2 → PowerSeries (ZMod p))
    (hg1 : constantCoeff (g 1) ≠ 0) (hgr : κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0))
    (hW : RespIn (ssGen g (faureZ p θ)) Wo Wx) :
    IsSeq0 (zcode p) (ssGen g (faureZ p θ)) ∧
      ∀ LB : ℝ, GAbound p Wo Wx LB → ∀ K, 1 ≤ K →
        SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p θ))) (min 1 LB) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`thm:GA`** (covering windows): let `p ≥ 5` be prime, `θ, κ_{0←1}, κ_{1←0} ∈ 𝔽_p^*` with
`κ_{0←1} κ_{1←0} = θ²`, and windows with (i) `-κ_{1-c'←c'} ∈ W_x^{(c')}` and (ii)
`κ_{1-c'←c'}(W_o^{(c')} - 1) - W_x^{(c')} = 𝔽_p`. Then (1) the choices exist at every depth, for every
history (`GA_step`); (2) a choice for all depths exists (`GA_exists`); (3) every resulting sequence is a
`(0,2)`-sequence with `c(P_{2K}) ≥ min(1, LB^GA)` for every `K ≥ 1` (`GA_sep`). The scramble is
parametrised by its multipliers `g_c` (equivalently `(λ_c, ψ_c)`, `prop:LI`(a)), normalised by
`κ_{0←1} g_1(0) = θ g_0(0)`. -/
theorem GA (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (θ κ01 κ10 : ZMod p) (hθ : θ ≠ 0)
    (h01 : κ01 ≠ 0) (hκ : κ01 * κ10 = θ ^ 2) (Wo Wx : Fin 2 → Set (ZMod p))
    (hi0 : -κ10 ∈ Wx 0) (hi1 : -κ01 ∈ Wx 1)
    (hc0 : Covers κ10 (Wo 0) (Wx 0)) (hc1 : Covers κ01 (Wo 1) (Wx 1)) :
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) → ∀ l, 1 ≤ l →
      ∃ g' : Fin 2 → PowerSeries (ZMod p), (∀ c, ∀ j < l, coeff j (g' c) = coeff j (g c)) ∧
        (∀ K d, l ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 0 0 d → d ∈ Wo 0) ∧
          (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 l 1 1 d → d ∈ Wo 1)) ∧
        (∀ K d, l + 1 ≤ K → (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 1 0 d → d ∈ Wx 0) ∧
          (IsCarryEntry (ssGen g' (faureZ p θ)) K 0 (l + 1) 0 1 d → d ∈ Wx 1))) ∧
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p θ)) Wo Wx) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      κ01 * constantCoeff (g 1) = θ * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p θ)) Wo Wx →
      IsSeq0 (zcode p) (ssGen g (faureZ p θ)) ∧
        ∀ LB : ℝ, GAbound p Wo Wx LB → ∀ K, 1 ≤ K →
          SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p θ))) (min 1 LB)) := by
  sorry

/-- Every integer `S` with `b lo - b ≤ S ≤ b hi + b` is `b i - ξ` with `lo ≤ i ≤ hi`, `-b ≤ ξ ≤ b`. -/
theorem cover_round (b lo hi S : ℤ) (hb : 1 ≤ b) (hlh : lo ≤ hi) (h1 : b * lo - b ≤ S)
    (h2 : S ≤ b * hi + b) : ∃ i ξ : ℤ, lo ≤ i ∧ i ≤ hi ∧ -b ≤ ξ ∧ ξ ≤ b ∧ S = b * i - ξ := by
  sorry

/-- An integer interval `[L, L + p - 1]` meets every residue class: every `β ∈ 𝔽_p` is `(S : 𝔽_p)` for some
`S ∈ [L, L + p - 1]`. -/
theorem cover_interval (p : ℕ) [NeZero p] (L : ℤ) (β : ZMod p) :
    ∃ S : ℤ, L ≤ S ∧ S ≤ L + p - 1 ∧ (S : ZMod p) = β := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** Conditions (i), (ii) of `thm:GA` for the square-root windows (`app:G2`): `-b ∈ [-b, b]` and
`b([-A,-b] - 1) - [-b,b] = 𝔽_p`, for `p ≥ 41`. -/
theorem G2_cover (p : ℕ) [Fact p.Prime] (hp : 41 ≤ p) :
    -((g2b p : ℕ) : ZMod p) ∈ intWin p (-(g2b p : ℤ)) (g2b p) ∧
      Covers ((g2b p : ℕ) : ZMod p) (intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (intWin p (-(g2b p : ℤ)) (g2b p)) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** The real bound of `cor:G2`: for `p ≥ 41`, `A < 2√p`, `b ≤ A`, `A + b < p`, and
`min(1 - (A+1)/p, √2(1 - (A+b+1)/p)) > 1 - (2√p+1)/p`. -/
theorem G2_bound (p : ℕ) (hp : 41 ≤ p) :
    g2b p ≤ g2A p ∧ g2A p + g2b p < p ∧
      1 - (2 * Real.sqrt p + 1) / p <
        min (1 - ((g2A p : ℝ) + 1) / p) (Real.sqrt 2 * (1 - ((g2A p : ℝ) + g2b p + 1) / p)) := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`cor:G2`** (= `thm:G`, square-root windows): for every prime `p ≥ 41`, with `b = θ = ⌈√p⌉`,
`A = b - 2 + ⌈(p-1)/b⌉`, `W_x = [-b,b]`, `W_o = [-A,-b]` in both columns (symmetric case of `thm:GA`,
`κ_{0←1} = κ_{1←0} = θ`): conditions (i), (ii) hold; a sequence with all responses in the windows
exists; and every such sequence is a `(0,2)`-sequence with `c(P_{2K}) ≥ L` for every `K ≥ 1`, for one
`L > 1 - (2√p+1)/p`. -/
theorem G2 (p : ℕ) [Fact p.Prime] (hp : 41 ≤ p) :
    (-((g2b p : ℕ) : ZMod p) ∈ intWin p (-(g2b p : ℤ)) (g2b p) ∧
      Covers ((g2b p : ℕ) : ZMod p) (intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (intWin p (-(g2b p : ℤ)) (g2b p))) ∧
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      constantCoeff (g 1) = constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (g2b p))) (fun _ => intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (fun _ => intWin p (-(g2b p : ℤ)) (g2b p))) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      constantCoeff (g 1) = constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (g2b p))) (fun _ => intWin p (-(g2A p : ℤ)) (-(g2b p : ℤ)))
        (fun _ => intWin p (-(g2b p : ℤ)) (g2b p)) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (g2b p))) ∧
        ∃ L : ℝ, 1 - (2 * Real.sqrt p + 1) / p < L ∧
          ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (g2b p)))) L) := by
  sorry

/-- With `ν = 2b + 1`, every integer `m` with `ν lo + 2b ≤ m ≤ ν hi - 2b` is `ν i + 2ξ` with
`lo ≤ i ≤ hi` and `-b ≤ ξ ≤ b`. -/
theorem cover_odd (b lo hi m : ℤ) (hb : 0 ≤ b) (h1 : (2 * b + 1) * lo + 2 * b ≤ m)
    (h2 : m ≤ (2 * b + 1) * hi - 2 * b) :
    ∃ i ξ : ℤ, lo ≤ i ∧ i ≤ hi ∧ -b ≤ ξ ∧ ξ ≤ b ∧ m = (2 * b + 1) * i + 2 * ξ := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:HBcov`** (with condition (i) of `thm:GA` and the square condition): for the brick hybrid
data (`b, e ≥ 1`, `ν = 2b + 1 < p`, `3k < p`), `κ_{0←1} κ_{1←0} = θ²`, `-κ_{1←0} = ν/2 ∈ W_x^{(0)}`,
`-κ_{0←1} = k ∈ W_x^{(1)}`, and both columns satisfy condition (ii). -/
theorem HBcov (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hν : hbNu b < p) (hk : 3 * hbK b e < p) :
    hbK01 p b e * hbK10 p b = hbTheta p b e ^ 2 ∧
      -hbK10 p b ∈ hbWx p b e 0 ∧ -hbK01 p b e ∈ hbWx p b e 1 ∧
      Covers (hbK10 p b) (hbWo p b e 0) (hbWx p b e 0) ∧
      Covers (hbK01 p b e) (hbWo p b e 1) (hbWx p b e 1) := by
  sorry

/-- **`thm:HB`** (hexagonal brick wall; V3: "every selection rule" = every multiplier family
normalised by `κ_{0←1} g_1(0) = θ g_0(0)` with all responses in the windows, and one exists): with `b, e ≥ 1`, `ν = 2b+1 < p`, `3k < p`, `2k + M_A < p` and
`η > 0` (`2b + 2M_B + 1 < p`), the scramble of `thm:GA` with the windows of the brick hybrid exists, and
every choice gives a `(0,2)`-sequence with `c(P_{2K}) ≥ min(1, LB^HB)` for every `K ≥ 1`. -/
theorem HB (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hν : hbNu b < p) (hk : 3 * hbK b e < p) (hka : 2 * hbK b e + hbMA p b < p)
    (hη : 2 * b + 2 * hbMB p b e + 1 < p) :
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e)) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      hbK01 p b e * constantCoeff (g 1) = hbTheta p b e * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (hbTheta p b e))) (hbWo p b e) (hbWx p b e) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (hbTheta p b e))) ∧
        ∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p b e))))
          (min 1 (Real.sqrt (hbLB2 p b e)))) := by
  sorry

/-- Correctness of the reflected checker `hbOK`. -/
theorem hbOK_spec (p : ℕ) : hbOK p = true ↔ HBConds p := by
  sorry

/-- Correctness of `smallDiv`: a small divisor `2 ≤ d < 20`. -/
theorem smallDiv_spec (n : ℕ) (h : smallDiv n = true) : ∃ d, 2 ≤ d ∧ d < 20 ∧ d ∣ n := by
  sorry

/-- Correctness of the range checker `hbCheck`. -/
theorem hbCheck_spec (cnt : ℕ) : ∀ lo, hbCheck lo cnt = true →
    ∀ n, lo ≤ n → n < lo + cnt → hbOK n = true ∨ smallDiv n = true := by
  sorry

/-- The finite range `3678 ≤ n < 10^4`, evaluated by the kernel (`decide`, no `native_decide`). -/
theorem hb_check_range : hbCheck 3678 6322 = true := by
  sorry

/-- `cor:HB17`, finite range: every prime `3677 < p < 10^4` satisfies the integer conditions. -/
theorem hb_range (p : ℕ) (hp : p.Prime) (h1 : 3677 < p) (h2 : p < 10000) : HBConds p := by
  sorry

/-- `cor:HB17`, the hand range: every `p ≥ 10^4` satisfies the integer conditions (written proof:
`p = 68b + r`, `0 ≤ r < 68`, `b ≥ 147`; `M_A ≤ 38`, `M_B ≤ 17`; two quadratic inequalities in `b, r`). -/
theorem hb_large (p : ℕ) (hp : 10000 ≤ p) : HBConds p := by
  sorry

/-- **`cor:HB17`** (separation of order `1 - O(1/p)`; the V3 clause "quasi-uniform" is `HB17_qu`,
stage V0): for every prime `p > 3677`, the brick hybrid with
`e = 1`, `b = ⌊p/68⌋` exists (`thm:GA`), and every such sequence is a `(0,2)`-sequence with
`c(P_{2K}) ≥ 1 - 17/p` for every `K ≥ 1` and `δ(P_{[N]}) ≥ (1 - 17/p) p^{-1} N^{-1/2}` for all `N ≥ 2`.
The range `p ≥ 10^4` is the written proof (`hb_large`); the `715` primes `3677 < p < 10^4` are checked by
the kernel (`hb_range`, reflected checker `hbCheck`, `decide`). -/
theorem HB17 (p : ℕ) [Fact p.Prime] (hp : 3677 < p) :
    (∃ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 ∧
      hbK01 p (p / 68) 1 * constantCoeff (g 1) = hbTheta p (p / 68) 1 * constantCoeff (g 0) ∧
      RespIn (ssGen g (faureZ p (hbTheta p (p / 68) 1))) (hbWo p (p / 68) 1) (hbWx p (p / 68) 1)) ∧
    (∀ g : Fin 2 → PowerSeries (ZMod p), constantCoeff (g 1) ≠ 0 →
      hbK01 p (p / 68) 1 * constantCoeff (g 1) = hbTheta p (p / 68) 1 * constantCoeff (g 0) →
      RespIn (ssGen g (faureZ p (hbTheta p (p / 68) 1))) (hbWo p (p / 68) 1) (hbWx p (p / 68) 1) →
      IsSeq0 (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))) ∧
        (∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))))
          (1 - 17 / (p : ℝ))) ∧
        SepAllN 2 (seqPoint (zcode p) (ssGen g (faureZ p (hbTheta p (p / 68) 1))))
          ((1 - 17 / (p : ℝ)) / p)) := by
  sorry

end GeoSeq
