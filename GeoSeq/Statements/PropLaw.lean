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
# Statements: the multi-digit law `prop:law` (`sec:law`), GeoSeq stage S3

Compared theorems (statement with `sorry`; proofs in `GeoSeq/Law.lean`, `GeoSeq/WFSep.lean`,
restated by name).

* `vecDigit_ss`: digits of an index vector of a self-similar scramble (`def:selfsim`).
* `law_cells`: the cell-digit map of a self-similar scramble is bijective (cell ring).
* `frame_hat_one`: `[x^i] M Ĝ = I`.
* **`law`** (`prop:law`, second form, every `s`, every depth `i`, every level `K ≥ l`: K-independence),
  **`law_first`** (first form `D_i(l) = [x^{l+i}] M_{>i} Ĝ`), `frame_inv` (the frame matrix of a frame
  is invertible).
* The bridge to `cert`: `cell_existsUnique`, `carry_exists`, `carryEntry_unique` (a `(0,sK,s)`-net
  prefix has unique carry responses).
* `WF_sep_of_law`: the separation half of `thm:WF` from the two statements of `lem:WFlaw`.
* `lem:gform` (`GeoSeq/Faure2.lean`): `lawD_zero`, `faure_inv`, **`gform`**, `faure_z0`;
  `prop:freeze` (a), (b): `partial_sums_zero`, **`freeze_a`**, **`freeze_b`**.
* `lem:WFlaw` over a field (`GeoSeq/WFLaw.lean`): `sq_of_rec`, `rhoWF_sq` (`ρ² = 1 + a x`), `wf_root`
  (`eq:roots`), `coeff_geom`, **`wf_law`**; the `𝔽_p` statements `WF_law_O1`, `WF_law_X10`, `WF_sep`,
  `WF_allN` are in `Statements/WF.lean` (now PROVED).

**V3 re-sync (stage V0, the formalization notes of the research repository).** Labels refer to the V3 paper
(development version V3 of the paper, `); the label → Lean map is the formalization notes of the research repository. Theorems tagged
*Legacy* belong to the earlier version only and are compared in `comparatorGeoSeqLegacy.json`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Matrix

section Law

variable {R : Type*} [CommRing R] {s : ℕ}

/-- The digits of an index vector of a self-similar scramble: `y_{c,n} = [x^n] g_c · V(z_c(θx))`. -/
theorem vecDigit_ss (g zθ : Fin s → PowerSeries R) {m : ℕ} (V : Fin m → R) (c : Fin s) (n : ℕ) :
    vecDigit (ssGen g zθ) V c n =
      coeff n (g c * ∑ k : Fin m, PowerSeries.C (V k) * zθ c ^ (k : ℕ)) := by
  sorry

/-- `[x^i] M Ĝ = I`: `∑_b ∑_{a ≤ i} [x^a] M[c][b] [x^{i-a}] Ĝ[b][c'] = δ_{cc'}`. -/
theorem frame_hat_one (g zθ : Fin s → PowerSeries R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (hMG : frameM g zθ * G = 1) (i : ℕ) (c c' : Fin s) :
    ∑ b, ∑ a ∈ range (i + 1), coeff a (frameM g zθ c b) * coeff (i - a) (G b c' * PowerSeries.mk 1) =
      if c = c' then 1 else 0 := by
  sorry

/-- **The cells of a self-similar scramble** (the cell ring `𝔽_q[z]/(w^K)` of `sec:law`): the cell-digit
map `V ↦ (y_{c,n}(V))_{c, n<K}`, `R^{sK} → R^{s×K}`, is bijective (onto by `law_digits`; one-to-one by
counting, `R` finite). -/
theorem law_cells [Fintype R] [DecidableEq R] (g zθ : Fin s → PowerSeries R) (w : Polynomial R)
    (hw : w.natDegree ≤ s) (θ θ' : R) (hθ : θ * θ' = 1)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (hMG : frameM g zθ * G = 1) (K : ℕ) (hK : 1 ≤ K) :
    Function.Bijective (fun (V : Fin (s * K) → R) (c : Fin s) (n : Fin K) =>
      vecDigit (ssGen g zθ) V c n) := by
  sorry

/-- **`prop:law`** (multi-digit law, every `s`, every depth `i`): for a self-similar scramble with
local roots `w(z_c(θx)) = θx` (`eq:roots`; `deg w ≤ s`, `θ` a unit) and a right inverse `G` of the
frame matrix, at EVERY level `K ≥ l` the carry response is
`D_i(l)[c][c'] = δ_{cc'} - ∑_{a ≤ i} ∑_b [x^a] M[c][b] [x^{l+i-a}] Ĝ[b][c']` (`lawD`): the law does not
depend on `K`. -/
theorem law [Fintype R] [DecidableEq R] (g zθ : Fin s → PowerSeries R) (w : Polynomial R)
    (hw : w.natDegree ≤ s) (θ θ' : R) (hθ : θ * θ' = 1)
    (hroot : ∀ c, Polynomial.aeval (zθ c) w = PowerSeries.C θ * X)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (hMG : frameM g zθ * G = 1)
    (K i l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) (c c' : Fin s) :
    IsCarryEntry (ssGen g zθ) K i l c c' (lawD g zθ G i l c c') := by
  sorry

/-- **`prop:law`, first form**: `D_i(l) = [x^{l+i}] M_{>i} Ĝ`. -/
theorem law_first (g zθ : Fin s → PowerSeries R) (G : Matrix (Fin s) (Fin s) (PowerSeries R))
    (hMG : frameM g zθ * G = 1) (i l : ℕ) (c c' : Fin s) :
    lawD g zθ G i l c c' = coeff (l + i) ((frameTail g zθ i * G) c c' * PowerSeries.mk 1) := by
  sorry

/-- **The frame matrix of a frame is invertible** (proof of `prop:law`: `M(0)[c][b] = g_c(0) a_c^b` is a
Vandermonde matrix with nonzero row factors): over a field, distinct places `a_c = z_c(0)` and
`g_c(0) ≠ 0` give a two-sided inverse `G` of `M`. -/
theorem frame_inv {F : Type*} [Field F] (g zθ : Fin s → PowerSeries F)
    (hplace : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0) :
    ∃ G : Matrix (Fin s) (Fin s) (PowerSeries F), frameM g zθ * G = 1 ∧ G * frameM g zθ = 1 := by
  sorry

end Law

section Bridge

variable {R : Type*} [CommRing R] {s q : ℕ} [NeZero q]

/-- If the prefix `P_{sK}` is a `(0,sK,s)`-net, every pattern of cell digits (digits `0, …, K-1` of
every coordinate) is attained by exactly one index vector `V ∈ R^{sK}`. -/
theorem cell_existsUnique (D : DigitCode R q) (C : Gen s R) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) (T : Fin s → ℕ → R) :
    ∃! V : Fin (s * K) → R, ∀ c, ∀ n < K, vecDigit C V c n = T c n := by
  sorry

/-- **Carry responses exist** for every digital sequence whose prefix `P_{sK}` is a `(0,sK,s)`-net
(the hypothesis `IsCarryEntry` of `cert`, `cert_one` can always be met). -/
theorem carry_exists (D : DigitCode R q) (C : Gen s R) (K : ℕ) (hnet : BlockNet0 D C (s * K) 0)
    (i l : ℕ) (c c' : Fin s) : ∃ d, IsCarryEntry C K i l c c' d := by
  sorry

end Bridge

section Unique

variable {R : Type*} [CommRing R] {s : ℕ}

/-- Carry responses are unique. -/
theorem carryEntry_unique (C : Gen s R) (K i l : ℕ) (c c' : Fin s) {d d' : R}
    (h : IsCarryEntry C K i l c c' d) (h' : IsCarryEntry C K i l c c' d') : d = d' := by
  sorry

end Unique

/-- **`thm:WF` (separation) from the law of coordinate `1`** (earlier `lem:WFlaw`): if the own response of coordinate `1` vanishes and its
cross response is `½(-a)^l` at every level, then `c(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`. -/
theorem WF_sep_of_law (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (hO : ∀ K l : ℕ, 1 ≤ l → l ≤ K → IsCarryEntry (WFgen p a) K 0 l 1 1 0)
    (hX : ∀ K l : ℕ, 1 ≤ l → l ≤ K →
      IsCarryEntry (WFgen p a) K 0 l 1 0 ((2 : ZMod p)⁻¹ * (-a) ^ l))
    (K : ℕ) (hK : 1 ≤ K) :
    SepAtLevel p 2 K (seqPoint (zcode p) (WFgen p a)) (((p : ℝ) - 3) / (2 * p)) := by
  sorry

/-! ## Stage S3: the Faure frame (`lem:gform`) and the brick walls (`lem:WFlaw`) -/

/-- **`prop:law` at depth `i = 0`** (the one-digit law): `D(l)[c][c'] = δ_{cc'} - ∑_b M(0)[c][b] Ĝ_l[b][c']`. -/
theorem lawD_zero {R : Type*} [CommRing R] {s : ℕ} (g zθ : Fin s → PowerSeries R)
    (G : Matrix (Fin s) (Fin s) (PowerSeries R)) (l : ℕ) (c c' : Fin s) :
    lawD g zθ G 0 l c c' = (if c = c' then 1 else 0) -
      ∑ b, constantCoeff (frameM g zθ c b) * coeff l (G b c' * PowerSeries.mk 1) := by
  sorry

section Faure

variable {F : Type*} [Field F]

/-- `M G = 1` for the Faure frame matrix `M = ((g_0, g_0 z_0), (g_1, g_1 z_1))`, `k_c ρ g_c = 1`. -/
theorem faure_inv (z0 z1 g0 g1 k0 k1 : PowerSeries F)
    (hk0 : k0 * ((z1 - z0) * g0) = 1) (hk1 : k1 * ((z1 - z0) * g1) = 1) :
    frameM ![g0, g1] ![z0, z1] * faureG z0 z1 k0 k1 = 1 := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:gform`** (one-digit law of a self-similar scramble of the Faure frame, in the multipliers):
`D(l)[c][c'] = [x^l] 𝒟[c][c']/(1-x)` with `𝒟 = I - M(0) G`, entry by entry. -/
theorem gform (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (l : ℕ) :
    lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 0 =
        coeff l ((1 - C (constantCoeff g0) * z1 * k0) * PowerSeries.mk 1) ∧
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 1 =
        coeff l (C (constantCoeff g0) * z0 * k1 * PowerSeries.mk 1) ∧
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        coeff l (C (constantCoeff g1) * z0 * k0 * PowerSeries.mk 1) ∧
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 =
        coeff l ((1 - C (constantCoeff g1) * z1 * k1) * PowerSeries.mk 1) := by
  sorry

/-- `z_0 = -θx / z_1` (the scaled local roots of the Faure frame, `z_0 z_1 = -θx`). -/
theorem faure_z0 (θ : F) (z0 z1 : PowerSeries F) (hz1 : constantCoeff z1 ≠ 0)
    (hprod : z0 * z1 = -(C θ * X)) : z0 = -(C θ * X) * z1⁻¹ := by
  sorry

/-- All partial sums of `D` vanish iff `D = 0`. -/
theorem partial_sums_zero (D : PowerSeries F) :
    (∀ l, coeff l (D * PowerSeries.mk 1) = 0) ↔ D = 0 := by
  sorry

/-- **`prop:freeze` (a)**: for a self-similar scramble of the Faure frame, `O_1^{(l)} = 0` for all
`l ≥ 1` iff `g_1 = g_1(0) z_1/ρ`. -/
theorem freeze_a (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (hg1 : constantCoeff g1 ≠ 0) (hk1 : k1 * ((z1 - z0) * g1) = 1) :
    (∀ l, 1 ≤ l → lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 = 0) ↔
      g1 = C (constantCoeff g1) * z1 * (z1 - z0)⁻¹ := by
  sorry

/-- **`prop:freeze` (b)**: for a self-similar scramble of the Faure frame with scale `θ ≠ 0` and
`g_1(0) ≠ 0`, `X_{1←0}^{(l)}` does not depend on `l ≥ 1` iff `g_0 = g_0(0)/(ρ z_1)`, and then
`X_{1←0}^{(l)} = -θ g_1(0)/g_0(0)` for all `l ≥ 1`. Part (c) (`O_0 = 1 - z_1²`) is `freeze_c` (stage V0). -/
theorem freeze_b (θ : F) (z0 z1 g0 g1 k0 k1 : PowerSeries F) (hz0 : constantCoeff z0 = 0)
    (hsum : z0 + z1 = 1) (hprod : z0 * z1 = -(C θ * X)) (hθ : θ ≠ 0)
    (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0)
    (hk0 : k0 * ((z1 - z0) * g0) = 1) :
    ((∀ l, 1 ≤ l → lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 1 1 0) ↔
      g0 = C (constantCoeff g0) * ((z1 - z0) * z1)⁻¹) ∧
    (g0 = C (constantCoeff g0) * ((z1 - z0) * z1)⁻¹ → ∀ l, 1 ≤ l →
      lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        -(θ * constantCoeff g1 * (constantCoeff g0)⁻¹)) := by
  sorry

end Faure

section General

variable {F : Type*} [Field F]

/-- A series whose coefficients satisfy the recursion of `sqrtCoeff` squares to `1 + a x`. -/
theorem sq_of_rec (h2 : (2 : F) ≠ 0) (a : F) (f : ℕ → F) (h0 : f 0 = 1)
    (hs : ∀ n, f (n + 1) =
      ((if n = 0 then a else 0) - ∑ i : Fin n, f (i + 1) * f (n - i)) * (2 : F)⁻¹) :
    (PowerSeries.mk f) ^ 2 = 1 + C a * X := by
  sorry

/-- `eq:roots` for `W^±`: `z_c² - z_c = (a/4) x`. -/
theorem wf_root (h2 : (2 : F) ≠ 0) (a : F) (ρ : PowerSeries F) (hρ2 : ρ ^ 2 = 1 + C a * X) (c : Fin 2) :
    Polynomial.aeval (wfZ ρ c) (Polynomial.X ^ 2 - Polynomial.X : Polynomial F) =
      C ((2 : F)⁻¹ * (2 : F)⁻¹ * a) * X := by
  sorry

/-- `E (1 + a x) = -(a h) x` ⟹ `[x^l] E = h (-a)^l` for `l ≥ 1` (the coefficients of `-(a h) x/(1 + a x)`). -/
theorem coeff_geom (E : PowerSeries F) (a h : F) (hE : E * (1 + C a * X) = -(C a * C h * X)) :
    ∀ l, 1 ≤ l → coeff l E = h * (-a) ^ l := by
  sorry

/-- **[Legacy — earlier version, not in V3; `comparatorGeoSeqLegacy.json`]** **`lem:WFlaw`** over `F` (both coordinate-1 responses): `O_1^{(l)} = 0` and
`X_{1←0}^{(l)} = ½ (-a)^l` for every level `K` and `1 ≤ l ≤ K`. -/
theorem wf_law [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (a : F) (ρ : PowerSeries F)
    (ha : a ≠ 0) (hρ0 : constantCoeff ρ = 1) (hρ2 : ρ ^ 2 = 1 + C a * X)
    (K l : ℕ) (hl : 1 ≤ l) (hlK : l ≤ K) :
    IsCarryEntry (ssGen (wfG ρ) (wfZ ρ)) K 0 l 1 1 0 ∧
      IsCarryEntry (ssGen (wfG ρ) (wfZ ρ)) K 0 l 1 0 ((2 : F)⁻¹ * (-a) ^ l) := by
  sorry

end General

/-- `ρ = √(1 + a x)` (`rhoWF`, defined by the recursion `sqrtCoeff`) squares to `1 + a x`. -/
theorem rhoWF_sq (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (a : ZMod p) :
    rhoWF p a ^ 2 = 1 + C a * X := by
  sorry

end GeoSeq
