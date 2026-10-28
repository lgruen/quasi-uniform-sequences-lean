/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V94Dyadic
public import GeoSeq.LIa
public import GeoSeq.WFLaw
public import GeoSeq.Fidelity

@[expose] public section

/-!
# GeoSeq stage V9-4 (part 4): the brick wall (`ex:brickwall`, `def:WF`, `thm:WF`)

* `resStar_faure_ss` (the residue form ↔ the multiplier form for `s = 2`, any field): the staggered residue
  sequence on the Faure places `(0, 1)` with `c⋆ = 1` is the self-similar scramble `ssGen g zθ` with the scaled local
  roots `zθ_c = z_c(θx)` and the multipliers `g_0 = μ_0 θ u_0(θx)`, `g_1 = μ⋆ u_1(θx) z_1(θx)²` (`u_c` the e-basis
  weights; the change of coordinate is `ebas_eq_x`, stage S11). This is `lem:resform`(b) for this sequence.
* **`brickWall_eq_WFgen`** (bridge, every prime `p ≥ 3`): the V4 brick wall (the staggered residue sequence of
  `ex:brickwall`, `brickWall`) equals the V3 multiplier form `WFgen p (-1)` of `W^-`
  (`g_0 = 2/(√(1-x)(1+√(1-x)))`, `g_1 = (1+√(1-x))/√(1-x)`, `z_{0,1}(θx) = (1 ∓ √(1-x))/2`). Hence all V3 results
  on `WFgen p (-1)` (`WF_net`, `WF_sep`, `WF_allN`, `WF_mesh`, `lem:WFlaw`) hold for the V4 definition.
* `brickWall_C0`, `brickWall_C1` (**`ex:brickwall`**, `p = 7`): the leading `4 × 4` blocks are those of
  `ex:running`.
* **`brickWall_WF`** (**`thm:WF`** for the V4 definition, proof via `cor:dyadic` at `s = 2`): for every prime
  `p ≥ 5`, `W^-` is a digital `(0,2)`-sequence with `sep(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`, quasi-uniform.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Field
variable {F : Type*} [Field F]

local notation "PS" => PowerSeries F

lemma scrDig_resStarL {s : ℕ} (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k : Fin s → F)
    (c : Fin s) (n : ℕ) (V : F[X]) :
    scrDig (a c) (resStarL a θ cs μs k c) n V = stagMu cs μs k c * θ ^ stagLev cs c n *
      coeff n ((Polynomial.taylor (a c) V : PS) *
        (Polynomial.taylor (a c) (placeCo a (stagK cs (stagLev cs c n)) c) : PS)⁻¹) := by
  rw [scrDig, coeff_mul_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [resStarL, Polynomial.coeff_coe]
  ring

lemma wCo_faurePl_zero : wCo (faurePl : Fin 2 → F) 0 = Polynomial.X - Polynomial.C 1 := by
  rw [wCo, show (univ.erase (0 : Fin 2)) = {1} by decide, Finset.prod_singleton]; rfl

lemma wCo_faurePl_one : wCo (faurePl : Fin 2 → F) 1 = Polynomial.X := by
  rw [wCo, show (univ.erase (1 : Fin 2)) = {0} by decide, Finset.prod_singleton]
  simp [faurePl]

lemma cc_rescale (θ : F) (f : PS) : constantCoeff (rescale θ f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
    coeff_zero_eq_constantCoeff_apply]

lemma rescale_C' (θ a : F) : rescale θ (C a : PS) = C a := by
  ext n; simp only [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]

/-- `u_c(θx) = 1 / ((2 z_c(θx) - 1)(z_c(θx) - a_c + δ_c))`. -/
lemma rescale_uF (θ : F) (c : Fin 2) :
    rescale θ (uF c : PS) = ((C 2 * rescale θ (zF c) - 1) *
      (rescale θ (zF c) - C (faurePl c) + C (faureDel c)))⁻¹ := by
  have hQ := constantCoeff_uF_inv (F := F) c
  have hQθ : constantCoeff ((C 2 * rescale θ (zF c) - 1) *
      (rescale θ (zF c) - C (faurePl c) + C (faureDel c)) : PS) = 1 := by
    rw [← hQ]; simp [map_mul, map_sub, map_add, cc_rescale]
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [hQθ]; exact one_ne_zero)]
  have e : (C 2 * rescale θ (zF c) - 1) * (rescale θ (zF c) - C (faurePl c) + C (faureDel c)) =
      rescale θ ((C 2 * zF c - 1) * (zF c - C (faurePl c) + C (faureDel c)) : PS) := by
    simp only [map_mul, map_sub, map_add, rescale_C', map_one]
  rw [e, ← map_mul, uF, PowerSeries.inv_mul_cancel _ (by rw [hQ]; exact one_ne_zero), map_one]

/-- **The brick-wall family in the multiplier form** (`lem:resform`(b) for `s = 2`, `c⋆ = 1`, Faure places):
`𝓡^⋆ = ssGen g zθ` with `zθ_c = z_c(θx)`, `g_0 = μ_0 θ u_0(θx)`, `g_1 = μ⋆ u_1(θx) z_1(θx)²`. -/
theorem resStar_faure_ss (θ μs : F) (k : Fin 2 → F) :
    resStar faurePl θ 1 μs k =
      ssGen ![C (stagMu 1 μs k 0 * θ) * rescale θ (uF 0),
          C μs * rescale θ (uF 1) * rescale θ (zF 1) ^ 2]
        (fun c => rescale θ (zF c)) := by
  rw [resStar, scrGen_eq_ssGen_iff]
  refine Fin.forall_fin_two.mpr ⟨fun n V => ?_, fun n V => ?_⟩
  · rw [scrDig_resStarL]
    -- `c = 0 ≠ c⋆`: digit `n` is `μ_0 θ^{n+1} ε_{0,n}(V)`
    show stagMu 1 μs k 0 * θ ^ stagLev 1 0 n * _ = _
    have hl : stagLev (1 : Fin 2) 0 n = n + 1 := by simp [stagLev]
    rw [hl, placeCo_stagK_ne faurePl 1 0 (by decide), wCo_faurePl_zero]
    have hE : coeff n ((Polynomial.taylor (faurePl 0 : F) V : PS) *
        (Polynomial.taylor (faurePl 0 : F) ((Polynomial.X - Polynomial.C (faurePl 1 : F)) *
          (Polynomial.X - Polynomial.C (1 : F)) ^ (n + 1)) : PS)⁻¹) = ebas 0 n V := by
      simp only [faurePl_zero, faurePl_one, Polynomial.taylor_zero]
      rw [ebas, faurePl_zero, faureDel_zero, Polynomial.taylor_zero, Polynomial.coe_mul,
        Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, ← pow_succ',
        map_neg, sub_eq_add_neg]
    rw [hE, show (Matrix.vecCons (C (stagMu 1 μs k 0 * θ) * rescale θ (uF 0))
      ![C μs * rescale θ (uF 1) * rescale θ (zF 1) ^ 2] : Fin 2 → PS) 0 =
        C (stagMu 1 μs k 0 * θ) * rescale θ (uF 0) from rfl, mul_assoc (C _), coeff_C_mul,
      ← ebas_eq_x]
    show stagMu 1 μs k 0 * θ ^ (n + 1) * ebas 0 n V = stagMu 1 μs k 0 * θ * (θ ^ n * ebas 0 n V)
    ring
  · -- `c = c⋆ = 1`: digit `n` is `μ⋆ θ^n ε_{1,n}(z² V)`
    rw [scrDig_resStarL]
    show stagMu 1 μs k 1 * θ ^ stagLev 1 1 n * _ = _
    have hl : stagLev (1 : Fin 2) 1 n = n := by simp [stagLev]
    have hm : stagMu (1 : Fin 2) μs k 1 = μs := by simp [stagMu]
    rw [hl, hm, placeCo_stagK_self, wCo_faurePl_one]
    have hE : coeff n ((Polynomial.taylor (faurePl 1 : F) V : PS) *
        (Polynomial.taylor (faurePl 1 : F) (Polynomial.X ^ n) : PS)⁻¹) =
        ebas 1 n (Polynomial.X ^ 2 * V) := by
      rw [ebas, faurePl_one, faureDel_one, Polynomial.taylor_mul, Polynomial.taylor_X_pow,
        Polynomial.taylor_X_pow, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_pow,
        Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, mul_comm _ (Polynomial.taylor 1 V : PS),
        mul_assoc, pow_mul_inv_pow (1 : F) one_ne_zero 2 (n + 2) (by omega),
        show n + 2 - 2 = n by omega]
    rw [hE, show (Matrix.vecCons (C (stagMu 1 μs k 0 * θ) * rescale θ (uF 0))
      ![C μs * rescale θ (uF 1) * rescale θ (zF 1) ^ 2] : Fin 2 → PS) 1 =
        C μs * rescale θ (uF 1) * rescale θ (zF 1) ^ 2 from rfl]
    have h2 := ebas_eq_x θ 1 n (Polynomial.X ^ 2 * V)
    rw [show Polynomial.aeval (rescale θ (zF 1)) (Polynomial.X ^ 2 * V) = rescale θ (zF 1) ^ 2 *
      Polynomial.aeval (rescale θ (zF 1)) V by rw [map_mul, Polynomial.aeval_X_pow]] at h2
    show μs * θ ^ n * ebas 1 n (Polynomial.X ^ 2 * V) = _
    rw [mul_assoc, h2, show C μs * rescale θ (uF 1) * rescale θ (zF 1) ^ 2 *
      Polynomial.aeval (rescale θ (zF 1)) V = C μs * (rescale θ (uF 1) *
        (rescale θ (zF 1) ^ 2 * Polynomial.aeval (rescale θ (zF 1)) V)) by ring, coeff_C_mul]

/-- Uniqueness of the local root: two power series with `z² - z = z'² - z'` and `(z + z' - 1)(0) ≠ 0` agree. -/
lemma root_unique (z z' : PS) (h : z ^ 2 - z = z' ^ 2 - z')
    (h0 : constantCoeff (z + z' - 1) ≠ 0) : z = z' := by
  have hprod : (z - z') * (z + z' - 1) = 0 := by linear_combination h
  have hne : z + z' - 1 ≠ 0 := fun h' => h0 (by rw [h', map_zero])
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne)

lemma rescale_zF_sq (θ : F) (c : Fin 2) :
    rescale θ (zF c : PS) ^ 2 - rescale θ (zF c) = C θ * X := by
  have hT := tRoot_add_sq (F := F)
  have h : (zF c : PS) ^ 2 - zF c = X := by
    fin_cases c
    · show (-tRoot : PS) ^ 2 - -tRoot = X; linear_combination hT
    · show ((1 : PS) + tRoot) ^ 2 - (1 + tRoot) = X; linear_combination hT
  rw [← map_pow, ← map_sub, h, rescale_X]


/-! ### The brick wall over a field of characteristic `≠ 2` (`ρ = √(1 - x)`)

All algebra is done over a general field (so that `ring` sees one set of instances); the `ℤ/pℤ` statements are
instances. -/

variable (h2 : (2 : F) ≠ 0) (ρ : PowerSeries F) (hρ : ρ ^ 2 = 1 + C (-1) * X) (hρ0 : constantCoeff ρ = 1)
include h2 hρ hρ0

lemma brick_z (c : Fin 2) :
    rescale (-(4 : F)⁻¹) (zF c) = ![C (2 : F)⁻¹ * (1 - ρ), C (2 : F)⁻¹ * (1 + ρ)] c := by
  have hC' : (C (2 : F)⁻¹ : PS) * 2 = 1 := by
    rw [show (2 : PS) = C 2 from (map_ofNat C 2).symm, ← map_mul, inv_mul_cancel₀ h2, map_one]
  refine root_unique _ _ ?_ ?_
  · rw [rescale_zF_sq]
    have hW : (![C (2 : F)⁻¹ * (1 - ρ), C (2 : F)⁻¹ * (1 + ρ)] c : PS) ^ 2 -
        ![C (2 : F)⁻¹ * (1 - ρ), C (2 : F)⁻¹ * (1 + ρ)] c = C (2 : F)⁻¹ * C (2 : F)⁻¹ * (ρ ^ 2 - 1) := by
      fin_cases c
      · show (C (2 : F)⁻¹ * (1 - ρ)) ^ 2 - C (2 : F)⁻¹ * (1 - ρ) = _
        linear_combination ((1 - ρ) * C (2 : F)⁻¹) * hC'
      · show (C (2 : F)⁻¹ * (1 + ρ)) ^ 2 - C (2 : F)⁻¹ * (1 + ρ) = _
        linear_combination ((1 + ρ) * C (2 : F)⁻¹) * hC'
    rw [hW, hρ, ← map_mul, show (1 + C (-1) * X - 1 : PS) = C (-1) * X by ring, ← mul_assoc, ← map_mul]
    congr 2
    rw [show (4 : F) = 2 * 2 by norm_num, mul_inv]; ring
  · have hc : constantCoeff (rescale (-(4 : F)⁻¹) (zF c)) = faurePl c := by
      rw [cc_rescale, constantCoeff_zF]
    rw [map_sub, map_add, hc, map_one]
    fin_cases c
    · show (faurePl 0 : F) + constantCoeff (C (2 : F)⁻¹ * (1 - ρ)) - 1 ≠ 0
      rw [map_mul, map_sub, map_one, hρ0, constantCoeff_C, faurePl_zero]; norm_num
    · show (faurePl 1 : F) + constantCoeff (C (2 : F)⁻¹ * (1 + ρ)) - 1 ≠ 0
      rw [map_mul, map_add, map_one, hρ0, constantCoeff_C, faurePl_one, one_add_one_eq_two,
        inv_mul_cancel₀ h2]
      norm_num

lemma brick_g0 :
    C (stagMu (1 : Fin 2) (2 : F) ![(2 : F)⁻¹, 0] 0 * -(4 : F)⁻¹) * rescale (-(4 : F)⁻¹) (uF 0) =
      C (2 : F) * ρ * ((1 - X : PS) * (1 + ρ))⁻¹ := by
  have hCC : (C (2 : F) : PS) * C (2 : F)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h2, map_one]
  have hC' : (C (2 : F)⁻¹ : PS) * 2 = 1 := by
    rw [show (2 : PS) = C 2 from (map_ofNat C 2).symm, ← map_mul, inv_mul_cancel₀ h2, map_one]
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hμθ : stagMu (1 : Fin 2) (2 : F) ![(2 : F)⁻¹, 0] 0 * -(4 : F)⁻¹ = 1 := by
    simp only [stagMu, show (0 : Fin 2) ≠ 1 by decide, if_false, Matrix.cons_val_zero]
    field_simp
    norm_num
  rw [hμθ, map_one, one_mul, rescale_uF, brick_z h2 ρ hρ hρ0 0, faurePl_zero, faureDel_zero]
  show ((C 2 * (C (2 : F)⁻¹ * (1 - ρ)) - 1) * (C (2 : F)⁻¹ * (1 - ρ) - C 0 + C (-1)))⁻¹ = _
  have hQ : (C 2 * (C (2 : F)⁻¹ * (1 - ρ)) - 1) * (C (2 : F)⁻¹ * (1 - ρ) - C 0 + C (-1)) =
      C (2 : F)⁻¹ * (ρ * (1 + ρ)) := by
    rw [map_zero, map_neg, map_one, show (C 2 : PS) = 2 from map_ofNat C 2]
    linear_combination ((1 - ρ) ^ 2 * C (2 : F)⁻¹ - 1) * hC'
  rw [hQ]
  have hc : constantCoeff (C (2 : F)⁻¹ * (ρ * (1 + ρ))) ≠ 0 := by
    rw [map_mul, map_mul, map_add, map_one, constantCoeff_C, hρ0, one_mul]
    exact mul_ne_zero (inv_ne_zero h2) (by simpa [one_add_one_eq_two] using h2)
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc]
  have hu : constantCoeff ((1 - X) * (1 + ρ) : PS) ≠ 0 := by
    rw [map_mul, map_sub, map_add, map_one, constantCoeff_X, hρ0, sub_zero, one_mul]
    simpa [one_add_one_eq_two] using h2
  have hρ' : ρ * ρ = 1 - X := by rw [← sq, hρ, map_neg, map_one]; ring
  calc C (2 : F) * ρ * ((1 - X) * (1 + ρ))⁻¹ * (C (2 : F)⁻¹ * (ρ * (1 + ρ)))
      = (C (2 : F) * C (2 : F)⁻¹) * ((ρ * ρ) * (1 + ρ)) * ((1 - X) * (1 + ρ))⁻¹ := by ring
    _ = ((1 - X) * (1 + ρ)) * ((1 - X) * (1 + ρ))⁻¹ := by rw [hCC, hρ', one_mul]
    _ = 1 := PowerSeries.mul_inv_cancel _ hu

lemma brick_g1 :
    C (2 : F) * rescale (-(4 : F)⁻¹) (uF 1) * rescale (-(4 : F)⁻¹) (zF 1) ^ 2 = (1 + ρ) * ρ⁻¹ := by
  have hCC : (C (2 : F) : PS) * C (2 : F)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h2, map_one]
  have hC' : (C (2 : F)⁻¹ : PS) * 2 = 1 := by
    rw [show (2 : PS) = C 2 from (map_ofNat C 2).symm, ← map_mul, inv_mul_cancel₀ h2, map_one]
  rw [rescale_uF, brick_z h2 ρ hρ hρ0 1, faurePl_one, faureDel_one]
  show C (2 : F) * ((C 2 * (C (2 : F)⁻¹ * (1 + ρ)) - 1) * (C (2 : F)⁻¹ * (1 + ρ) - C 1 + C 1))⁻¹ *
    (C (2 : F)⁻¹ * (1 + ρ)) ^ 2 = _
  set W := C (2 : F)⁻¹ * (1 + ρ) with hW
  have hQ : (C 2 * W - 1) * (W - C 1 + C 1) = ρ * W := by
    rw [hW, show (C 2 : PS) = 2 from map_ofNat C 2]
    linear_combination (C (2 : F)⁻¹ * (1 + ρ) * (1 + ρ)) * hC'
  rw [hQ]
  have hW0 : constantCoeff W ≠ 0 := by
    rw [hW, map_mul, map_add, map_one, constantCoeff_C, hρ0]
    exact mul_ne_zero (inv_ne_zero h2) (by simpa [one_add_one_eq_two] using h2)
  rw [PowerSeries.mul_inv_rev]
  calc C (2 : F) * (W⁻¹ * ρ⁻¹) * W ^ 2 = C (2 : F) * W * (W * W⁻¹) * ρ⁻¹ := by ring
    _ = C (2 : F) * W * ρ⁻¹ := by rw [PowerSeries.mul_inv_cancel _ hW0, mul_one]
    _ = (C (2 : F) * C (2 : F)⁻¹) * (1 + ρ) * ρ⁻¹ := by rw [hW]; ring
    _ = (1 + ρ) * ρ⁻¹ := by rw [hCC, one_mul]

/-- The brick-wall family over a field of characteristic `≠ 2`: the staggered residue sequence of `ex:brickwall`
is `ssGen g zθ` with `g = (2ρ/((1-x)(1+ρ)), (1+ρ)/ρ)` and `zθ = ((1-ρ)/2, (1+ρ)/2)`, `ρ = √(1 - x)`. -/
theorem brick_ss :
    resStar faurePl (-(4 : F)⁻¹) 1 2 ![(2 : F)⁻¹, 0] =
      ssGen ![C (2 : F) * ρ * ((1 - X : PS) * (1 + ρ))⁻¹, (1 + ρ) * ρ⁻¹]
        ![C (2 : F)⁻¹ * (1 - ρ), C (2 : F)⁻¹ * (1 + ρ)] := by
  rw [resStar_faure_ss]
  congr 1
  · funext c
    fin_cases c
    · exact brick_g0 h2 ρ hρ hρ0
    · exact brick_g1 h2 ρ hρ hρ0
  · funext c; exact brick_z h2 ρ hρ hρ0 c

omit h2 hρ hρ0

/-- The weight of the staggered coordinate does not enter `𝓡^⋆_v`. -/
lemma resStar_congr {s : ℕ} (a : Fin s → F) (θ : F) (cs : Fin s) (μs : F) (k k' : Fin s → F)
    (h : ∀ c, c ≠ cs → k c = k' c) : resStar a θ cs μs k = resStar a θ cs μs k' := by
  have hm : stagMu cs μs k = stagMu cs μs k' := by
    funext c; unfold stagMu; split_ifs with hc
    · rfl
    · rw [h c hc]
  unfold resStar resStarL
  rw [hm]

end Field

section WF
variable {p : ℕ} [Fact p.Prime]

/-- **The bridge** (`def:WF`, every prime `p ≥ 3`): the V4 brick wall (the staggered residue sequence of
`ex:brickwall`) is the V3 multiplier form `WFgen p (-1)` of `W^-`. -/
theorem brickWall_eq_WFgen (hp : 3 ≤ p) : brickWall p = WFgen p (-1) :=
  brick_ss (two_ne_zero_of_ne_two (by omega)) (rhoWF p (-1)) (rhoWF_sq p hp (-1)) (rhoWF_const p (-1))

/-- **`ex:brickwall`** (`p = 7`): the leading `4 × 4` block of `C_0` of the V4 brick wall is that of
`ex:running`. -/
theorem brickWall_C0 :
    (Matrix.of fun n k : Fin 4 => brickWall 7 0 n k) = !![1, 0, 0, 0; 6, 2, 0, 0; 5, 2, 4, 0; 0, 1, 5, 1] := by
  rw [brickWall_eq_WFgen (by norm_num)]; exact ex_running_C0

/-- **`ex:brickwall`** (`p = 7`): the leading `4 × 4` block of `C_1` of the V4 brick wall is that of
`ex:running`. -/
theorem brickWall_C1 :
    (Matrix.of fun n k : Fin 4 => brickWall 7 1 n k) = !![2, 2, 2, 2; 4, 0, 3, 6; 3, 1, 0, 0; 6, 1, 2, 0] := by
  rw [brickWall_eq_WFgen (by norm_num)]; exact ex_running_C1

lemma faurePl_injective_two : Function.Injective (faurePl : Fin 2 → ZMod p) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h (by simp [faurePl])
  · exact absurd h (by simp [faurePl])
  · rfl

/-- **`thm:WF`** (V4 definition; proof via `cor:dyadic` with `s = 2`): for every prime `p ≥ 5` the brick wall is a
digital `(0,2)`-sequence with `sep(P_{2K}) ≥ (p-3)/(2p)` for every `K ≥ 1`, and it is quasi-uniform. -/
theorem brickWall_WF (hp : 5 ≤ p) :
    IsSeq0 (zcode p) (brickWall p) ∧
      (∀ K, 1 ≤ K → SepAtLevel p 2 K (seqPoint (zcode p) (brickWall p)) (((p : ℝ) - 3) / (2 * p))) ∧
      IsQuasiUniform (seqPoint (zcode p) (brickWall p)) := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have h2 := two_ne_zero_of_ne_two hp2
  have hb : brickWall p = resStar faurePl (-(4 : ZMod p)⁻¹) 1 2 (dyadicK p (stdOrder 1)) := by
    rw [brickWall]
    refine resStar_congr _ _ _ _ _ _ fun c hc => ?_
    fin_cases c
    · simp [dyadicK, stdOrder]
    · exact absurd rfl hc
  have h4 : (4 : ZMod p) ≠ 0 := by rw [show (4 : ZMod p) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  obtain ⟨hseq, hsep, hqu⟩ := dyadic_qu (s := 2) le_rfl (by norm_num; omega) faurePl faurePl_injective_two
    (-(4 : ZMod p)⁻¹) (neg_ne_zero.mpr (inv_ne_zero h4)) 1 2 h2 (stdOrder 1)
    (fun c c' hc hc' h => stdOrder_inj 1 c c' hc hc' h) (fun c hc => stdOrder_lt 1 c hc)
  rw [hb]
  refine ⟨hseq, fun K hK => ?_, hqu⟩
  have hv : ((((p / 2 ^ (2 - 1) : ℕ) : ℝ) - 1) / p) = ((p : ℝ) - 3) / (2 * p) := by
    have hd : 2 * (p / 2) + 1 = p := by omega
    have hr : ((p / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
      have : (2 : ℝ) * ((p / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hd
      linarith
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    norm_num [hr]
    field_simp
    ring
  rw [← hv]; exact hsep K hK

end WF

end GeoSeq
