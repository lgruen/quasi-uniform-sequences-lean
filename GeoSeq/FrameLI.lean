/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.FrameLaw

@[expose] public section

/-!
# GeoSeq stage S10: `prop:LI`(c) and `prop:depthdir` for every frame

See `GeoSeq/FrameLaw.lean` for the setting. `ψ = freeSer g zθ c'` is the free series of column `c'`
(`prop:LI`(a) with `ϖ = dz`, written in `x`: `ψ(x) = ψ_{c'}(θx)` of the paper).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

variable {F : Type*} [Field F] {s : ℕ}

local notation "PS" => PowerSeries F

lemma cc_eq_place (zθ : Fin s → PS) (c : Fin s) : constantCoeff (zθ c) = ssPlace zθ c := rfl

lemma placeDer_ne (zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s) :
    placeDer zθ c' ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun c hc => sub_ne_zero.2 fun h => (Finset.mem_erase.1 hc).1 (hinj h.symm)

lemma constantCoeff_prodZ (zθ : Fin s → PS) (c' : Fin s) :
    constantCoeff (∏ c ∈ univ.erase c', (zθ c' - zθ c)) = placeDer zθ c' := by
  simp [placeDer, map_prod, ssPlace]

/-- `ψ(0) = 1`. -/
theorem freeSer_const (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (c' : Fin s) : constantCoeff (freeSer g zθ c') = 1 := by
  rw [freeSer, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv, map_mul,
    constantCoeff_prodZ]
  exact mul_inv_cancel₀ (mul_ne_zero (hg c') (placeDer_ne zθ hinj c'))

lemma freeSer_mul (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (c' : Fin s) :
    freeSer g zθ c' * (g c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c)) =
      C (constantCoeff (g c') * placeDer zθ c') := by
  have hP : constantCoeff (g c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c)) ≠ 0 := by
    rw [map_mul, constantCoeff_prodZ]; exact mul_ne_zero (hg c') (placeDer_ne zθ hinj c')
  rw [freeSer, mul_assoc, PowerSeries.inv_mul_cancel _ hP, mul_one]

/-- The column multiplier from the free series:
`g_{c'} = g_{c'}(0) w'(a_{c'}) / (ψ ∏_{c≠c'}(z_{c'}-z_c))`. -/
lemma g_of_freeSer (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (c' : Fin s) :
    g c' = C (constantCoeff (g c') * placeDer zθ c') *
      (freeSer g zθ c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹ := by
  have hc : constantCoeff (freeSer g zθ c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c)) ≠ 0 := by
    rw [map_mul, freeSer_const g zθ hinj hg, constantCoeff_prodZ, one_mul]
    exact placeDer_ne zθ hinj c'
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hc, ← freeSer_mul g zθ hinj hg c']
  ring

/-- `λ = (g_{c'} P(z_{c'}))⁻¹` and `ψ = g_{c'}(0) w'(a_{c'}) λ`. -/
lemma freeSer_lam (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (G : Matrix (Fin s) (Fin s) PS)
    (hMG : frameM g zθ * G = 1) (c' : Fin s) :
    freeSer g zθ c' = C (constantCoeff (g c') * placeDer zθ c') *
      ((colH G c').eval (zθ c') * ((colP zθ c').eval (zθ c'))⁻¹) := by
  have hP : constantCoeff (g c' * ∏ c ∈ univ.erase c', (zθ c' - zθ c)) ≠ 0 := by
    rw [map_mul, constantCoeff_prodZ]; exact mul_ne_zero (hg c') (placeDer_ne zθ hinj c')
  have hev : (colP zθ c').eval (zθ c') = ∏ c ∈ univ.erase c', (zθ c' - zθ c) := by
    simp [colP, Polynomial.eval_prod]
  rw [freeSer]
  congr 1
  rw [eq_comm, PowerSeries.eq_inv_iff_mul_eq_one hP, ← colLam_spec g zθ hinj hg G hMG c', hev]
  ring

/-- Directional coefficient change: if `ψ` and `ψ'` agree below `x^l`, then
`[x^l] Eψ/(1-x) - [x^l] Eψ'/(1-x) = E(0) (ψ_l - ψ'_l)`. -/
lemma coeff_dir (E ψ ψ' : PS) (l : ℕ) (h : ∀ n < l, coeff n ψ = coeff n ψ') :
    coeff l (E * ψ * PowerSeries.mk 1) - coeff l (E * ψ' * PowerSeries.mk 1) =
      constantCoeff E * (coeff l ψ - coeff l ψ') := by
  obtain ⟨r, hr⟩ : X ^ l ∣ ψ - ψ' :=
    PowerSeries.X_pow_dvd_iff.2 fun m hm => by rw [map_sub, h m hm, sub_self]
  have e : E * ψ * PowerSeries.mk 1 - E * ψ' * PowerSeries.mk 1 =
      X ^ l * (E * r * PowerSeries.mk 1) := by
    rw [← sub_mul, ← mul_sub, hr]; ring
  have e2 : coeff l ψ - coeff l ψ' = constantCoeff r := by
    rw [← map_sub, hr, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [← map_sub, e, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, e2]
  simp

/-- **`prop:LI`(c)** (every frame, normalisation `ϖ = dz`): for a self-similar scramble with free series
`ψ = freeSer g zθ c'` of column `c'`, the one-digit law `D(l) = [x^l]𝒟/(1-x)` has
`𝒟[c'][c'] = O_{c'} = 1 - ŵ_{c'}(z_{c'}) ψ` with `ŵ_{c'}(z) = ∏_{c≠c'} (z - a_c)/w'(a_{c'})`, and for
`c ≠ c'`, `𝒟[c][c'] = x X_{c←c'} = -κ_{c←c'} x χ_{cc'}(z_{c'}) ψ` with `χ_{cc'}(z) = (a_{c'} - a_c)/(z - a_c)`. -/
theorem LI_c (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0)
    (g zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (G : Matrix (Fin s) (Fin s) PS) (hMG : frameM g zθ * G = 1) (c' : Fin s) :
    (∀ l, lawD g zθ G 0 l c' c' =
      coeff l ((1 - (∏ c ∈ univ.erase c', (zθ c' - C (ssPlace zθ c))) * C (placeDer zθ c')⁻¹ *
        freeSer g zθ c') * PowerSeries.mk 1)) ∧
    (∀ c, c ≠ c' → ∀ l, lawD g zθ G 0 l c c' =
      coeff l (X * (-C (kap θ g zθ c c') *
        (C (ssPlace zθ c' - ssPlace zθ c) * (zθ c' - C (ssPlace zθ c))⁻¹) * freeSer g zθ c') *
          PowerSeries.mk 1)) := by
  set lam := (colH G c').eval (zθ c') * ((colP zθ c').eval (zθ c'))⁻¹ with hlam
  have hH := colH_eq g zθ hinj hg G hMG c'
  have hψ := freeSer_lam g zθ hinj hg G hMG c'
  rw [← hlam] at hH hψ
  have hwd := placeDer_ne zθ hinj c'
  constructor
  · intro l
    rw [law_colH, if_pos rfl, map_one, hH, Polynomial.eval_mul, Polynomial.eval_C, cc_eq_place zθ c',
      colP_own w hw hdeg θ hθ zθ hroot hinj c', hψ]
    have hk : C (placeDer zθ c')⁻¹ * C (constantCoeff (g c') * placeDer zθ c') =
        C (constantCoeff (g c')) := by
      rw [← map_mul]; congr 1; field_simp
    refine congrArg (fun t => coeff l (t * PowerSeries.mk 1)) ?_
    linear_combination ((∏ c ∈ univ.erase c', (zθ c' - C (ssPlace zθ c))) * lam) * hk
  · intro c hc l
    have hac : ssPlace zθ c' - ssPlace zθ c ≠ 0 := sub_ne_zero.2 fun h => hc (hinj h.symm)
    have hu : constantCoeff (C (ssPlace zθ c) - zθ c') ≠ 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C]
      exact sub_ne_zero.2 fun h => hc (hinj (by simpa [ssPlace] using h))
    have hu' : constantCoeff (zθ c' - C (ssPlace zθ c)) ≠ 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C]
      exact sub_ne_zero.2 fun h => hc (hinj (by simpa [ssPlace] using h.symm))
    set u := (C (ssPlace zθ c) - zθ c')⁻¹ with hudef
    have hneg : (zθ c' - C (ssPlace zθ c))⁻¹ = -u := by
      refine ((PowerSeries.eq_inv_iff_mul_eq_one hu').2 ?_).symm
      rw [show -u * (zθ c' - C (ssPlace zθ c)) = u * (C (ssPlace zθ c) - zθ c') by ring, hudef,
        PowerSeries.inv_mul_cancel _ hu]
    have hP : (colP zθ c').eval (C (ssPlace zθ c)) = u * (-(C θ * X)) := by
      rw [← colP_cross w hw hdeg θ zθ hroot hinj c c', ← mul_assoc, hudef,
        PowerSeries.inv_mul_cancel _ hu, one_mul]
    rw [law_colH, if_neg hc, map_zero, hH, Polynomial.eval_mul, Polynomial.eval_C, cc_eq_place zθ c, hP,
      hψ, hneg]
    have hk : C (kap θ g zθ c c') * C (ssPlace zθ c' - ssPlace zθ c) *
        C (constantCoeff (g c') * placeDer zθ c') = C θ * C (constantCoeff (g c)) := by
      simp only [← map_mul]; congr 1; unfold kap; have := hg c'; field_simp
    refine congrArg (fun t => coeff l (t * PowerSeries.mk 1)) ?_
    linear_combination (-(X * u * lam)) * hk

/-- **`prop:depthdir`** (depth direction): let two self-similar scrambles of the same frame differ only in
the multiplier of column `c'`, with the same `g_{c'}(0)`, and let their free series agree below `x^l`.
Then the own response `O^{(l)}` changes by `-Δψ_l` and every cross response `X^{(l+1)}_{c←c'}` by
`-κ_{c←c'} Δψ_l`: the column moves along the fixed direction `(1, (κ_{c←c'})_{c≠c'})`, and the offset depends
only on the earlier coefficients of `ψ` (paper: `ψ̄_l = -θ^l ψ_{c',l}`, our `ψ` is `ψ_{c'}(θx)`). -/
theorem depthdir (w : F[X]) (hw : w.Monic) (hdeg : w.natDegree = s) (θ : F) (hθ : θ ≠ 0)
    (zθ : Fin s → PS) (hroot : ∀ c, Polynomial.aeval (zθ c) w = C θ * X)
    (hinj : Function.Injective (ssPlace zθ)) (g g' : Fin s → PS) (hg : ∀ c, constantCoeff (g c) ≠ 0)
    (hg' : ∀ c, constantCoeff (g' c) ≠ 0) (G G' : Matrix (Fin s) (Fin s) PS)
    (hMG : frameM g zθ * G = 1) (hMG' : frameM g' zθ * G' = 1) (c' : Fin s)
    (hother : ∀ c, c ≠ c' → g c = g' c) (h0 : constantCoeff (g c') = constantCoeff (g' c')) (l : ℕ)
    (hagree : ∀ n < l, coeff n (freeSer g zθ c') = coeff n (freeSer g' zθ c')) :
    lawD g zθ G 0 l c' c' - lawD g' zθ G' 0 l c' c' =
        -(coeff l (freeSer g zθ c') - coeff l (freeSer g' zθ c')) ∧
      ∀ c, c ≠ c' → lawD g zθ G 0 (l + 1) c c' - lawD g' zθ G' 0 (l + 1) c c' =
        -(kap θ g zθ c c' * (coeff l (freeSer g zθ c') - coeff l (freeSer g' zθ c'))) := by
  obtain ⟨hO, hX⟩ := LI_c w hw hdeg θ hθ g zθ hroot hinj hg G hMG c'
  obtain ⟨hO', hX'⟩ := LI_c w hw hdeg θ hθ g' zθ hroot hinj hg' G' hMG' c'
  constructor
  · rw [hO, hO']
    set E := (∏ c ∈ univ.erase c', (zθ c' - C (ssPlace zθ c))) * C (placeDer zθ c')⁻¹
    have hE : constantCoeff E = 1 := by
      simp only [E, map_mul, map_prod, map_sub, PowerSeries.constantCoeff_C]
      rw [cc_eq_place zθ c']
      exact mul_inv_cancel₀ (placeDer_ne zθ hinj c')
    have := coeff_dir E _ _ l hagree
    rw [hE, one_mul] at this
    rw [sub_mul, sub_mul, map_sub, map_sub, one_mul, ← this]
    ring
  · intro c hc
    rw [hX c hc, hX' c hc]
    have hk : kap θ g' zθ c c' = kap θ g zθ c c' := by
      unfold kap; rw [hother c hc, h0]
    rw [hk]
    set E := -C (kap θ g zθ c c') *
      (C (ssPlace zθ c' - ssPlace zθ c) * (zθ c' - C (ssPlace zθ c))⁻¹)
    have hE : constantCoeff E = -kap θ g zθ c c' := by
      have hac : ssPlace zθ c' - ssPlace zθ c ≠ 0 := sub_ne_zero.2 fun h => hc (hinj h.symm)
      simp only [E, map_mul, map_neg, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv,
        map_sub]
      rw [cc_eq_place zθ c', mul_inv_cancel₀ hac, mul_one]
    have := coeff_dir E _ _ l hagree
    rw [hE] at this
    have hs : ∀ φ : PS, coeff (l + 1) (X * φ * PowerSeries.mk 1) = coeff l (φ * PowerSeries.mk 1) :=
      fun φ => by rw [mul_assoc, PowerSeries.coeff_succ_X_mul]
    rw [hs, hs, this]
    ring

/-- **Freeness** (`prop:LI`(a), `prop:depthdir`): every unit series `ψ` with `ψ(0) = 1` and every value
`γ ≠ 0` of `g_{c'}(0)` occur: the multiplier `g_{c'} = γ w'(a_{c'}) / (ψ ∏_{c≠c'} (z_{c'} - z_c))` has
`g_{c'}(0) = γ` and free series `ψ`. -/
theorem freeSer_free (g zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ)) (c' : Fin s)
    (γ : F) (hγ : γ ≠ 0) (ψ : PS) (hψ : constantCoeff ψ = 1) :
    constantCoeff (Function.update g c' (C (γ * placeDer zθ c') *
        (ψ * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹) c') = γ ∧
      freeSer (Function.update g c' (C (γ * placeDer zθ c') *
        (ψ * ∏ c ∈ univ.erase c', (zθ c' - zθ c))⁻¹)) zθ c' = ψ := by
  set Pz := ∏ c ∈ univ.erase c', (zθ c' - zθ c)
  have hP : constantCoeff Pz = placeDer zθ c' := constantCoeff_prodZ zθ c'
  have hwd := placeDer_ne zθ hinj c'
  have hψP : constantCoeff (ψ * Pz) ≠ 0 := by rw [map_mul, hψ, hP, one_mul]; exact hwd
  have h1 : constantCoeff (C (γ * placeDer zθ c') * (ψ * Pz)⁻¹) = γ := by
    rw [map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv, map_mul, hψ, hP, one_mul]
    field_simp
  refine ⟨by rw [Function.update_self]; exact h1, ?_⟩
  rw [freeSer, Function.update_self, h1]
  have hk : γ * placeDer zθ c' ≠ 0 := mul_ne_zero hγ hwd
  have hgP : constantCoeff (C (γ * placeDer zθ c') * (ψ * Pz)⁻¹ * Pz) ≠ 0 := by
    rw [map_mul, h1, hP]; exact mul_ne_zero hγ hwd
  rw [eq_comm, PowerSeries.eq_mul_inv_iff_mul_eq hgP]
  rw [show ψ * (C (γ * placeDer zθ c') * (ψ * Pz)⁻¹ * Pz) =
    C (γ * placeDer zθ c') * ((ψ * Pz) * (ψ * Pz)⁻¹) by ring, PowerSeries.mul_inv_cancel _ hψP, mul_one]

/-- **Row dependence** (`prop:depthdir`): if two multipliers of column `c'` have the same constant term
and their free series agree up to `x^n`, then row `n` of the generator matrix `C_{c'}` is the same. -/
theorem freeSer_row (g g' zθ : Fin s → PS) (hinj : Function.Injective (ssPlace zθ))
    (hg : ∀ c, constantCoeff (g c) ≠ 0) (hg' : ∀ c, constantCoeff (g' c) ≠ 0) (c' : Fin s)
    (h0 : constantCoeff (g c') = constantCoeff (g' c')) (n : ℕ)
    (hagree : ∀ m ≤ n, coeff m (freeSer g zθ c') = coeff m (freeSer g' zθ c')) (k : ℕ) :
    ssGen g zθ c' n k = ssGen g' zθ c' n k := by
  set Pz := ∏ c ∈ univ.erase c', (zθ c' - zθ c)
  set ψ := freeSer g zθ c'
  set ψ' := freeSer g' zθ c'
  have hP : constantCoeff Pz = placeDer zθ c' := constantCoeff_prodZ zθ c'
  have hA : constantCoeff (ψ * Pz) ≠ 0 := by
    rw [map_mul, freeSer_const g zθ hinj hg, hP, one_mul]; exact placeDer_ne zθ hinj c'
  have hA' : constantCoeff (ψ' * Pz) ≠ 0 := by
    rw [map_mul, freeSer_const g' zθ hinj hg', hP, one_mul]; exact placeDer_ne zθ hinj c'
  obtain ⟨r, hr⟩ : X ^ (n + 1) ∣ ψ' - ψ :=
    PowerSeries.X_pow_dvd_iff.2 fun m hm => by
      rw [map_sub, hagree m (by omega), sub_self]
  obtain ⟨γ, hγ⟩ : ∃ γ, constantCoeff (g c') = γ := ⟨_, rfl⟩
  have hgc := g_of_freeSer g zθ hinj hg c'
  rw [hγ] at hgc
  have hgc' := g_of_freeSer g' zθ hinj hg' c'
  rw [← h0, hγ] at hgc'
  have hdiff : g c' - g' c' = X ^ (n + 1) * (C (γ * placeDer zθ c') *
      (ψ * Pz)⁻¹ * (ψ' * Pz)⁻¹ * Pz * r) := by
    have e : (ψ * Pz)⁻¹ - (ψ' * Pz)⁻¹ = (ψ * Pz)⁻¹ * (ψ' * Pz)⁻¹ * ((ψ' - ψ) * Pz) := by
      linear_combination ((ψ' * Pz)⁻¹) * (PowerSeries.mul_inv_cancel _ hA) -
        ((ψ * Pz)⁻¹) * (PowerSeries.mul_inv_cancel _ hA')
    rw [hgc, hgc', ← mul_sub, e, hr]
    ring
  have : coeff n ((g c' - g' c') * zθ c' ^ k) = 0 := by
    rw [hdiff, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [sub_mul, map_sub, sub_eq_zero] at this
  exact this

/-- **`prop:LI`(d)** (Faure frame, `s = 2`, places `0, 1`, normalisation `ϖ_1 = dz/z`, `ϖ_0 = dz/(z-1)`):
with `γ = z_1²` (`= (1 - z_0)²`), `ψ_1 = g_1(0) k_1 / z_1`, `ψ_0 = g_0(0) k_0 / z_1` (`k_c = 1/(ρ g_c)`),
`κ_{0←1} = θ g_0(0)/g_1(0)`, `κ_{1←0} = θ g_1(0)/g_0(0)`: the one-digit law `D(l) = [x^l]𝒟/(1-x)` has
`𝒟[0][1] = x X_{0←1}`, `X_{0←1} = -κ_{0←1} ψ_1`, `𝒟[1][1] = O_1 = 1 - γ ψ_1 = 1 + γ X_{0←1}/κ_{0←1}`, and
symmetrically for column `0`; `κ_{0←1} κ_{1←0} = θ²`, `X_{0←1}(0) = -κ_{0←1}` (as `ψ_1(0) = 1`). -/
theorem LI_d (θ : F) (z0 z1 g0 g1 k0 k1 : PS) (hz0 : constantCoeff z0 = 0) (hsum : z0 + z1 = 1)
    (hprod : z0 * z1 = -(C θ * X)) (hg0 : constantCoeff g0 ≠ 0) (hg1 : constantCoeff g1 ≠ 0)
    (hk0 : k0 * ((z1 - z0) * g0) = 1) (hk1 : k1 * ((z1 - z0) * g1) = 1) :
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 1 =
        coeff l (X * (-C (θ * constantCoeff g0 / constantCoeff g1) *
          (C (constantCoeff g1) * k1 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 1 =
        coeff l ((1 - z1 ^ 2 * (C (constantCoeff g1) * k1 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 1 0 =
        coeff l (X * (-C (θ * constantCoeff g1 / constantCoeff g0) *
          (C (constantCoeff g0) * k0 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (∀ l, lawD ![g0, g1] ![z0, z1] (faureG z0 z1 k0 k1) 0 l 0 0 =
        coeff l ((1 - z1 ^ 2 * (C (constantCoeff g0) * k0 * z1⁻¹)) * PowerSeries.mk 1)) ∧
    (θ * constantCoeff g0 / constantCoeff g1) * (θ * constantCoeff g1 / constantCoeff g0) = θ ^ 2 ∧
    constantCoeff (C (constantCoeff g1) * k1 * z1⁻¹) = 1 ∧
    constantCoeff (C (constantCoeff g0) * k0 * z1⁻¹) = 1 ∧
    (1 - z1 ^ 2 * (C (constantCoeff g1) * k1 * z1⁻¹) =
      1 + C (θ * constantCoeff g0 / constantCoeff g1)⁻¹ * z1 ^ 2 *
        (-C (θ * constantCoeff g0 / constantCoeff g1) * (C (constantCoeff g1) * k1 * z1⁻¹)) ∨
      θ = 0) := by
  have hz1 : constantCoeff z1 = 1 := by
    have := congrArg constantCoeff hsum; rw [map_add, hz0, zero_add, map_one] at this; exact this
  have hz1u : z1 * z1⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hz1]; exact one_ne_zero)
  have hG := gform z0 z1 g0 g1 k0 k1 hz0 hsum
  have hk1c : constantCoeff k1 = (constantCoeff g1)⁻¹ := by
    have := congrArg constantCoeff hk1
    rw [map_mul, map_mul, map_sub, hz1, hz0, sub_zero, one_mul, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  have hk0c : constantCoeff k0 = (constantCoeff g0)⁻¹ := by
    have := congrArg constantCoeff hk0
    rw [map_mul, map_mul, map_sub, hz1, hz0, sub_zero, one_mul, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  refine ⟨fun l => ?_, fun l => ?_, fun l => ?_, fun l => ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hG l).2.1]
    refine congrArg (fun t => coeff l (t * PowerSeries.mk 1)) ?_
    have hc : C (θ * constantCoeff g0 / constantCoeff g1) * C (constantCoeff g1) =
        C θ * C (constantCoeff g0) := by
      rw [← map_mul, ← map_mul]; congr 1; field_simp
    linear_combination (k1 * z1⁻¹ * X) * hc + (C (constantCoeff g0) * k1 * z1⁻¹) * hprod -
      (C (constantCoeff g0) * z0 * k1) * hz1u
  · rw [(hG l).2.2.2]
    refine congrArg (fun t => coeff l (t * PowerSeries.mk 1)) ?_
    linear_combination (C (constantCoeff g1) * z1 * k1) * hz1u
  · rw [(hG l).2.2.1]
    refine congrArg (fun t => coeff l (t * PowerSeries.mk 1)) ?_
    have hc : C (θ * constantCoeff g1 / constantCoeff g0) * C (constantCoeff g0) =
        C θ * C (constantCoeff g1) := by
      rw [← map_mul, ← map_mul]; congr 1; field_simp
    linear_combination (k0 * z1⁻¹ * X) * hc + (C (constantCoeff g1) * k0 * z1⁻¹) * hprod -
      (C (constantCoeff g1) * z0 * k0) * hz1u
  · rw [(hG l).1]
    refine congrArg (fun t => coeff l (t * PowerSeries.mk 1)) ?_
    linear_combination (C (constantCoeff g0) * z1 * k0) * hz1u
  · field_simp
  · rw [map_mul, map_mul, PowerSeries.constantCoeff_C, hk1c, PowerSeries.constantCoeff_inv, hz1,
      inv_one, mul_one, mul_inv_cancel₀ hg1]
  · rw [map_mul, map_mul, PowerSeries.constantCoeff_C, hk0c, PowerSeries.constantCoeff_inv, hz1,
      inv_one, mul_one, mul_inv_cancel₀ hg0]
  · by_cases hθ : θ = 0
    · exact Or.inr hθ
    · left
      have hc : C (θ * constantCoeff g0 / constantCoeff g1)⁻¹ *
          C (θ * constantCoeff g0 / constantCoeff g1) = (1 : PS) := by
        rw [← map_mul, inv_mul_cancel₀ (div_ne_zero (mul_ne_zero hθ hg0) hg1), map_one]
      linear_combination (z1 ^ 2 * (C (constantCoeff g1) * k1 * z1⁻¹)) * hc

end GeoSeq
