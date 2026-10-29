/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_2Form

@[expose] public section

/-!
# GeoSeq stage V10-2 (part 3): `sec:count` for `def:selfsim` as written

The V9-8 results on self-similar scrambles (`onerel_poly`, `onerel_skel`, `residuerows_ss`, `onerel_stag`) were stated
for scrambles in residue form (`ssL a θ φ`). By `lem:resform`(b) (`selfsim_frDigit`) a self-similar scramble in the
sense of `def:selfsim` has the digits of `ssL a θ (locMul a θ g)`, so the relation spaces coincide (`relSpace_congr`),
and the results hold for `def:selfsim` as written, with `φ = locMul a θ g`:

* `onerel_poly_selfsim` (`prop:onerel`(i) polynomial part and (ii)), `onerel_skel_selfsim` (`prop:onerel`(iii),
  skeleton: the scramble IS the residue sequence `𝓡_{v/α}`), `onerel_stag_selfsim` (`prop:onerel`(iii), staggered: the
  scramble IS `𝓡^⋆`), `residuerows_selfsim` (`cor:residuerows`, self-similar clause).
* `prop:onerel`(i) (dimension), `prop:blockrel`, `lem:rigid`, `cor:residuerows` (first part), `cor:nodesign` and the
  last sentence of `prop:onerel`(iii) are proved in V9-8 for EVERY scramble of the frame (no bridge needed).
-/

namespace GeoSeq

open Finset Polynomial

variable {F : Type*} [Field F] {s : ℕ}

lemma relSpace_congr (a : Fin s → F) {L₁ L₂ : Fin s → ℕ → ℕ → F} (h : frDigit a L₁ = frDigit a L₂) (T m : ℕ) :
    relSpace a L₁ T m = relSpace a L₂ T m := by
  have hrf : relForm a L₁ = relForm a L₂ := by
    funext T f V; simp only [relForm, h]
  ext f
  show ((∀ c n, T < n → f c n = 0) ∧ ∀ V : F[X], V.natDegree < m → relForm a L₁ T f V = 0) ↔
    ((∀ c n, T < n → f c n = 0) ∧ ∀ V : F[X], V.natDegree < m → relForm a L₂ T f V = 0)
  rw [hrf]

section Bridge
variable (a : Fin s → F) (θ : F)

/-- The relation spaces of a self-similar scramble (`def:selfsim`) are those of its residue form. -/
theorem selfsim_relSpace (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (T m : ℕ) :
    relSpace a L T m = relSpace a (ssL a θ (locMul a θ g)) T m :=
  relSpace_congr a (selfsim_frDigit a θ ha hθ g L hL) T m

/-- **`prop:onerel`(i) (polynomial part) and (ii), for `def:selfsim` as written.** If a self-similar scramble with
scale `θ` and unit multipliers `g_c` satisfies the level-independent relation `∑_c ∑_{i ≤ J} ϑ_{c,i} y_{c,T-i} = 0` on
`P_{sT+i}` for every `T ≥ T₀ ≥ J`, then there is a polynomial `A ≠ 0`, `deg A < s - i`, with `φ_c ϑ_c(w/θ) = A` at
every place, `φ_c = θ^{-1} g_c(w/θ) w'` (`locMul`). -/
theorem onerel_poly_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (J T₀ i : ℕ) (hJ : J ≤ T₀)
    (ϑ : Fin s → ℕ → F) (hsupp : ∀ c i, J < i → ϑ c i = 0) (hϑ0 : ϑ ≠ 0)
    (hrel : ∀ T, T₀ ≤ T → liEmbed J T ϑ ∈ relSpace a L T (s * T + i)) :
    ∃ A : F[X], A ≠ 0 ∧ A.degree < ((s - i : ℕ) : WithBot ℕ) ∧
      ∀ c, locMul a θ g c * ((taylor (a c) (ϑpoly a θ J ϑ c) : F[X]) : PowerSeries F) =
        ((taylor (a c) A : F[X]) : PowerSeries F) :=
  onerel_poly a ha θ hθ (locMul a θ g) (selfsim_locMul_unit a θ ha hθ g L hL) J T₀ i hJ ϑ hsupp hϑ0
    (fun T hT => selfsim_relSpace a θ ha hθ g L hL T (s * T + i) ▸ hrel T hT)

/-- **`prop:onerel`(iii), skeleton part, for `def:selfsim` as written.** A self-similar scramble satisfying a
skeleton relation `∑_c v_c y_{c,T} = 0` on `P_{s(T+1)-1}` at every level `T ≥ T₀` (`v ≠ 0`) has every `v_c ≠ 0`,
constant local multipliers `φ_c = α/v_c`, and IS the residue sequence `𝓡_{v/α}` (same generator matrices). -/
theorem onerel_skel_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (T₀ : ℕ) (v : Fin s → F) (hv : v ≠ 0)
    (hrel : ∀ T, T₀ ≤ T → skelVec T v ∈ relSpace a L T (s * (T + 1) - 1)) :
    ∃ α : F, α ≠ 0 ∧ (∀ c, v c ≠ 0 ∧ locMul a θ g c = PowerSeries.C (α / v c)) ∧
      scrGen a L = resSeq a θ (fun c => v c / α) := by
  obtain ⟨α, hα, hc, heq⟩ := onerel_skel a ha θ hθ (locMul a θ g) (selfsim_locMul_unit a θ ha hθ g L hL) T₀ v hv
    (fun T hT => selfsim_relSpace a θ ha hθ g L hL T _ ▸ hrel T hT)
  exact ⟨α, hα, hc, by rw [selfsim_scrGen a θ ha hθ g L hL, heq, resSeq]⟩

/-- **`cor:residuerows`, self-similar clause, for `def:selfsim` as written.** A self-similar scramble whose rows are
residue rows up to scalars (`y_{c,n} = μ_{c,n} ŷ_{c,n}`) at every level `n ≥ n₀` IS the residue sequence `𝓡_v` with
`v_c = 1/φ_c(a_c)`. -/
theorem residuerows_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (n₀ : ℕ)
    (hrow : ∀ n, n₀ ≤ n → ∃ μ : Fin s → F, ∀ c V, frDigit a L c n V = μ c * resDig a c n V) :
    scrGen a L = resSeq a θ (fun c => (PowerSeries.constantCoeff (locMul a θ g c))⁻¹) := by
  have h := residuerows_ss a θ hθ ha (locMul a θ g) n₀
    (fun n hn => by rw [← selfsim_frDigit a θ ha hθ g L hL]; exact hrow n hn)
  rw [selfsim_scrGen a θ ha hθ g L hL, h, resSeq]

/-- **`prop:onerel`(iii), staggered part, for `def:selfsim` as written.** A self-similar scramble satisfying
`y_{c⋆,T} = ∑_{c ≠ c⋆} k_c y_{c,T-1}` on `P_{sT}` at every level `T ≥ T₀ ≥ 1` (`s ≥ 2`) has every `k_c ≠ 0` and IS the
staggered residue sequence `𝓡^⋆` with `μ⋆ = λθ` and weights `k` (`def:residuestar`). -/
theorem onerel_stag_selfsim (ha : Function.Injective a) (hθ : θ ≠ 0) (g : Fin s → PowerSeries F)
    (L : Fin s → ℕ → ℕ → F) (hL : IsSelfSim a θ g L) (hs : 2 ≤ s) (T₀ : ℕ) (hT₀ : 1 ≤ T₀) (cs : Fin s)
    (k : Fin s → F) (hrel : ∀ T, T₀ ≤ T → stagVec cs k T ∈ relSpace a L T (s * T)) :
    (∀ c, c ≠ cs → k c ≠ 0) ∧ ∃ lam : F, lam ≠ 0 ∧ scrGen a L = resStar a θ cs (lam * θ) k := by
  obtain ⟨hk, lam, hlam, hcs, hc⟩ := onerel_stag a ha θ hθ (locMul a θ g) (selfsim_locMul_unit a θ ha hθ g L hL)
    hs T₀ hT₀ cs k (fun T hT => selfsim_relSpace a θ ha hθ g L hL T _ ▸ hrel T hT)
  refine ⟨hk, lam, hlam, ?_⟩
  rw [selfsim_scrGen a θ ha hθ g L hL, onerel_stag_gen a ha θ (locMul a θ g) cs k lam hcs hc, resStar]

end Bridge

end GeoSeq
