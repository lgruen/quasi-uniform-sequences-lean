/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5P0

@[expose] public section

/-!
# GeoSeq stage V5: the staggered rule in dimension three (`thm:A3`, `tab:BSdata` column `s = 3`)

The design of `thm:A3`: Faure places `(0, 1, 2)`, staggered coordinate `c⋆ = 0`, order `(1, 2)`, `Q = (7, 3)`
(`a3Design`); window fractions `(27/1000, 1/200, 1/10)`, `u = 891/78 400 000`, rows sorted by `|n|` (`a3Data`).
* **`A3_design`**: `δ = 2` and `L = 21` are the least values of `lem:R`, `g = (1, -56, 6)`, `θ = 84T`, and
  `n = (2352, -126, 3/2, 7/2, -392, -9)` (exact, `decide`).
* **`A3_kappa`**: in `𝔽_p` (`p ≠ 2, 3, 7`, `T` odd, `p ∤ T`): `κ_{1←0} = 2352T`, `κ_{2←0} = -126T`,
  `κ_{0←1} = 3T/2`, `κ_{0←2} = 7T/2`, `κ_{1←2} = -392T`, `κ_{2←1} = -9T`.
* **`A3_threshold`**: `𝒫(p₀)` at `p₀ = 19 673 600` and `742 < M⋆^+(p₀) < 742.356` (one exact rational evaluation,
  kernel `decide`).
* **`A3`** (`thm:A3`): for every prime `p ≥ 1.97·10⁷`, the local roots exist, selection rules exist, and every
  selection rule gives a quasi-uniform digital `(0,3)`-sequence over `𝔽_p` with `c(P_{3K}) ≥ 1 - 742/p` for
  every `K ≥ 1`.
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

instance (D : StagDesign 3) : Decidable (sdOK D) := by unfold sdOK; infer_instance
instance (D : StagDesign 3) (δ : ℕ) : Decidable (sdDeltaOK D δ) := by unfold sdDeltaOK; infer_instance
instance (D : StagDesign 3) (δ L : ℕ) : Decidable (sdLOK D δ L) := by unfold sdLOK; infer_instance

/-- **`thm:A3`, the design** (`lem:R` data, `tab:BSdata`): `δ = 2` and `L = 21` are the least values with the
conditions of `lem:R`, `g = (1, -56, 6)`, `θ = 2^δ L T = 84T`, and the rationals
`n_{1←0} = 2352`, `n_{2←0} = -126`, `n_{0←1} = 3/2`, `n_{0←2} = 7/2`, `n_{1←2} = -392`, `n_{2←1} = -9`; the stored
row order of every column is the order of decreasing `|n|` (`def:BS` (S3), `app:LFdata`). -/
theorem A3_design :
    sdOK a3Design ∧ IsLeast {δ | sdDeltaOK a3Design δ} 2 ∧ IsLeast {L | sdLOK a3Design 2 L} 21 ∧
    (sdG a3Design 2 0 = 1 ∧ sdG a3Design 2 1 = -56 ∧ sdG a3Design 2 2 = 6) ∧ 2 ^ 2 * 21 = 84 ∧
    sdN a3Design 2 21 1 0 = 2352 ∧ sdN a3Design 2 21 2 0 = -126 ∧ sdN a3Design 2 21 0 1 = 3 / 2 ∧
    sdN a3Design 2 21 0 2 = 7 / 2 ∧ sdN a3Design 2 21 1 2 = -392 ∧ sdN a3Design 2 21 2 1 = -9 ∧
    (∀ c' : Fin 3, |sdN a3Design 2 21 (a3Rows c' 1) c'| ≤ |sdN a3Design 2 21 (a3Rows c' 0) c'|) := by
  refine ⟨by decide +kernel, ⟨by decide +kernel, fun δ hδ => ?_⟩, ⟨by decide +kernel, fun L hL => ?_⟩,
    by decide +kernel, by norm_num, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · by_contra h
    push_neg at h
    interval_cases δ <;> revert hδ <;> decide +kernel
  · by_contra h
    push_neg at h
    interval_cases L <;> revert hL <;> decide +kernel

/-- The data are valid (rows, nonzero crosses, odd half-cell numbers). -/
theorem a3Data_valid : a3Data.Valid := by decide +kernel

/-- **`thm:A3`, the threshold** (`tab:BSdata`): `𝒫(p₀)` holds at `p₀ = 19 673 600`, with
`742 < M⋆^+(p₀) < 742.356` (exact rational evaluation by the kernel). -/
theorem A3_threshold : StP a3Data (19673600 : ℚ) ∧
    742 < stMstP a3Data (19673600 : ℚ) ∧ stMstP a3Data (19673600 : ℚ) < 742356 / 1000 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The numbers of `a3Data`: `nI = n_{cc'}` (`c ≠ 0`) and `nI 0 j = L/Q_j`. -/
lemma a3Data_nI : a3Data.nI 1 0 = 2352 ∧ a3Data.nI 2 0 = -126 ∧ a3Data.nI 0 1 = 3 ∧ a3Data.nI 0 2 = 7 ∧
    a3Data.nI 1 2 = -392 ∧ a3Data.nI 2 1 = -9 := by
  decide +kernel

variable {p : ℕ} [Fact p.Prime]

lemma a3_hpa (hp2 : p ≠ 2) :
    ∀ b c : Fin 3, b ≠ c → ((frameA a3Design.fr b - frameA a3Design.fr c : ℤ) : ZMod p) ≠ 0 := by
  have h1 : ((1 : ℤ) : ZMod p) ≠ 0 := by simp
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this)
  intro b c hbc
  fin_cases b <;> fin_cases c <;> simp_all [frameA, a3Design] <;>
    first
    | exact h1
    | exact h2
    | (intro h; apply h1; linear_combination -h)
    | (intro h; apply h2; linear_combination -h)

lemma a3_hpQ (hp3 : p ≠ 3) (hp7 : p ≠ 7) :
    ∀ j, j ≠ a3Design.cs → ((a3Design.Q j).num : ZMod p) ≠ 0 ∧ ((a3Design.Q j).den : ZMod p) ≠ 0 := by
  have hq : ∀ q : ℕ, q.Prime → q ≠ p → ((q : ℤ) : ZMod p) ≠ 0 := by
    intro q hq hne h
    have : ((q : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp this).symm
  intro j hj
  fin_cases j
  · exact absurd rfl hj
  · refine ⟨?_, by simp [a3Design]⟩
    have := hq 7 (by norm_num) (Ne.symm hp7)
    simpa [a3Design] using this
  · refine ⟨?_, by simp [a3Design]⟩
    have := hq 3 (by norm_num) (Ne.symm hp3)
    simpa [a3Design] using this

lemma a3_hpL (hp3 : p ≠ 3) (hp7 : p ≠ 7) : ((21 : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hp := (Fact.out : p.Prime)
  have : p ∣ 3 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp this with h3 | h7
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7)

/-- **`thm:A3`, the crosses** (`lem:R` in `𝔽_p`): for every prime `p ≠ 2, 3, 7`, every odd `T` with `p ∤ T`, and
every choice of the local roots of the Faure frame `(0, 1, 2)`, with `θ = 84T` and `g = (1, -56, 6)`:
`κ_{1←0} = 2352T`, `κ_{2←0} = -126T`, `κ_{0←1} = 3T/2`, `κ_{0←2} = 7T/2`, `κ_{1←2} = -392T`, `κ_{2←1} = -9T`. -/
theorem A3_kappa (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp7 : p ≠ 7) (T : ℕ) (hT : T % 2 = 1) (hpT : (T : ZMod p) ≠ 0)
    (zθ : Fin 3 → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA a3Design.fr c : ℤ) : ZMod p)) :
    sdTheta p 2 21 T = ((84 * T : ℕ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 1 0 = ((2352 * T : ℤ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 2 0 = ((-126 * T : ℤ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 0 1 = ((3 * T : ℤ) : ZMod p) / 2 ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 0 2 = ((7 * T : ℤ) : ZMod p) / 2 ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 1 2 = ((-392 * T : ℤ) : ZMod p) ∧
    kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 2 1 = ((-9 * T : ℤ) : ZMod p) := by
  obtain ⟨hok, -, ⟨hL, -⟩, -⟩ := A3_design
  obtain ⟨-, -, hκ, hκh⟩ := lemR_Fp hp2 a3Design hok 2 21 T hL hT (a3_hpa hp2) (a3_hpQ hp3 hp7)
    (a3_hpL hp3 hp7) hpT zθ hplace
  obtain ⟨n10, n20, n01, n02, n12, n21⟩ := a3Data_nI
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_p (by have := (Fact.out : p.Prime).two_le; omega)
  have hn : ∀ c c' : Fin 3, c ≠ 0 → (sdN a3Design 2 21 c c').num = a3Data.nI c c' := fun c c' hc => by
    simp [a3Data, sdData, a3Design, hc]
  have hm : ∀ j : Fin 3, ((21 : ℕ) / a3Design.Q j : ℚ).num = a3Data.nI 0 j := fun j => by
    simp [a3Data, sdData, a3Design]
  have hk : ∀ c c' : Fin 3, c ≠ 0 → c ≠ c' → ∀ z : ℤ, a3Data.nI c c' = z →
      kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ c c' = ((z * T : ℤ) : ZMod p) := by
    intro c c' hc hcc z hz
    rw [hκ c c' hc hcc, hn c c' hc, hz]
    congr 1; ring
  have hh : ∀ j : Fin 3, j ≠ 0 → ∀ z : ℤ, a3Data.nI 0 j = z →
      kapL (sdTheta p 2 21 T) (sdLam a3Design p 2) zθ 0 j = ((z * T : ℤ) : ZMod p) / 2 := by
    intro j hj z hz
    have := (hκh j hj).1
    change 2 * kapL _ _ zθ 0 j = _ at this
    rw [hm j, hz] at this
    rw [eq_div_iff h2, mul_comm, this]
    congr 1; ring
  exact ⟨by unfold sdTheta; congr 1, hk 1 0 (by decide) (by decide) _ n10, hk 2 0 (by decide) (by decide) _ n20,
    hh 1 (by decide) _ n01, hh 2 (by decide) _ n02, hk 1 2 (by decide) (by decide) _ n12,
    hk 2 1 (by decide) (by decide) _ n21⟩

/-- **`thm:A3`** (the staggered rule in dimension three): for every prime `p ≥ 1.97·10⁷`, the local roots of the
Faure frame `(0, 1, 2)` with scale `θ = 84T` exist; for every choice of them, with `g = (1, -56, 6)`, the window
fractions `(27/1000, 1/200, 1/10)` and `u = 891/78 400 000` (`def:BS`), selection rules exist, and every
selection rule gives a digital `(0,3)`-sequence over `𝔽_p` with `c(P_{3K}) ≥ 1 - 742/p` for every `K ≥ 1`,
quasi-uniform (`h(P_{[N]}) ≤ (√3 p/(1 - 742/p)) δ(P_{[N]})` for every `N ≥ 2`, `lem:prefix`); the same for every
multiplier family with the constants `λ_c = g_c w'(a_c)` and all responses in the windows (= every selection
rule, `steer_every`). -/
theorem A3 (hp : 19700000 ≤ p) :
    (∃ zθ : Fin 3 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 3 a3Design.fr) = C (sdTheta p 2 21 (stT a3u p)) * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA a3Design.fr c : ℤ) : ZMod p)) ∧
    ∀ zθ : Fin 3 → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p 3 a3Design.fr) = C (sdTheta p 2 21 (stT a3u p)) * X) →
      (∀ c, constantCoeff (zθ c) = ((frameA a3Design.fr c : ℤ) : ZMod p)) →
      (∃ rule : Fin 3 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ (stWin a3Data p) rule) ∧
      (∀ rule : Fin 3 → ℕ → (ℕ → ZMod p) → ZMod p,
        IsSelRule (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ (stWin a3Data p) rule →
        IsSeq0 (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K
          (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))
          (1 - 742 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N
            (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))) ≤
            Real.sqrt 3 * p / (1 - 742 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N
                (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))))) ∧
      ∀ g : Fin 3 → PowerSeries (ZMod p), (∀ c, constantCoeff (g c) ≠ 0) → (∀ c, lam g zθ c = sdLam a3Design p 2 c) →
        RespInS (ssGen g zθ) (stWin a3Data p) →
        IsSeq0 (zcode p) (ssGen g zθ) ∧
        (∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 742 / p)) ∧
        ∀ N : ℕ, 2 ≤ N →
          Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen g zθ))) ≤
            Real.sqrt 3 * p / (1 - 742 / p) *
              (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (ssGen g zθ)))) := by
  obtain ⟨hok, -, ⟨hL, -⟩, -⟩ := A3_design
  obtain ⟨hP0q, -, hMq⟩ := A3_threshold
  have hP0 : StP a3Data ((19673600 : ℚ) : ℝ) := (StP_cast a3Data _).mp hP0q
  have hM0 : stMstP a3Data ((19673600 : ℚ) : ℝ) < 742356 / 1000 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hMq
    rw [stMstP_cast] at h
    have e : ((742356 / 1000 : ℚ) : ℝ) = 742356 / 1000 := by push_cast; ring
    rw [e] at h; exact h
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hp7 : p ≠ 7 := by omega
  have hpR : (19700000 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : ((19673600 : ℚ) : ℝ) ≤ p := by push_cast; linarith
  have hpa := a3_hpa (p := p) hp2
  -- `1 ≤ T < p`
  have hu : (a3u : ℝ) = 891 / 78400000 := by unfold a3u; push_cast; ring
  have hT := stT_facts a3u p (by rw [hu]; linarith)
  have hTp : stT a3u p < p := by
    have : (stT a3u p : ℝ) < p := by
      have := hT.2.2.1; rw [hu] at this; linarith
    exact_mod_cast this
  have hpT : (stT a3u p : ZMod p) ≠ 0 := natCast_ne_zero_of_lt (by have := hT.1; omega) hTp
  have hroots := frame_roots_exist p 3 a3Design.fr
    (fun c hc b hb => by
      have := hpa ⟨c, hc⟩ ⟨b, by omega⟩ (fun e => by have := congrArg Fin.val e; simp at this; omega)
      intro h0; apply this
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.dvd_of_emod_eq_zero h0)
    (sdTheta p 2 21 (stT a3u p))
  refine ⟨hroots, fun zθ hroot hplace => ?_⟩
  obtain ⟨hMst, hex, hall, hfam⟩ := P0_design a3Design (by norm_num) hok 2 21 hL a3Rows (27 / 1000) (1 / 200)
    (1 / 10) a3u a3Data_valid _ (by norm_num) hP0 p hpp hpa (a3_hpQ hp3 hp7) (a3_hpL hp3 hp7) hpT zθ hroot hplace
  -- `M⋆ ≤ 742`
  have hMst' : (stMv a3Data p a3Data.cs : ℝ) ≤ stMstP a3Data ((19673600 : ℚ) : ℝ) := hMst
  have hM742 : stMv a3Data p a3Data.cs ≤ 742 := by
    have : (stMv a3Data p a3Data.cs : ℝ) < 743 := by
      have := hMst'.trans_lt hM0; linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hpR0 : (0 : ℝ) < p := by linarith
  have hmono : 1 - 742 / (p : ℝ) ≤ 1 - (stMv a3Data p a3Data.cs : ℝ) / p := by
    have : (stMv a3Data p a3Data.cs : ℝ) ≤ 742 := by exact_mod_cast hM742
    have := div_le_div_of_nonneg_right this hpR0.le
    linarith
  have hpos : 0 < 1 - 742 / (p : ℝ) := by
    have : 742 / (p : ℝ) < 1 := by rw [div_lt_one hpR0]; linarith
    linarith
  refine ⟨hex, fun rule hrule => ?_, fun g hg hlg hW => ?_⟩
  · obtain ⟨hseq, hsep, -, -⟩ := hall rule hrule
    have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K
        (seqPoint (zcode p) (ssGen (ruleMult (sdTheta p 2 21 (stT a3u p)) (sdLam a3Design p 2) zθ rule) zθ))
        (1 - 742 / p) := fun K hK => sepAtLevel_le (hsep K hK) hmono
    exact ⟨hseq, hsep', fun N hN => by
      have := prefix_mesh (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep' N hN
      simpa using this⟩
  · obtain ⟨hseq, hsep, -, -⟩ := hfam g hg hlg hW
    have hsep' : ∀ K : ℕ, 1 ≤ K → SepAtLevel p 3 K (seqPoint (zcode p) (ssGen g zθ)) (1 - 742 / p) :=
      fun K hK => sepAtLevel_le (hsep K hK) hmono
    exact ⟨hseq, hsep', fun N hN => by
      have := prefix_mesh (zcode p) _ (by omega) (by norm_num) hseq _ hpos hsep' N hN
      simpa using this⟩

end GeoSeq
