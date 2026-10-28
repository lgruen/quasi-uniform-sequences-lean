/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2
public import GeoSeq.V4Defs

@[expose] public section

/-!
# GeoSeq stage V4: integer frames and the ordered-window theorem (`thm:LF`)

* Integer frames over `𝔽_p`: `framePoly_monic`, `framePoly_natDegree`, `frame_roots_exist` (the local roots
  exist when the places are distinct mod `p`), `frame_placeDer` (`w'(a_c) = ∏_{b≠c}(a_c - a_b)`).
* **`lex_sound`**: the argument of `thm:MR` for any ordered windows (`def:lex`) over an integer frame with
  integer upper crosses: if the crosses are the integers `κ_{c←j}`, `|κ_{c←j}| ≤ B_{c←j}` (condition (i)),
  every column covers in the second form of `lem:lexcover`, the integer conditions of `def:lex` hold and
  `Γ = lexCost < p`, then selection rules exist and every selection rule gives a quasi-uniform digital
  `(0,s)`-sequence with `c(P_{sK}) ≥ (p - Γ)/p` for every `K` (`prop:steer`, `lem:lex`, `rem:lexexact`,
  `lem:prefix`). Both parts of `thm:LF` are instances (`GeoSeq/V4OD.lean`, `GeoSeq/V4ED.lean`).
-/

namespace GeoSeq

open Finset PowerSeries
open scoped Polynomial

section Frame

variable {p : ℕ} [Fact p.Prime]

theorem framePoly_monic (p s : ℕ) (fr : List ℤ) : (framePoly p s fr).Monic :=
  Polynomial.monic_prod_X_sub_C _ _

theorem framePoly_natDegree (p s : ℕ) [Fact p.Prime] (fr : List ℤ) : (framePoly p s fr).natDegree = s := by
  unfold framePoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C, sum_const, card_range, smul_eq_mul, mul_one]

/-- Places distinct mod `p` (integer form) give distinct residues. -/
lemma frame_ne (s : ℕ) (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0)
    {b c : ℕ} (hb : b < s) (hc : c < s) (hbc : b ≠ c) :
    ((frameA fr b : ℤ) : ZMod p) ≠ ((frameA fr c : ℤ) : ZMod p) := by
  intro h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  rcases lt_or_gt_of_ne hbc with hlt | hlt
  · exact hd c hc b hlt (Int.emod_eq_zero_of_dvd h)
  · exact hd b hb c hlt (Int.emod_eq_zero_of_dvd (by
      have := dvd_neg.mpr h; rwa [neg_sub] at this))

/-- **The local roots of an integer frame exist** (places distinct mod `p`, any scale `θ`). -/
theorem frame_roots_exist (p s : ℕ) [Fact p.Prime] (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0) (θ : ZMod p) :
    ∃ zθ : Fin s → PowerSeries (ZMod p),
      (∀ c, Polynomial.aeval (zθ c) (framePoly p s fr) = C θ * X) ∧
      ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p) := by
  have h : ∀ c : Fin s, ∃ z : PowerSeries (ZMod p),
      Polynomial.aeval z (framePoly p s fr) = C θ * X ∧
        constantCoeff z = ((frameA fr c : ℤ) : ZMod p) := by
    intro c
    have hc : (c : ℕ) ∈ range s := mem_range.mpr c.isLt
    have hfac : framePoly p s fr = (Polynomial.X - Polynomial.C ((frameA fr c : ℤ) : ZMod p)) *
        ∏ b ∈ (range s).erase c, (Polynomial.X - Polynomial.C ((frameA fr b : ℤ) : ZMod p)) :=
      (Finset.mul_prod_erase _ (fun b : ℕ => Polynomial.X - Polynomial.C ((frameA fr b : ℤ) : ZMod p))
        hc).symm
    refine exists_localRoot _ (framePoly_monic p s fr) _ ?_ ?_ θ
    · rw [hfac]; simp
    · rw [hfac, Polynomial.derivative_mul]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
        sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]
      rw [Polynomial.eval_prod, prod_ne_zero_iff]
      intro b hb
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
      exact frame_ne s fr hd c.isLt (mem_range.mp (mem_of_mem_erase hb)) (ne_of_mem_erase hb).symm
  choose zθ hz using h
  exact ⟨zθ, fun c => (hz c).1, fun c => (hz c).2⟩

/-- `w'(a_c) = ∏_{b≠c} (a_c - a_b)` for an integer frame. -/
theorem frame_placeDer (s : ℕ) (fr : List ℤ) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p)) (c : Fin s) :
    placeDer zθ c = ((frameW s fr c : ℤ) : ZMod p) := by
  unfold placeDer ssPlace frameW
  simp only [hplace]
  push_cast
  set f : ℕ → ZMod p := fun b => if b = (c : ℕ) then 1 else
    ((frameA fr c : ℤ) : ZMod p) - ((frameA fr b : ℤ) : ZMod p)
  have h1 : ∏ b ∈ univ.erase c, (((frameA fr c : ℤ) : ZMod p) - ((frameA fr b : ℤ) : ZMod p)) =
      ∏ b : Fin s, f b := by
    rw [← Finset.mul_prod_erase univ (fun b : Fin s => f b) (mem_univ c)]
    simp only [f, if_pos rfl, one_mul]
    exact prod_congr rfl fun b hb => by
      rw [if_neg (fun e => (ne_of_mem_erase hb) (Fin.ext e))]
  have h2 : ∏ b ∈ (range s).erase c, (((frameA fr c : ℤ) : ZMod p) - ((frameA fr b : ℤ) : ZMod p)) =
      ∏ b ∈ range s, f b := by
    rw [← Finset.mul_prod_erase (range s) f (mem_range.mpr c.isLt)]
    simp only [f, if_pos rfl, one_mul]
    exact prod_congr rfl fun b hb => by rw [if_neg (ne_of_mem_erase hb)]
  rw [h1, h2, Fin.prod_univ_eq_prod_range f s]

theorem frameW_ne (s : ℕ) (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0) {c : ℕ} (hc : c < s) :
    ((frameW s fr c : ℤ) : ZMod p) ≠ 0 := by
  unfold frameW
  push_cast
  rw [prod_ne_zero_iff]
  intro b hb
  exact sub_ne_zero.mpr (frame_ne s fr hd hc (mem_range.mp (mem_of_mem_erase hb)) (ne_of_mem_erase hb).symm)

theorem frame_inj (s : ℕ) (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0) (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p)) :
    Function.Injective (ssPlace zθ) := by
  intro b c h
  by_contra hne
  simp only [ssPlace, hplace] at h
  exact frame_ne s fr hd b.isLt c.isLt (fun e => hne (Fin.ext e)) h

/-- An integer not divisible by `p` is a unit of `𝔽_p`. -/
lemma intCast_ne_zero_of_emod {x : ℤ} (h : x % (p : ℤ) ≠ 0) : (x : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  exact h (Int.emod_eq_zero_of_dvd h0)

end Frame

section Core

variable {s : ℕ}

/-- **The ordered-window theorem** (the argument of `thm:MR` for any ordered windows; `thm:LF`). Let
`p ≥ 5` be prime, `w = ∏_{c<s} (z - a_c)` an integer frame with places distinct mod `p`, local roots
`z_c(θx)`, a scale `θ ≠ 0` and constants `λ_c ≠ 0`. Suppose the upper crosses are integers,
`κ_{c←j} = κ̂_{c←j}` (`c < j`), with `|κ̂_{c←j}| ≤ B_{c←j}` (condition (i)), the integer conditions of
`def:lex` hold, `Γ = max_c (A_c + M_c + B_c) < p`, and every column covers in the second form of
`lem:lexcover` (for every `σ` some own value `o ∈ [-(A_j+M_j-1), -A_j]` has `σ_c + o κ̂_{c←j} ∈ [-B_{c←j},
B_{c←j}]` for every `c < j`). Then selection rules exist, and every selection rule defines a quasi-uniform
digital `(0,s)`-sequence over `𝔽_p` with `c(P_{sK}) ≥ (p - Γ)/p` for every `K ≥ 1`. -/
theorem lex_sound (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hs : 1 ≤ s) (fr : List ℤ)
    (hd : ∀ c < s, ∀ b < c, (frameA fr c - frameA fr b) % (p : ℤ) ≠ 0)
    (θ : ZMod p) (hθ : θ ≠ 0) (lamv : Fin s → ZMod p) (hlam : ∀ c, lamv c ≠ 0)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hroot : ∀ c, Polynomial.aeval (zθ c) (framePoly p s fr) = C θ * X)
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA fr c : ℤ) : ZMod p))
    (A M : Fin s → ℕ) (Bx : Fin s → Fin s → ℕ) (hlex : IsLexData p A M Bx)
    (hcost : lexCost A M Bx < p) (κ : Fin s → Fin s → ℤ)
    (hκ : ∀ c j, c < j → kapL θ lamv zθ c j = (κ c j : ZMod p))
    (hi : ∀ c j, c < j → (κ c j).natAbs ≤ Bx c j)
    (hcov : ∀ j : Fin s, ∀ σ : Fin s → ZMod p, ∃ o : ℤ, -((A j : ℤ) + M j - 1) ≤ o ∧ o ≤ -(A j : ℤ) ∧
      ∀ c, c < j → σ c + (o : ZMod p) * (κ c j : ZMod p) ∈ intWin p (-(Bx c j : ℤ)) (Bx c j)) :
    (∃ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (lexWin p A M Bx) rule) ∧
    ∀ rule : Fin s → ℕ → (ℕ → ZMod p) → ZMod p, IsSelRule θ lamv zθ (lexWin p A M Bx) rule →
      IsSeq0 (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ) ∧
      (∀ K : ℕ, 1 ≤ K → SepAtLevel p s K (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))
        (((p : ℝ) - lexCost A M Bx) / p)) ∧
      ∀ N : ℕ, 2 ≤ N →
        Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ))) ≤
          Real.sqrt s * p / (((p : ℝ) - lexCost A M Bx) / p) *
            (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2
              (prefixSet N (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule) zθ)))) := by
  have hs0 : 0 < s := hs
  have hi' : ∀ c c' : Fin s, c ≠ c' → -kapL θ lamv zθ c c' ∈ lexWin p A M Bx c c' := by
    intro c c' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [hκ c c' hlt, lexWin_up p _ _ _ hlt]
      have := hi c c' hlt
      refine ⟨-κ c c', by omega, by omega, by push_cast; rfl⟩
    · rw [lexWin_low p _ _ _ hlt]; trivial
  have hii : ∀ j : Fin s, LinesMeet (stAlpha θ lamv zθ j) (colWin (lexWin p A M Bx) j) := by
    intro j
    rw [lexcover_iff _ _ zθ _ j (fun c hc => lexWin_low p _ _ _ hc)]
    intro σ
    obtain ⟨o, ho1, ho2, hgood⟩ := hcov j σ
    refine ⟨(o : ZMod p), by rw [lexWin_own]; exact ⟨o, ho1, ho2, rfl⟩, fun c hc => ?_⟩
    rw [lexWin_up p _ _ _ hc, hκ c j hc]
    exact hgood c hc
  have hinj := frame_inj s fr hd zθ hplace
  obtain ⟨-, ⟨rule, hrule⟩, hall⟩ := steer p hp (framePoly p s fr) (framePoly_monic p s fr)
    (framePoly_natDegree p s fr) θ hθ zθ hroot hinj lamv hlam (lexWin p A M Bx) hi' hii
  refine ⟨⟨rule, hrule⟩, fun rule' hrule' => ?_⟩
  obtain ⟨-, hseq, -, hcert⟩ := hall rule' hrule'
  have hLB := (lex_eq p (by omega) hs0 A M Bx hlex).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hΓR : (lexCost A M Bx : ℝ) < p := by exact_mod_cast hcost
  have hpos : (0 : ℝ) < ((p : ℝ) - lexCost A M Bx) / p := div_pos (by linarith) hpR
  have hle1 : ((p : ℝ) - lexCost A M Bx) / p ≤ 1 := by
    rw [div_le_one hpR]; have : (0 : ℝ) ≤ lexCost A M Bx := Nat.cast_nonneg _; linarith
  have hsep : ∀ K : ℕ, 1 ≤ K → SepAtLevel p s K
      (seqPoint (zcode p) (ssGen (ruleMult θ lamv zθ rule') zθ)) (((p : ℝ) - lexCost A M Bx) / p) := by
    intro K hK
    have := (hcert _ hLB K hK).2
    rwa [min_eq_right hle1] at this
  exact ⟨hseq, hsep, fun N hN => prefix_mesh (zcode p) _ (by omega) hs0 hseq _ hpos hsep N hN⟩

end Core

end GeoSeq
