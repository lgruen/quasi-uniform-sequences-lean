/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V98Cor

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 1): the density clauses of `cor:layer`(a) and `cor:density`

The range forms are `layer_a` and `density` (stage V9-8, `GeoSeq/V98Cor.lean`). Here the `limsup` clauses, by
covering the levels with admissible ranges, as the paper says. The covering is done for an arbitrary weight `g`
on the levels that obeys the count `∑_{T ∈ I} g T ≤ J + R + 1` on every admissible range `I = [K₀, K₀ + R]`
(`dens_ranges_bound`, `dens_ranges_eps`, `dens_ranges_limsup`), with ranges of ONE fixed length `R + 1` starting
at `T₁ = J + (s-1)R + s + 1` (every such range is admissible); letting `R → ∞` gives the density bound. The paper's
geometrically growing ranges give a better rate (`O(J log X)` instead of `O(√(JX))`), but are not needed for the
`limsup`.

* `dens_ranges_bound`: `∑_{T < X} g T ≤ B T₁ + (⌊X/(R+1)⌋ + 1)(J + R + 1)` for every `R` (`g ≤ B`).
* `dens_ranges_eps`, `dens_ranges_limsup`: `∑_{T ∈ [1,X]} g T ≤ (1 + ε) X` eventually; `limsup ≤ 1`.
* **`layer_a_density`** (`cor:layer`(a), density clause): `limsup |E ∩ [1,X]| / X ≤ 1/s`.
* **`density_limsup`** (`cor:density`, `limsup` clause): `limsup (|S ∩ [1,X]| + (s-1)|E ∩ [1,X]|)/X ≤ 1`;
  **`density_dens`** (`d_S + (s-1) d_E ≤ 1` when the densities exist); **`density_skel_range`** (a skeleton relation
  at every level of an admissible range leaves room for at most `J/(s-1)` design levels in it).
-/

namespace GeoSeq

open Finset Polynomial

section Dens

lemma sum_blocks (g : ℕ → ℕ) (T₁ R n : ℕ) :
    ∑ T ∈ range (T₁ + n * (R + 1)), g T =
      ∑ T ∈ range T₁, g T + ∑ k ∈ range n, ∑ i ∈ range (R + 1), g (T₁ + k * (R + 1) + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show T₁ + (n + 1) * (R + 1) = (T₁ + n * (R + 1)) + (R + 1) by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (n := n)]
    ring

/-- **Covering by admissible ranges of one length** (`cor:layer`(a), proof): if a weight `g ≤ B` on the levels obeys
the count `∑_{T ∈ [K₀, K₀+R]} g T ≤ J + R + 1` on every range admissible for depth `J` (`K₀ ≥ J`,
`K₀ > (s-1)R + s - 2`), then for every `R` and `X`, with `T₁ = J + (s-1)R + s + 1`,
`∑_{T < X} g T ≤ B T₁ + (⌊X/(R+1)⌋ + 1)(J + R + 1)`. -/
theorem dens_ranges_bound (g : ℕ → ℕ) (B s J : ℕ) (hB : ∀ T, g T ≤ B)
    (h : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1)
    (R X : ℕ) :
    ∑ T ∈ range X, g T ≤ B * (J + (s - 1) * R + s + 1) + (X / (R + 1) + 1) * (J + R + 1) := by
  set T₁ := J + (s - 1) * R + s + 1 with hT₁
  set n := X / (R + 1) + 1 with hn
  have hX : X ≤ T₁ + n * (R + 1) := by
    have h1 := Nat.lt_div_mul_add (a := X) (show 0 < R + 1 by omega)
    rw [hn, add_mul, one_mul]; omega
  calc ∑ T ∈ range X, g T ≤ ∑ T ∈ range (T₁ + n * (R + 1)), g T :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hX)
    _ = ∑ T ∈ range T₁, g T + ∑ k ∈ range n, ∑ i ∈ range (R + 1), g (T₁ + k * (R + 1) + i) := sum_blocks g T₁ R n
    _ ≤ T₁ * B + n * (J + R + 1) := by
        refine add_le_add ?_ ?_
        · have := Finset.sum_le_card_nsmul (range T₁) g B (fun T _ => hB T)
          simpa using this
        · have := Finset.sum_le_card_nsmul (range n)
            (fun k => ∑ i ∈ range (R + 1), g (T₁ + k * (R + 1) + i)) (J + R + 1) (fun k _ => by
            show ∑ i ∈ range (R + 1), g (T₁ + k * (R + 1) + i) ≤ J + R + 1
            rw [← sum_Icc_eq_range]
            refine h _ R (by omega) ?_
            have : (s - 1) * R + s - 2 < T₁ := by
              have e : T₁ = J + (s - 1) * R + s + 1 := hT₁
              have hs2 : s - 2 < s + 1 := by omega
              rw [e]; omega
            have : T₁ ≤ T₁ + k * (R + 1) := Nat.le_add_right _ _
            omega)
          simpa using this
    _ = B * (J + (s - 1) * R + s + 1) + (X / (R + 1) + 1) * (J + R + 1) := by rw [mul_comm]

/-- `cor:layer`(a), density form, for a general weight: `∑_{T ∈ [1,X]} g T ≤ (1 + ε) X` for all large `X`. -/
theorem dens_ranges_eps (g : ℕ → ℕ) (B s J : ℕ) (hB : ∀ T, g T ≤ B)
    (h : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) ≤ (1 + ε) * X := by
  intro ε hε
  obtain ⟨R, hR⟩ := exists_nat_gt (2 * J / ε)
  set C : ℕ := B * (J + (s - 1) * R + s + 1) + (J + R + 1) with hC
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((2 * C + 2 + ε) / ε)
  refine ⟨X₀, fun X hX => ?_⟩
  have h1 := dens_ranges_bound g B s J hB h R (X + 1)
  have hsub : ∑ T ∈ Icc 1 X, g T ≤ ∑ T ∈ range (X + 1), g T :=
    Finset.sum_le_sum_of_subset (fun T hT => by simp only [Finset.mem_Icc] at hT; simp; omega)
  set q := (X + 1) / (R + 1) with hq
  have hqR : q * (R + 1) ≤ X + 1 := Nat.div_mul_le_self _ _
  have h2 : ∑ T ∈ Icc 1 X, g T ≤ C + q * (R + 1) + q * J := by
    refine hsub.trans (h1.trans (le_of_eq ?_)); rw [hC]; ring
  have hJ : (J : ℝ) ≤ ε / 2 * (R + 1) := by
    have := (div_lt_iff₀ hε).mp hR
    nlinarith
  have hqR' : (q : ℝ) * (R + 1) ≤ X + 1 := by exact_mod_cast hqR
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hqJ : (q : ℝ) * J ≤ ε / 2 * (X + 1) := by
    calc (q : ℝ) * J ≤ q * (ε / 2 * (R + 1)) := mul_le_mul_of_nonneg_left hJ hq0
      _ = ε / 2 * (q * (R + 1)) := by ring
      _ ≤ ε / 2 * (X + 1) := mul_le_mul_of_nonneg_left hqR' (by positivity)
  have hX' : (X₀ : ℝ) ≤ X := by exact_mod_cast hX
  have hCX : (2 * C + 2 + ε : ℝ) < ε * X := by
    have := (div_lt_iff₀ hε).mp hX₀; nlinarith
  have h2' : ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) ≤ C + q * (R + 1) + q * J := by exact_mod_cast h2
  nlinarith

/-- `cor:layer`(a), `limsup` form, for a general weight: `limsup_{X → ∞} (∑_{T ∈ [1,X]} g T)/X ≤ 1`. -/
theorem dens_ranges_limsup (g : ℕ → ℕ) (B s J : ℕ) (hB : ∀ T, g T ≤ B)
    (h : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1) :
    Filter.limsup (fun X : ℕ => ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) / X) Filter.atTop ≤ 1 := by
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun X : ℕ => ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) / X) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop (fun X => by positivity)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨X₀, hX₀⟩ := dens_ranges_eps g B s J hB h ε hε
  refine Filter.limsup_le_of_le hcob (Filter.eventually_atTop.mpr ⟨X₀ + 1, fun X hX => ?_⟩)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [div_le_iff₀ hXpos]
  linarith [hX₀ X (by omega)]

end Dens

section Cor
variable {F : Type*} [Field F] {s : ℕ}

/-- **`cor:layer`(a), density clause**: the set `E` of levels `T` at which all `s` geometric digits of `P_{sT}` are
designed by exact relations of depth at most `J` has upper density at most `1/s`: `s |E ∩ [1,X]| ≤ (1 + ε) X` for all
large `X`, and `limsup_{X → ∞} |E ∩ [1,X]|/X ≤ 1/s` (any field, distinct places, any scramble, `s ≥ 1`). -/
theorem layer_a_density (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (J : ℕ) [DecidablePred (AllDesigned a L J)] :
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (s : ℝ) * ((Icc 1 X).filter (AllDesigned a L J)).card ≤ (1 + ε) * X) ∧
    Filter.limsup (fun X : ℕ => (((Icc 1 X).filter (AllDesigned a L J)).card : ℝ) / X) Filter.atTop ≤
      1 / s := by
  set g : ℕ → ℕ := fun T => if AllDesigned a L J T then s else 0 with hg
  have hsum : ∀ t : Finset ℕ, ∑ T ∈ t, g T = s * (t.filter (AllDesigned a L J)).card :=
    fun t => sum_ite_card _ t s
  have hB : ∀ T, g T ≤ s := fun T => by simp only [hg]; split_ifs <;> omega
  have hcount : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1 :=
    fun K₀ R hJ hadm => by rw [hsum]; exact layer_a a ha L hL K₀ R J hJ hadm
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  refine ⟨fun ε hε => ?_, ?_⟩
  · obtain ⟨X₀, hX₀⟩ := dens_ranges_eps g s s J hB hcount ε hε
    refine ⟨X₀, fun X hX => ?_⟩
    have := hX₀ X hX
    rw [hsum] at this
    exact_mod_cast this
  · have hl := dens_ranges_limsup g s s J hB hcount
    have he : (fun X : ℕ => ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) / X) =
        fun X : ℕ => (s : ℝ) * ((((Icc 1 X).filter (AllDesigned a L J)).card : ℝ) / X) := by
      funext X; rw [hsum]; push_cast; ring
    rw [he] at hl
    have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
        (fun X : ℕ => (((Icc 1 X).filter (AllDesigned a L J)).card : ℝ) / X) :=
      Filter.isCoboundedUnder_le_of_le Filter.atTop (fun X => by positivity)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨X₀, hX₀⟩ := dens_ranges_eps g s s J hB hcount (s * ε) (by positivity)
    refine Filter.limsup_le_of_le hcob (Filter.eventually_atTop.mpr ⟨X₀ + 1, fun X hX => ?_⟩)
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have h1 := hX₀ X (by omega)
    rw [hsum] at h1
    push_cast at h1
    rw [div_le_iff₀ hXpos, div_add' _ _ _ hs0.ne', div_mul_eq_mul_div, le_div_iff₀ hs0]
    nlinarith

/-- The weight of `cor:density`: `[T ∈ S] + (s-1)[T ∈ E]`, and its sums. -/
lemma density_sum (a : Fin s → F) (L : Fin s → ℕ → ℕ → F) (J : ℕ) [DecidablePred (AllDesigned a L J)]
    [DecidablePred (HasSkel a L)] (t : Finset ℕ) :
    ∑ T ∈ t, ((if HasSkel a L T then 1 else 0) + (s - 1) * (if AllDesigned a L J T then 1 else 0)) =
      (t.filter (HasSkel a L)).card + (s - 1) * (t.filter (AllDesigned a L J)).card := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite_card, sum_ite_card, one_mul, one_mul]

/-- **`cor:density`, `limsup` clause**: with `E` (all geometric digits of `P_{sT}` designed with depth `≤ J`) and `S`
(a skeleton relation on `P_{s(T+1)-1}`), `|S ∩ [1,X]| + (s-1)|E ∩ [1,X]| ≤ (1 + ε) X` for all large `X`, and
`limsup_{X → ∞} (|S ∩ [1,X]| + (s-1)|E ∩ [1,X]|)/X ≤ 1` (any field, distinct places, any scramble, `s ≥ 1`). -/
theorem density_limsup (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (J : ℕ) [DecidablePred (AllDesigned a L J)] [DecidablePred (HasSkel a L)] :
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Icc 1 X).filter (HasSkel a L)).card : ℝ) + (s - 1 : ℕ) * ((Icc 1 X).filter (AllDesigned a L J)).card ≤
        (1 + ε) * X) ∧
    Filter.limsup (fun X : ℕ => ((((Icc 1 X).filter (HasSkel a L)).card : ℝ) +
      (s - 1 : ℕ) * ((Icc 1 X).filter (AllDesigned a L J)).card) / X) Filter.atTop ≤ 1 := by
  set g : ℕ → ℕ := fun T => (if HasSkel a L T then 1 else 0) + (s - 1) * (if AllDesigned a L J T then 1 else 0)
    with hg
  have hB : ∀ T, g T ≤ s := fun T => by
    simp only [hg]; split_ifs <;> omega
  have hcount : ∀ K₀ R, J ≤ K₀ → (s - 1) * R + s - 2 < K₀ → ∑ T ∈ Icc K₀ (K₀ + R), g T ≤ J + R + 1 :=
    fun K₀ R hJ hadm => by rw [density_sum]; exact density a ha L hL K₀ R J hJ hadm
  have he : ∀ X, ((∑ T ∈ Icc 1 X, g T : ℕ) : ℝ) = (((Icc 1 X).filter (HasSkel a L)).card : ℝ) +
      (s - 1 : ℕ) * ((Icc 1 X).filter (AllDesigned a L J)).card := fun X => by
    rw [density_sum]; push_cast; ring
  refine ⟨fun ε hε => ?_, ?_⟩
  · obtain ⟨X₀, hX₀⟩ := dens_ranges_eps g s s J hB hcount ε hε
    exact ⟨X₀, fun X hX => by rw [← he]; exact hX₀ X hX⟩
  · have hl := dens_ranges_limsup g s s J hB hcount
    simp_rw [he] at hl
    exact hl

/-- **`cor:density`, "in particular"**: if the densities `d_S` of `S` and `d_E` of `E` exist (as limits of
`|S ∩ [1,X]|/X` and `|E ∩ [1,X]|/X`), then `d_S + (s-1) d_E ≤ 1`. -/
theorem density_dens (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F) (hL : IsScramble L)
    (hs : 1 ≤ s) (J : ℕ) [DecidablePred (AllDesigned a L J)] [DecidablePred (HasSkel a L)] (dS dE : ℝ)
    (hS : Filter.Tendsto (fun X : ℕ => (((Icc 1 X).filter (HasSkel a L)).card : ℝ) / X) Filter.atTop (nhds dS))
    (hE : Filter.Tendsto (fun X : ℕ => (((Icc 1 X).filter (AllDesigned a L J)).card : ℝ) / X) Filter.atTop
      (nhds dE)) :
    dS + (s - 1 : ℕ) * dE ≤ 1 := by
  obtain ⟨h1, -⟩ := density_limsup a ha L hL hs J
  have hT := hS.add (hE.const_mul ((s - 1 : ℕ) : ℝ))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨X₀, hX₀⟩ := h1 ε hε
  refine le_of_tendsto hT (Filter.eventually_atTop.mpr ⟨X₀ + 1, fun X hX => ?_⟩)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have := hX₀ X (by omega)
  show _ / (X : ℝ) + _ * (_ / (X : ℝ)) ≤ 1 + ε
  rw [mul_div_assoc', ← add_div, div_le_iff₀ hXpos]
  linarith

/-- **`cor:density`, last clause**: a skeleton relation at every level of an admissible range `I = [K₀, K₀ + R]`
leaves room for at most `J/(s-1)` design levels in it: `(s-1) |E ∩ I| ≤ J`. -/
theorem density_skel_range (a : Fin s → F) (ha : Function.Injective a) (L : Fin s → ℕ → ℕ → F)
    (hL : IsScramble L) (K₀ R J : ℕ) (hJ : J ≤ K₀) (hadm : (s - 1) * R + s - 2 < K₀)
    [DecidablePred (AllDesigned a L J)] [DecidablePred (HasSkel a L)]
    (hS : ∀ T, K₀ ≤ T → T ≤ K₀ + R → HasSkel a L T) :
    (s - 1) * ((Icc K₀ (K₀ + R)).filter (AllDesigned a L J)).card ≤ J := by
  have h := density a ha L hL K₀ R J hJ hadm
  have hc : ((Icc K₀ (K₀ + R)).filter (HasSkel a L)).card = R + 1 := by
    rw [Finset.filter_true_of_mem (fun T hT => by simp only [Finset.mem_Icc] at hT; exact hS T hT.1 hT.2),
      Nat.card_Icc]; omega
  omega

end Cor

end GeoSeq
