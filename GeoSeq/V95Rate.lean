/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Gen

@[expose] public section

/-!
# GeoSeq stage V9-5 (part 4): a faster rate when two places are one apart (`rem:faurerate`)

Prime `p`, the unscrambled frame with places `a_ĉ` and `a_{c₁} = a_ĉ + 1`, `Y = z - a_ĉ`, `δ_c = a_c - a_ĉ`,
`γ = ∏_{c ≠ ĉ} (-δ_c)`, `Q = p^w` (`w ≥ 1`):
`D = -γ^{-1} (Y - 1)^{Q-1} ∏_{c ≠ ĉ, c₁} (Y - δ_c)^Q` (`faureD`), `V_1 = -(Y + ⋯ + Y^{Q-1})` (`faureV1`).

* `prod_add_sub_prod_dvd`: `A ∣ ∏ (A + u_c) - ∏ u_c`.
* `faureD_taylor`: the first `Q` Taylor digits of `D` at `a_ĉ` are `1` (`(Y - 1) D ≡ -1 (mod Y^Q)`, Frobenius and
  `δ^Q = δ` in `𝔽_p`); `faureD_dvd_c1`, `faureD_dvd`: `(z - a_{c₁})^{Q-1} ∣ D`, `(z - a_c)^Q ∣ D` for the other `c`;
  `faureD_natDegree`: `deg D ≤ (s-1)Q - 1`.
* **`faurerate`** (`rem:faurerate`): the indices `ι(V_1)`, `ι(V_1 + D)` are distinct and `< N = p^{(s-1)Q}`, and the two
  points of the frame sequence are at distance `< √(p² + s + 2) p^{-Q} = √(p² + s + 2) N^{-1/(s-1)}`; hence
  `δ(P_{(s-1)Q}) < √(p² + s + 2) N^{-1/(s-1)}` (`faurerate_sep`).
-/

namespace GeoSeq

open Finset Polynomial

lemma prod_add_sub_prod_dvd {R ι : Type*} [CommRing R] [DecidableEq ι] (A : R) (u : ι → R) (T : Finset ι) :
    A ∣ ∏ c ∈ T, (A + u c) - ∏ c ∈ T, u c := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨k, hk⟩ := ih
    exact ⟨∏ c ∈ T, (A + u c) + u a * k, by linear_combination u a * hk⟩

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

section D
variable (a : Fin s → ZMod p) (ch c1 : Fin s)

lemma frob_sub (Y : (ZMod p)[X]) (δ : ZMod p) (w : ℕ) : (Y - C δ) ^ (p ^ w) = Y ^ (p ^ w) - C δ := by
  rw [sub_pow_char_pow, ← map_pow, ZMod.pow_card_pow]

/-- The first `Q = p^w` Taylor digits of `D` at `a_ĉ` are all `1`. -/
theorem faureD_taylor (ha : Function.Injective a) (hc1 : c1 ≠ ch) (h1 : a c1 = a ch + 1) (w : ℕ)
    (hw : 1 ≤ w) (n : ℕ) (hn : n < p ^ w) : (taylor (a ch) (faureD a ch c1 (p ^ w))).coeff n = 1 := by
  have hQ1 : 1 ≤ p ^ w := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  set Y : (ZMod p)[X] := X - C (a ch) with hY
  set γ : ZMod p := ∏ c ∈ univ.erase ch, -(a c - a ch) with hγ
  have hγ0 : γ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c hc =>
    neg_ne_zero.mpr (sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hc (ha h))
  have hc1m : c1 ∈ univ.erase ch := Finset.mem_erase.mpr ⟨hc1, mem_univ _⟩
  set P : (ZMod p)[X] := ∏ c ∈ (univ.erase ch).erase c1, (Y - C (a c - a ch)) ^ (p ^ w) with hP
  -- `(Y - 1) D = -γ^{-1} ∏_{c ≠ ĉ} (Y^Q - δ_c)`
  have hprod : ∏ c ∈ univ.erase ch, (Y ^ (p ^ w) + -C (a c - a ch)) = (Y - 1) ^ (p ^ w) * P := by
    rw [← Finset.mul_prod_erase _ _ hc1m]
    congr 1
    · rw [← sub_eq_add_neg, ← frob_sub Y (a c1 - a ch) w, h1, show a ch + 1 - a ch = 1 by ring, map_one]
    · exact Finset.prod_congr rfl fun c _ => by
        rw [frob_sub Y (a c - a ch) w]; exact (sub_eq_add_neg _ _).symm
  have hD : faureD a ch c1 (p ^ w) = -C γ⁻¹ * (Y - 1) ^ (p ^ w - 1) * P := rfl
  have hfac : (Y - 1) * faureD a ch c1 (p ^ w) =
      -C γ⁻¹ * ∏ c ∈ univ.erase ch, (Y ^ (p ^ w) + -C (a c - a ch)) := by
    have e1 : (Y - 1) * (Y - 1) ^ (p ^ w - 1) = (Y - 1) ^ (p ^ w) := by
      rw [← pow_succ']; congr 1; omega
    rw [hprod, hD]
    linear_combination (-C γ⁻¹ * P) * e1
  have hdiv1 : Y ^ (p ^ w) ∣ (Y - 1) * faureD a ch c1 (p ^ w) + 1 := by
    obtain ⟨k, hk⟩ := prod_add_sub_prod_dvd (Y ^ (p ^ w)) (fun c => -C (a c - a ch)) (univ.erase ch)
    have hu : ∏ c ∈ univ.erase ch, (-C (a c - a ch) : (ZMod p)[X]) = C γ := by
      rw [hγ, map_prod]; exact Finset.prod_congr rfl fun c _ => (map_neg C (a c - a ch)).symm
    rw [hu] at hk
    refine ⟨-C γ⁻¹ * k, ?_⟩
    rw [hfac]
    have hCC : (C γ⁻¹ : (ZMod p)[X]) * C γ = 1 := by rw [← map_mul, inv_mul_cancel₀ hγ0, map_one]
    linear_combination (-C γ⁻¹) * hk - hCC
  set S : (ZMod p)[X] := ∑ j ∈ range (p ^ w), Y ^ j with hS
  have hdiv2 : Y ^ (p ^ w) ∣ faureD a ch c1 (p ^ w) - S := by
    have hcop : IsCoprime (Y ^ (p ^ w)) (Y - 1) := IsCoprime.pow_left ⟨1, -1, by ring⟩
    refine hcop.dvd_of_dvd_mul_left ?_
    have hgeo : S * (Y - 1) = Y ^ (p ^ w) - 1 := geom_sum_mul Y (p ^ w)
    obtain ⟨k, hk⟩ := hdiv1
    exact ⟨k - 1, by linear_combination hk - hgeo⟩
  have hz := (X_sub_C_pow_dvd_iff (a ch) (p ^ w) _).mp hdiv2 n hn
  rw [map_sub, coeff_sub, sub_eq_zero] at hz
  rw [hz, hS, map_sum]
  simp only [hY, taylor_pow, taylor_X_sub_C]
  rw [coeff_sum_X_pow, if_pos hn]

theorem faureD_dvd_c1 (h1 : a c1 = a ch + 1) (Q : ℕ) : (X - C (a c1)) ^ (Q - 1) ∣ faureD a ch c1 Q := by
  rw [faureD, h1, map_add, map_one, show X - (C (a ch) + 1) = X - C (a ch) - 1 by ring]
  exact Dvd.dvd.mul_right (dvd_mul_left _ _) _

theorem faureD_dvd (c : Fin s) (hc : c ≠ ch) (hc1 : c ≠ c1) (Q : ℕ) :
    (X - C (a c)) ^ Q ∣ faureD a ch c1 Q := by
  rw [faureD]
  refine dvd_mul_of_dvd_right ?_ _
  have := Finset.dvd_prod_of_mem (fun c => (X - C (a ch) - C (a c - a ch)) ^ Q)
    (Finset.mem_erase.mpr ⟨hc1, Finset.mem_erase.mpr ⟨hc, mem_univ c⟩⟩)
  have e : (X - C (a ch) - C (a c - a ch) : (ZMod p)[X]) = X - C (a c) := by rw [map_sub]; ring
  beta_reduce at this
  rw [e] at this
  exact this

theorem faureD_natDegree (hc1 : c1 ≠ ch) (Q : ℕ) (hQ : 1 ≤ Q) :
    (faureD a ch c1 Q).natDegree ≤ (s - 1) * Q - 1 := by
  rw [faureD]
  have hcard : ((univ.erase ch).erase c1).card = s - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hc1, mem_univ _⟩),
      Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  have h1 : (-C (∏ c ∈ univ.erase ch, -(a c - a ch))⁻¹ * (X - C (a ch) - 1) ^ (Q - 1) : (ZMod p)[X]).natDegree
      ≤ Q - 1 := by
    refine natDegree_mul_le.trans ?_
    rw [← map_neg, natDegree_C, zero_add]
    refine natDegree_pow_le.trans ?_
    have : (X - C (a ch) - 1 : (ZMod p)[X]).natDegree ≤ 1 := by
      rw [show (X - C (a ch) - 1 : (ZMod p)[X]) = X - C (a ch + 1) by rw [map_add, map_one]; ring]
      exact natDegree_X_sub_C_le _
    nlinarith
  have h2 : (∏ c ∈ (univ.erase ch).erase c1, (X - C (a ch) - C (a c - a ch)) ^ Q : (ZMod p)[X]).natDegree
      ≤ (s - 2) * Q := by
    refine (natDegree_prod_le _ _).trans ?_
    rw [← hcard, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun c _ => natDegree_pow_le.trans ?_
    have : (X - C (a ch) - C (a c - a ch) : (ZMod p)[X]).natDegree ≤ 1 := by
      rw [show (X - C (a ch) - C (a c - a ch) : (ZMod p)[X]) = X - C (a c) by rw [map_sub]; ring]
      exact natDegree_X_sub_C_le _
    nlinarith
  have hs : 2 ≤ s := by
    have := Finset.card_le_univ (({ch, c1} : Finset (Fin s)))
    rw [Finset.card_pair hc1.symm, Fintype.card_fin] at this; omega
  have : (s - 1) * Q = (s - 2) * Q + Q := by
    rw [show s - 1 = (s - 2) + 1 by omega, add_mul, one_mul]
  exact natDegree_mul_le.trans ((add_le_add h1 h2).trans (by omega))

lemma faureV1_taylor (Q n : ℕ) :
    (taylor (a ch) (faureV1 a ch Q)).coeff n = if 1 ≤ n ∧ n < Q then -1 else 0 := by
  rw [faureV1, map_neg, map_sum, coeff_neg, finsetSum_coeff]
  simp only [taylor_pow, taylor_X_sub_C, coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_Ico]
  split_ifs <;> first | rfl | simp

lemma faureV1_natDegree (Q : ℕ) (hQ : 1 ≤ Q) : (faureV1 a ch Q).natDegree ≤ Q - 1 := by
  rw [faureV1, natDegree_neg]
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => natDegree_pow_le.trans ?_
  have := Finset.mem_Ico.mp hj
  rw [natDegree_X_sub_C]; omega

end D

/-- **`rem:faurerate`**: for the unscrambled frame with two places one apart (`a_{c₁} = a_ĉ + 1`) and `Q = p^w`
(`w ≥ 1`), the indices of `V_1` and `V_1 + D` are distinct and `< N = p^{(s-1)Q}`, and the two points are at
Euclidean distance `< √(p² + s + 2) p^{-Q} = √(p² + s + 2) N^{-1/(s-1)}`. -/
theorem faurerate (a : Fin s → ZMod p) (ha : Function.Injective a) (ch c1 : Fin s) (hc1 : c1 ≠ ch)
    (h1 : a c1 = a ch + 1) (w : ℕ) (hw : 1 ≤ w) :
    polyIdx p (faureV1 a ch (p ^ w)) < p ^ ((s - 1) * p ^ w) ∧
      polyIdx p (faureV1 a ch (p ^ w) + faureD a ch c1 (p ^ w)) < p ^ ((s - 1) * p ^ w) ∧
      polyIdx p (faureV1 a ch (p ^ w)) ≠ polyIdx p (faureV1 a ch (p ^ w) + faureD a ch c1 (p ^ w)) ∧
      euclDist (seqPoint (zcode p) (fun c n k => pas (a c) n k) (polyIdx p (faureV1 a ch (p ^ w))))
        (seqPoint (zcode p) (fun c n k => pas (a c) n k)
          (polyIdx p (faureV1 a ch (p ^ w) + faureD a ch c1 (p ^ w)))) <
        Real.sqrt ((p : ℝ) ^ 2 + s + 2) / (p : ℝ) ^ (p ^ w) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  set Q := p ^ w with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ hp.pos
  have hQ2 : 2 ≤ Q := le_trans hp2 (by rw [hQ]; exact Nat.le_self_pow (by omega) p)
  have hs : 2 ≤ s := by
    have := Finset.card_le_univ (({ch, c1} : Finset (Fin s)))
    rw [Finset.card_pair hc1.symm, Fintype.card_fin] at this; omega
  set V1 := faureV1 a ch Q with hV1
  set D := faureD a ch c1 Q with hD
  have hDt := faureD_taylor a ch c1 ha hc1 h1 w hw
  have hD0 : D ≠ 0 := fun h => by
    have := hDt 0 (by omega); rw [← hD, h] at this; simp at this
  have hdegD : D.natDegree ≤ (s - 1) * Q - 1 := faureD_natDegree a ch c1 hc1 Q hQ1
  have hdegV : V1.natDegree ≤ Q - 1 := faureV1_natDegree a ch Q hQ1
  have hm : (s - 1) * Q - 1 + 1 = (s - 1) * Q := by
    have : 1 ≤ (s - 1) * Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)); omega
  have hQle : Q ≤ (s - 1) * Q := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨polyIdx_lt _ (by omega), polyIdx_lt _ ((natDegree_add_le _ _).trans_lt (by omega)),
    fun h => hD0 ?_, ?_⟩
  · have := polyIdx_injective h; linear_combination -this
  -- the distance
  have hfr : seqPoint (zcode p) (fun c n k => pas (a c) n k) =
      linPt p (fun c V n => (taylor (a c) V).coeff n) := by
    rw [seqPoint_eq_linPt]; congr 1; funext c V n; exact pas_sum (a c) V n
  rw [hfr]
  set x := linPt p (fun c V n => (taylor (a c) V).coeff n) (polyIdx p V1)
  set y := linPt p (fun c V n => (taylor (a c) V).coeff n) (polyIdx p (V1 + D))
  have hxy : ∀ c, x c - y c = ∑' j, (((taylor (a c) V1).coeff j).val : ℝ) / (p : ℝ) ^ (j + 1) -
      ∑' j, (((taylor (a c) (V1 + D)).coeff j).val : ℝ) / (p : ℝ) ^ (j + 1) := fun c => by
    simp only [x, y, linPt_polyIdx]
  have hpQ : (0 : ℝ) < 1 / (p : ℝ) ^ Q := by positivity
  -- coordinate `ĉ`: a carry of length `Q`
  have hch : |x ch - y ch| < 2 / (p : ℝ) ^ Q := by
    rw [hxy, abs_sub_comm]
    have hv1 : ((1 : ZMod p)).val = 1 := ZMod.val_one p
    have hvm1 : ((-1 : ZMod p)).val = p - 1 := by erw [ZMod.neg_val]; rw [if_neg one_ne_zero, hv1]
    refine real_carry hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) (k := 0) (by omega)
      (fun j hj => absurd hj (by omega)) ?_ ?_ ?_
    · rw [map_add, coeff_add, faureV1_taylor, hDt 0 (by omega), if_neg (by omega), zero_add, hv1,
        ZMod.val_zero]
    · intro j hj1 hj2
      rw [map_add, coeff_add, faureV1_taylor, hDt j hj2, if_pos ⟨hj1, hj2⟩]
      exact ⟨hvm1, by rw [show (-1 : ZMod p) + 1 = 0 from neg_add_cancel 1, ZMod.val_zero]⟩
    · refine ⟨Q + (V1 + D).natDegree + 1, by omega, ?_⟩
      have hc0 : (taylor (a ch) (V1 + D)).coeff (Q + (V1 + D).natDegree + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [natDegree_taylor]; omega)
      rw [hc0, ZMod.val_zero]; omega
  -- coordinate `c₁`: `Q - 1` shared digits
  have hc1b : |x c1 - y c1| ≤ 1 / (p : ℝ) ^ (Q - 1) := by
    rw [hxy]
    refine real_prefix hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) (Q - 1) fun j hj => ?_
    rw [map_add, coeff_add, (X_sub_C_pow_dvd_iff (a c1) (Q - 1) D).mp (faureD_dvd_c1 a ch c1 h1 Q) j hj,
      add_zero]
  -- the other coordinates: `Q` shared digits
  have hoth : ∀ c, c ≠ ch → c ≠ c1 → |x c - y c| ≤ 1 / (p : ℝ) ^ Q := by
    intro c hc hc'
    rw [hxy]
    refine real_prefix hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) Q fun j hj => ?_
    rw [map_add, coeff_add, (X_sub_C_pow_dvd_iff (a c) Q D).mp (faureD_dvd a ch c1 c hc hc' Q) j hj,
      add_zero]
  have hpp : 1 / (p : ℝ) ^ (Q - 1) = p * (1 / (p : ℝ) ^ Q) := by
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [show Q = (Q - 1) + 1 by omega, pow_succ]; field_simp; simp
  rw [hpp] at hc1b
  have hsq_ch : (x ch - y ch) ^ 2 < 4 * (1 / (p : ℝ) ^ Q) ^ 2 := by
    have h2 : (2 : ℝ) / (p : ℝ) ^ Q = 2 * (1 / (p : ℝ) ^ Q) := by ring
    rw [h2] at hch
    have := sq_lt_sq' (abs_lt.mp hch).1 (abs_lt.mp hch).2
    nlinarith
  have hsq_c1 : (x c1 - y c1) ^ 2 ≤ (p : ℝ) ^ 2 * (1 / (p : ℝ) ^ Q) ^ 2 := by
    rw [← sq_abs, ← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hc1b 2
  have hsq_o : ∑ c ∈ (univ.erase ch).erase c1, (x c - y c) ^ 2 ≤ ((s : ℝ) - 2) * (1 / (p : ℝ) ^ Q) ^ 2 := by
    have h1' : ∀ c ∈ (univ.erase ch).erase c1, (x c - y c) ^ 2 ≤ (1 / (p : ℝ) ^ Q) ^ 2 := by
      intro c hc
      have hc' := Finset.ne_of_mem_erase hc
      have hc'' := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hoth c hc'' hc') 2
    refine (Finset.sum_le_card_nsmul _ _ _ h1').trans (le_of_eq ?_)
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hc1, mem_univ _⟩),
      Finset.card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsum : ∑ c, (x c - y c) ^ 2 < ((p : ℝ) ^ 2 + s + 2) * (1 / (p : ℝ) ^ Q) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ ch),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hc1, mem_univ c1⟩)]
    nlinarith
  unfold euclDist
  have hrhs : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ 2 + s + 2) / (p : ℝ) ^ Q := by positivity
  rw [Real.sqrt_lt' hrhs, div_pow, Real.sq_sqrt (by positivity)]
  calc ∑ c, (x c - y c) ^ 2 < ((p : ℝ) ^ 2 + s + 2) * (1 / (p : ℝ) ^ Q) ^ 2 := hsum
    _ = ((p : ℝ) ^ 2 + s + 2) / ((p : ℝ) ^ Q) ^ 2 := by ring

/-- **`rem:faurerate`** (separation): `δ(P_{(s-1)Q}) < √(p² + s + 2) N^{-1/(s-1)}` with `N = p^{(s-1)Q}`
(`N^{-1/(s-1)} = p^{-Q}`). -/
theorem faurerate_sep (a : Fin s → ZMod p) (ha : Function.Injective a) (ch c1 : Fin s) (hc1 : c1 ≠ ch)
    (h1 : a c1 = a ch + 1) (w : ℕ) (hw : 1 ≤ w) :
    sepDistIdx (seqPoint (zcode p) (fun c n k => pas (a c) n k)) (p ^ ((s - 1) * p ^ w)) <
      Real.sqrt ((p : ℝ) ^ 2 + s + 2) / (p : ℝ) ^ (p ^ w) := by
  obtain ⟨h1', h2', h3', h4'⟩ := faurerate a ha ch c1 hc1 h1 w hw
  exact (sepDistIdx_le_pair _ h1' h2' h3').trans_lt h4'

end GeoSeq
