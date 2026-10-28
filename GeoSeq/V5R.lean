/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V5Defs
public import GeoSeq.V4Core

@[expose] public section

/-!
# GeoSeq stage V5: the half from a power of two (`lem:R`)

Staggered designs over integer frames (`StagDesign`):
* **`lemR_rat`**: with `g_{c⋆} = 1`, `g_j = 2^{1+δ}Q_j/Δ_{⋆j}` and `θ = 2^δ L T`, every cross is
  `κ_{c←c'} = T n_{cc'}` (exact rational identity, any `δ`, `L`, `T`).
* **`lemR_int`**, **`lemR_half`**: under the definition of `L` (`sdLOK`), `n_{cc'} ∈ ℤ` for `c ≠ c⋆`, and
  `L/Q_j` is an odd integer, so `n_{⋆←j} = L/(2Q_j) ∈ ½ + ℤ`.
* **`lemR_delta`**, **`lemR_L`**: the least `δ` exists, and for any `δ` with the conditions of `sdDeltaOK` the least
  `L` exists ("it exists by the choice of `δ`": the `2`-adic valuations make every denominator of `n°` odd).
* **`lemR_Fp`**: for every prime `p` dividing none of the `a_c - a_{c'}`, the numerators and denominators of the
  `Q_j`, `L`, `T` and `2`, the same identities hold in `𝔽_p`: every `κ_{c←c'}` (`c ≠ c⋆`) is the integer
  `T n_{cc'}`, and `κ_{⋆←j} = ½ + (TL/Q_j - 1)/2`.
-/

namespace GeoSeq

open Finset PowerSeries

section R

variable {s : ℕ}

lemma sd_frameW_ne (D : StagDesign s) (hD : sdOK D) (c : Fin s) : frameW s D.fr c ≠ 0 := by
  unfold frameW
  rw [prod_ne_zero_iff]
  intro b hb
  have hb' : b < s := mem_range.mp (mem_of_mem_erase hb)
  have hbc : b ≠ (c : ℕ) := ne_of_mem_erase hb
  refine sub_ne_zero.mpr fun h => hD.1 ⟨b, hb'⟩ c (fun e => hbc (congrArg Fin.val e)) ?_
  exact h.symm

lemma sdDelta_ne (D : StagDesign s) (hD : sdOK D) {c c' : Fin s} (h : c ≠ c') : sdDelta D c c' ≠ 0 :=
  mul_ne_zero (sd_frameW_ne D hD c') (sub_ne_zero.mpr (hD.1 c' c (Ne.symm h)))

lemma sdDelta_ne_q (D : StagDesign s) (hD : sdOK D) {c c' : Fin s} (h : c ≠ c') :
    ((sdDelta D c c' : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (sdDelta_ne D hD h)

lemma sdQ_ne (D : StagDesign s) (hD : sdOK D) {j : Fin s} (hj : j ≠ D.cs) : D.Q j ≠ 0 :=
  (hD.2 j hj).1.ne'

/-- **`lem:R`, the identities** (exact, over `ℚ`): with `g_{c⋆} = 1`, `g_j = 2^{1+δ}Q_j/Δ_{⋆j}` and
`θ = 2^δ L T`, every depth-zero cross `κ_{c←c'} = θ g_c/(g_{c'}Δ_{cc'})` equals `T n_{cc'}`; in particular, in
the row of `c⋆`, `θ/(g_j Δ_{⋆j}) = TL/(2Q_j)` (the frame factor cancels completely). -/
theorem lemR_rat (D : StagDesign s) (hD : sdOK D) (δ L T : ℕ) {c c' : Fin s} (h : c ≠ c') :
    sdKap D δ ((2 : ℚ) ^ δ * L * T) c c' = T * sdN D δ L c c' := by
  unfold sdKap sdG sdN
  by_cases hc : c = D.cs
  · have hc' : c' ≠ D.cs := fun h' => h (hc.trans h'.symm)
    rw [hc] at h ⊢
    simp only [if_true, if_neg hc']
    have hQ := sdQ_ne D hD hc'
    have h1 := sdDelta_ne_q D hD h
    field_simp
    try ring
  · by_cases hc' : c' = D.cs
    · rw [hc'] at h ⊢
      simp only [if_true, if_neg hc]
      have hQ := sdQ_ne D hD hc
      have h1 := sdDelta_ne_q D hD h
      have h2 := sdDelta_ne_q D hD (Ne.symm h)
      field_simp
      try ring
    · simp only [if_neg hc, if_neg hc']
      have hQ := sdQ_ne D hD hc
      have hQ' := sdQ_ne D hD hc'
      have h1 := sdDelta_ne_q D hD h
      have h2 := sdDelta_ne_q D hD (Ne.symm hc)
      have h3 := sdDelta_ne_q D hD (Ne.symm hc')
      field_simp
      try ring

lemma sdN_lin (D : StagDesign s) (δ L : ℕ) (c c' : Fin s) : sdN D δ L c c' = L * sdN D δ 1 c c' := by
  unfold sdN
  split_ifs <;> push_cast <;> ring

/-- **`lem:R`**: `n_{cc'} ∈ ℤ` for `c ≠ c⋆` (by the definition of `L`). -/
theorem lemR_int (D : StagDesign s) (δ L : ℕ) (hL : sdLOK D δ L) {c c' : Fin s} (hc : c ≠ D.cs)
    (h : c ≠ c') : (sdN D δ L c c').den = 1 := by
  rw [sdN_lin]; exact hL.2.2 c c' hc h

/-- **`lem:R`**: `L/Q_j` is an odd integer, and `n_{⋆←j} = L/(2Q_j) = ½ + (L/Q_j - 1)/2 ∈ ½ + ℤ`. -/
theorem lemR_half (D : StagDesign s) (hD : sdOK D) (δ L : ℕ) (hL : sdLOK D δ L) {j : Fin s}
    (hj : j ≠ D.cs) :
    ((L : ℚ) / D.Q j).den = 1 ∧ ((L : ℚ) / D.Q j).num % 2 = 1 ∧
      sdN D δ L D.cs j = 1 / 2 + (((((L : ℚ) / D.Q j).num - 1) / 2 : ℤ) : ℚ) := by
  have hx1 := hL.2.1 j hj
  obtain ⟨hQpos, hnum, hden⟩ := hD.2 j hj
  set x := (L : ℚ) / D.Q j with hxdef
  have hxz : (x.num : ℚ) = x := Rat.coe_int_num_of_den_eq_one hx1
  have hQ : D.Q j = ((D.Q j).num : ℚ) / ((D.Q j).den : ℚ) := (Rat.num_div_den _).symm
  have hden0 : ((D.Q j).den : ℚ) ≠ 0 := by positivity
  have hnum0 : ((D.Q j).num : ℚ) ≠ 0 := by
    have := Rat.num_pos.mpr hQpos; exact_mod_cast this.ne'
  -- `x.num * qn = L * qd`
  have hrel : x.num * (D.Q j).num = (L : ℤ) * (D.Q j).den := by
    have hQ0 : D.Q j ≠ 0 := hQpos.ne'
    have hxQ : x * D.Q j = L := by rw [hxdef]; field_simp
    have hQd : D.Q j * (D.Q j).den = (D.Q j).num := Rat.mul_den_eq_num _
    have : (x.num : ℚ) * (D.Q j).num = (L : ℚ) * (D.Q j).den := by
      rw [hxz, ← hQd, ← mul_assoc, hxQ]
    exact_mod_cast this
  have hodd : x.num % 2 = 1 := by
    have hLo : Odd (L : ℤ) := by rw [Int.odd_iff]; have := hL.1; omega
    have hdo : Odd ((D.Q j).den : ℤ) := by rw [Int.odd_iff]; have := hden; omega
    have : Odd (x.num * (D.Q j).num) := by rw [hrel]; exact hLo.mul hdo
    exact Int.odd_iff.mp (Int.odd_mul.mp this).1
  refine ⟨hx1, hodd, ?_⟩
  have hsdN : sdN D δ L D.cs j = x / 2 := by
    unfold sdN; rw [if_pos rfl, hxdef]; field_simp
  rw [hsdN]
  conv_lhs => rw [← hxz]
  have hk : x.num = 2 * ((x.num - 1) / 2) + 1 := by omega
  conv_lhs => rw [hk]
  push_cast; ring

/-! ### Existence of the least `δ` and `L` -/

lemma den_odd_of_v2 (x : ℚ) (h : 0 ≤ padicValRat 2 x) : x.den % 2 = 1 := by
  by_contra hd
  have h2 : 2 ∣ x.den := by omega
  have hnum : ¬ 2 ∣ x.num.natAbs := by
    intro h2n
    have := Nat.dvd_gcd h2n h2
    rw [x.reduced] at this
    omega
  have hv1 : padicValInt 2 x.num = 0 := by
    unfold padicValInt; exact padicValNat.eq_zero_of_not_dvd hnum
  have hv2 : 1 ≤ padicValNat 2 x.den := one_le_padicValNat_of_dvd x.den_nz h2
  rw [padicValRat_def, hv1] at h
  omega

lemma v2_odd_rat (q : ℚ) (hn : q.num % 2 = 1) (hd : q.den % 2 = 1) : padicValRat 2 q = 0 := by
  rw [padicValRat_def]
  have h1 : padicValInt 2 q.num = 0 := by
    unfold padicValInt
    refine padicValNat.eq_zero_of_not_dvd fun h => ?_
    have : (2 : ℤ) ∣ q.num := Int.natAbs_dvd_natAbs.mp (by simpa using h)
    omega
  have h2 : padicValNat 2 q.den = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  rw [h1, h2]; simp

lemma v2_int (z : ℤ) : padicValRat 2 (z : ℚ) = padicValInt 2 z := padicValRat.of_int

/-- The `2`-adic content of the choice of `δ`: every `n°_{cc'}` (`c ≠ c⋆`) has an odd denominator. -/
lemma sdN1_den_odd (D : StagDesign s) (hD : sdOK D) (δ : ℕ) (hδ : sdDeltaOK D δ) {c c' : Fin s}
    (hc : c ≠ D.cs) (h : c ≠ c') : (sdN D δ 1 c c').den % 2 = 1 := by
  refine den_odd_of_v2 _ ?_
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hQ := sdQ_ne D hD hc
  have hvQ := v2_odd_rat (D.Q c) (hD.2 c hc).2.1 (hD.2 c hc).2.2
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num); simpa using this
  unfold sdN
  rw [if_neg hc]
  by_cases hc' : c' = D.cs
  · rw [if_pos hc']
    rw [hc'] at h
    have hΔ : ((sdDelta D c D.cs : ℚ) * sdDelta D D.cs c) ≠ 0 :=
      mul_ne_zero (sdDelta_ne_q D hD h) (sdDelta_ne_q D hD (Ne.symm h))
    have hcast : ((sdDelta D c D.cs : ℚ) * sdDelta D D.cs c) = ((sdDelta D c D.cs * sdDelta D D.cs c : ℤ) : ℚ) := by
      push_cast; ring
    rw [Nat.cast_one, mul_one, padicValRat.div (mul_ne_zero (pow_ne_zero _ h2) hQ) hΔ,
      padicValRat.mul (pow_ne_zero _ h2) hQ, padicValRat.pow, h22, hvQ,
      hcast, v2_int]
    have := hδ.1 c hc
    push_cast
    omega
  · rw [if_neg hc']
    have hQ' := sdQ_ne D hD hc'
    have hvQ' := v2_odd_rat (D.Q c') (hD.2 c' hc').2.1 (hD.2 c' hc').2.2
    have hA := sdDelta_ne_q D hD (Ne.symm hc')
    have hB := sdDelta_ne_q D hD (Ne.symm hc)
    have hC := sdDelta_ne_q D hD h
    rw [Nat.cast_one, mul_one, padicValRat.mul (mul_ne_zero (pow_ne_zero _ h2) (div_ne_zero hQ hQ'))
        (div_ne_zero hA (mul_ne_zero hB hC)),
      padicValRat.mul (pow_ne_zero _ h2) (div_ne_zero hQ hQ'), padicValRat.pow,
      h22, padicValRat.div hQ hQ', hvQ, hvQ',
      padicValRat.div hA (mul_ne_zero hB hC), padicValRat.mul hB hC, v2_int, v2_int, v2_int]
    have := hδ.2 c c' hc hc' h
    push_cast
    omega

lemma prod_mod_two_eq_one {ι : Type*} (S : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ S, f i % 2 = 1) :
    (∏ i ∈ S, f i) % 2 = 1 := by
  rw [Finset.prod_nat_mod, Finset.prod_congr rfl hf, Finset.prod_const_one]
  simp

/-- **`lem:R`, existence of `L`**: for every `δ` with the conditions of `sdDeltaOK` there is a least `L` with the
conditions of `sdLOK` (odd, every `L/Q_j` and every `L n°_{cc'}`, `c ≠ c⋆`, an integer). -/
theorem lemR_L (D : StagDesign s) (hD : sdOK D) (δ : ℕ) (hδ : sdDeltaOK D δ) :
    ∃ L, IsLeast {L | sdLOK D δ L} L := by
  classical
  set P1 := ∏ j ∈ univ.erase D.cs, (D.Q j).num.natAbs
  set P2 := ∏ c ∈ univ.erase D.cs, ∏ c' ∈ univ.erase c, (sdN D δ 1 c c').den
  have hex : ∃ L, sdLOK D δ L := by
    refine ⟨P1 * P2, ?_, fun j hj => ?_, fun c c' hc h => ?_⟩
    · rw [Nat.mul_mod]
      have h1 : P1 % 2 = 1 := prod_mod_two_eq_one _ _ fun j hj => by
        have := (hD.2 j (ne_of_mem_erase hj)).2.1
        have h' : Odd (D.Q j).num.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr this)
        exact Nat.odd_iff.mp h'
      have h2 : P2 % 2 = 1 := prod_mod_two_eq_one _ _ fun c hc =>
        prod_mod_two_eq_one _ _ fun c' hc' =>
          sdN1_den_odd D hD δ hδ (ne_of_mem_erase hc) (ne_of_mem_erase hc').symm
      rw [h1, h2]
    · obtain ⟨m, hm⟩ : (D.Q j).num.natAbs ∣ P1 * P2 :=
        Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (mem_erase.mpr ⟨hj, mem_univ _⟩)) _
      have hpos := Rat.num_pos.mpr (hD.2 j hj).1
      have hnat : ((D.Q j).num.natAbs : ℤ) = (D.Q j).num := Int.natAbs_of_nonneg hpos.le
      have hQ : D.Q j = ((D.Q j).num : ℚ) / ((D.Q j).den : ℚ) := (Rat.num_div_den _).symm
      have hnum0 : ((D.Q j).num : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      have hQ0 : D.Q j ≠ 0 := (hD.2 j hj).1.ne'
      have hQd : D.Q j * (D.Q j).den = (D.Q j).num := Rat.mul_den_eq_num _
      have hnatQ : (((D.Q j).num.natAbs : ℕ) : ℚ) = ((D.Q j).num : ℚ) := by
        calc (((D.Q j).num.natAbs : ℕ) : ℚ) = ((((D.Q j).num.natAbs : ℕ) : ℤ) : ℚ) := (Int.cast_natCast _).symm
          _ = ((D.Q j).num : ℚ) := by rw [hnat]
      have : ((P1 * P2 : ℕ) : ℚ) / D.Q j = (((m : ℤ) * (D.Q j).den : ℤ) : ℚ) := by
        rw [hm]
        push_cast
        rw [hnatQ, ← hQd]
        field_simp
      rw [this, Rat.den_intCast]
    · have hmem : c ∈ univ.erase D.cs := mem_erase.mpr ⟨hc, mem_univ _⟩
      have hmem' : c' ∈ univ.erase c := mem_erase.mpr ⟨Ne.symm h, mem_univ _⟩
      have hd1 : (sdN D δ 1 c c').den ∣ ∏ c'' ∈ univ.erase c, (sdN D δ 1 c c'').den :=
        Finset.dvd_prod_of_mem (fun c'' => (sdN D δ 1 c c'').den) hmem'
      have hd2 : (∏ c'' ∈ univ.erase c, (sdN D δ 1 c c'').den) ∣ P2 :=
        Finset.dvd_prod_of_mem (fun c => ∏ c'' ∈ univ.erase c, (sdN D δ 1 c c'').den) hmem
      obtain ⟨m, hm⟩ : (sdN D δ 1 c c').den ∣ P1 * P2 := (hd1.trans hd2).mul_left P1
      have : ((P1 * P2 : ℕ) : ℚ) * sdN D δ 1 c c' = (((m : ℤ) * (sdN D δ 1 c c').num : ℤ) : ℚ) := by
        rw [hm]
        push_cast
        rw [mul_comm ((sdN D δ 1 c c').den : ℚ) (m : ℚ), mul_assoc, mul_comm ((sdN D δ 1 c c').den : ℚ),
          Rat.mul_den_eq_num]
      rw [this, Rat.den_intCast]
  exact ⟨Nat.find hex, Nat.find_spec hex, fun L hL => Nat.find_min' hex hL⟩

/-- **`lem:R`, existence of `δ`**: a least `δ ≥ 0` with the conditions of `sdDeltaOK` exists. -/
theorem lemR_delta (D : StagDesign s) : ∃ δ, IsLeast {δ | sdDeltaOK D δ} δ := by
  classical
  set S := ∑ j, padicValInt 2 (sdDelta D j D.cs * sdDelta D D.cs j) + ∑ j, padicValInt 2 (sdDelta D D.cs j) +
    ∑ j, ∑ j', padicValInt 2 (sdDelta D j j')
  have hex : ∃ δ, sdDeltaOK D δ := by
    refine ⟨S, fun j _ => ?_, fun j j' _ _ _ => ?_⟩
    · have := Finset.single_le_sum (f := fun j => padicValInt 2 (sdDelta D j D.cs * sdDelta D D.cs j))
        (fun _ _ => Nat.zero_le _) (mem_univ j)
      omega
    · have h1 := Finset.single_le_sum (f := fun j => padicValInt 2 (sdDelta D D.cs j))
        (fun _ _ => Nat.zero_le _) (mem_univ j)
      have h2 := Finset.single_le_sum (f := fun j' => padicValInt 2 (sdDelta D j j'))
        (fun _ _ => Nat.zero_le _) (mem_univ j')
      have h3 := Finset.single_le_sum (f := fun j => ∑ j', padicValInt 2 (sdDelta D j j'))
        (fun _ _ => Nat.zero_le _) (mem_univ j)
      omega
  exact ⟨Nat.find hex, Nat.find_spec hex, fun δ hδ => Nat.find_min' hex hδ⟩

/-! ### The identities in `𝔽_p` -/

/-- Numerator of `g_c`: `1` for `c⋆`, `2^{1+δ} num(Q_c)` otherwise. -/
def sdGX (D : StagDesign s) (δ : ℕ) (c : Fin s) : ℤ := if c = D.cs then 1 else 2 ^ (1 + δ) * (D.Q c).num

/-- Denominator of `g_c`: `1` for `c⋆`, `den(Q_c) Δ_{⋆c}` otherwise. -/
def sdGY (D : StagDesign s) (δ : ℕ) (c : Fin s) : ℤ := if c = D.cs then 1 else (D.Q c).den * sdDelta D D.cs c

lemma sdG_eq (D : StagDesign s) (hD : sdOK D) (δ : ℕ) (c : Fin s) :
    sdG D δ c = (sdGX D δ c : ℚ) / (sdGY D δ c : ℚ) := by
  unfold sdG sdGX sdGY
  split_ifs with hc
  · simp
  · have hQ : D.Q c = ((D.Q c).num : ℚ) / ((D.Q c).den : ℚ) := (Rat.num_div_den _).symm
    have hden0 : ((D.Q c).den : ℚ) ≠ 0 := by positivity
    have hΔ := sdDelta_ne_q D hD (Ne.symm hc)
    conv_lhs => rw [hQ]
    push_cast
    field_simp

lemma sdGY_ne_q (D : StagDesign s) (hD : sdOK D) (δ : ℕ) (c : Fin s) : (sdGY D δ c : ℚ) ≠ 0 := by
  unfold sdGY
  split_ifs with hc
  · simp
  · push_cast
    exact mul_ne_zero (by positivity) (sdDelta_ne_q D hD (Ne.symm hc))

lemma sdGX_ne_q (D : StagDesign s) (hD : sdOK D) (δ : ℕ) (c : Fin s) : (sdGX D δ c : ℚ) ≠ 0 := by
  unfold sdGX
  split_ifs with hc
  · simp
  · push_cast
    exact mul_ne_zero (by positivity) (by exact_mod_cast (Rat.num_pos.mpr (hD.2 c hc).1).ne')

lemma quot_id {F : Type*} [Field F] (θ X Y X' Y' Δ R : F) (hY : Y ≠ 0) (hY' : Y' ≠ 0) (hX' : X' ≠ 0)
    (hΔ : Δ ≠ 0) (h : θ * X * Y' = R * X' * Y * Δ) : θ * (X / Y) / ((X' / Y') * Δ) = R := by
  rw [div_eq_iff (mul_ne_zero (div_ne_zero hX' hY') hΔ)]
  field_simp
  linear_combination h

lemma quot_cross {F : Type*} [Field F] (θ X Y X' Y' Δ R : F) (hY : Y ≠ 0) (hY' : Y' ≠ 0) (hX' : X' ≠ 0)
    (hΔ : Δ ≠ 0) (h : θ * (X / Y) / ((X' / Y') * Δ) = R) : θ * X * Y' = R * X' * Y * Δ := by
  rw [div_eq_iff (mul_ne_zero (div_ne_zero hX' hY') hΔ)] at h
  field_simp at h
  linear_combination h

/-- The integer identity behind `κ_{c←c'} = T n_{cc'}` (from `lemR_rat`), for any rational value `R` of
`T n_{cc'}` that is an integer. -/
lemma sd_cross_int (D : StagDesign s) (hD : sdOK D) (δ L T : ℕ) {c c' : Fin s} (h : c ≠ c') (R : ℤ)
    (hR : (T : ℚ) * sdN D δ L c c' = R) :
    (2 ^ δ * L * T : ℤ) * sdGX D δ c * sdGY D δ c' = R * sdGX D δ c' * sdGY D δ c * sdDelta D c c' := by
  have h1 := lemR_rat D hD δ L T h
  rw [hR] at h1
  unfold sdKap at h1
  rw [sdG_eq D hD δ c, sdG_eq D hD δ c'] at h1
  have := quot_cross _ _ _ _ _ _ _ (sdGY_ne_q D hD δ c) (sdGY_ne_q D hD δ c') (sdGX_ne_q D hD δ c')
    (sdDelta_ne_q D hD h) h1
  exact_mod_cast this

lemma half_id {F : Type*} [Field F] (θ W W' X Y a a' R : F) (hW : W ≠ 0) (hW' : W' ≠ 0) (hX : X ≠ 0)
    (hY : Y ≠ 0) (hd : a' - a ≠ 0) (h : θ * 2 * Y = R * X * (W' * (a' - a))) :
    2 * (θ * (((1 : ℤ) : F) / ((1 : ℤ) : F) * W) / (X / Y * W' * W * (a' - a))) = R := by
  have hYY : Y⁻¹ * Y = 1 := inv_mul_cancel₀ hY
  have hden : X / Y * W' * W * (a' - a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (div_ne_zero hX hY) hW') hW) hd
  rw [Int.cast_one, div_one, one_mul, mul_div_assoc', div_eq_iff hden, div_eq_mul_inv]
  linear_combination (W * Y⁻¹) * h - (2 * θ * W) * hYY

variable {p : ℕ} [Fact p.Prime]

lemma halfZ_two' (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : 2 * halfZ p = p + 1 := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  unfold halfZ; omega

lemma ratCast_div_int (X Y : ℤ) (hY : (Y : ZMod p) ≠ 0) :
    (((X : ℚ) / (Y : ℚ) : ℚ) : ZMod p) = (X : ZMod p) / (Y : ZMod p) := by
  rw [Rat.cast_div_of_ne_zero (by simp) (by simpa using hY)]
  simp

lemma frameW_ne_p (D : StagDesign s) (hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0)
    (c : Fin s) : ((frameW s D.fr c : ℤ) : ZMod p) ≠ 0 := by
  unfold frameW
  push_cast
  rw [prod_ne_zero_iff]
  intro b hb
  have hb' : b < s := mem_range.mp (mem_of_mem_erase hb)
  have hbc : b ≠ (c : ℕ) := ne_of_mem_erase hb
  have := hpa c ⟨b, hb'⟩ (fun e => hbc (congrArg Fin.val e).symm)
  push_cast at this
  exact this

lemma sdDelta_ne_p (D : StagDesign s)
    (hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0)
    {c c' : Fin s} (h : c ≠ c') : ((sdDelta D c c' : ℤ) : ZMod p) ≠ 0 := by
  unfold sdDelta
  push_cast
  have := hpa c' c (Ne.symm h)
  push_cast at this
  exact mul_ne_zero (by have := frameW_ne_p D hpa c'; push_cast at this; exact this) this

/-- **`lem:R` in `𝔽_p`**: let `p` be a prime dividing none of the `a_c - a_{c'}`, the numerators and denominators
of the `Q_j`, `L`, `T` and `2`, and `T` odd. With `θ = 2^δ L T` and the constants `λ_c = g_c w'(a_c)` (the
rationals `g_c` reduced mod `p`), for every choice of the local roots: `θ ≠ 0`, `λ_c ≠ 0`, every
`κ_{c←c'}` with `c ≠ c⋆` is the integer `T n_{cc'}`, and each half-cell offset is
`κ_{⋆←j} = ½ + (TL/Q_j - 1)/2` (with `2κ_{⋆←j} = TL/Q_j`). -/
theorem lemR_Fp (hp2 : p ≠ 2) (D : StagDesign s) (hD : sdOK D) (δ L T : ℕ) (hL : sdLOK D δ L)
    (hT : T % 2 = 1)
    (hpa : ∀ b c : Fin s, b ≠ c → ((frameA D.fr b - frameA D.fr c : ℤ) : ZMod p) ≠ 0)
    (hpQ : ∀ j, j ≠ D.cs → ((D.Q j).num : ZMod p) ≠ 0 ∧ ((D.Q j).den : ZMod p) ≠ 0)
    (hpL : (L : ZMod p) ≠ 0) (hpT : (T : ZMod p) ≠ 0)
    (zθ : Fin s → PowerSeries (ZMod p))
    (hplace : ∀ c, constantCoeff (zθ c) = ((frameA D.fr c : ℤ) : ZMod p)) :
    sdTheta p δ L T ≠ 0 ∧ (∀ c, sdLam D p δ c ≠ 0) ∧
    (∀ c c', c ≠ D.cs → c ≠ c' →
      kapL (sdTheta p δ L T) (sdLam D p δ) zθ c c' = (((T : ℤ) * (sdN D δ L c c').num : ℤ) : ZMod p)) ∧
    ∀ j, j ≠ D.cs →
      2 * kapL (sdTheta p δ L T) (sdLam D p δ) zθ D.cs j = (((T : ℤ) * ((L : ℚ) / D.Q j).num : ℤ) : ZMod p) ∧
      kapL (sdTheta p δ L T) (sdLam D p δ) zθ D.cs j =
        ((halfZ p : ℤ) : ZMod p) + ((((T : ℤ) * ((L : ℚ) / D.Q j).num - 1) / 2 : ℤ) : ZMod p) := by
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp this
    exact hp2 this
  have hθ : sdTheta p δ L T ≠ 0 := by
    unfold sdTheta; push_cast
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2p) hpL) hpT
  -- the `g_c` mod `p`
  have hGY : ∀ c, ((sdGY D δ c : ℤ) : ZMod p) ≠ 0 := by
    intro c; unfold sdGY
    split_ifs with hc
    · simp
    · push_cast
      exact mul_ne_zero (hpQ c hc).2 (sdDelta_ne_p D hpa (Ne.symm hc))
  have hGX : ∀ c, ((sdGX D δ c : ℤ) : ZMod p) ≠ 0 := by
    intro c; unfold sdGX
    split_ifs with hc
    · simp
    · push_cast
      exact mul_ne_zero (pow_ne_zero _ h2p) (hpQ c hc).1
  have hG : ∀ c, ((sdG D δ c : ℚ) : ZMod p) = ((sdGX D δ c : ℤ) : ZMod p) / ((sdGY D δ c : ℤ) : ZMod p) := by
    intro c; rw [sdG_eq D hD δ c, ratCast_div_int _ _ (hGY c)]
  have hlam : ∀ c, sdLam D p δ c ≠ 0 := by
    intro c; unfold sdLam; rw [hG c]
    exact mul_ne_zero (div_ne_zero (hGX c) (hGY c)) (frameW_ne_p D hpa c)
  -- `κ` in `𝔽_p` from the integer identity
  have hkap : ∀ c c', c ≠ c' → ∀ R : ℤ, (T : ℚ) * sdN D δ L c c' = R →
      kapL (sdTheta p δ L T) (sdLam D p δ) zθ c c' = (R : ZMod p) := by
    intro c c' h R hR
    have hZ := sd_cross_int D hD δ L T h R hR
    have hZp := congrArg (fun z : ℤ => (z : ZMod p)) hZ
    push_cast at hZp
    unfold kapL sdLam
    rw [frame_placeDer s D.fr zθ hplace c]
    simp only [ssPlace, hplace]
    have hW := frameW_ne_p D hpa c
    rw [show ((sdG D δ c : ℚ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p) =
        ((sdG D δ c : ℚ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p) from rfl]
    rw [show (sdTheta p δ L T) * (((sdG D δ c : ℚ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p)) /
        (((sdG D δ c' : ℚ) : ZMod p) * ((frameW s D.fr c' : ℤ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p) *
          (((frameA D.fr c' : ℤ) : ZMod p) - ((frameA D.fr c : ℤ) : ZMod p))) =
        (sdTheta p δ L T) * ((sdG D δ c : ℚ) : ZMod p) /
          (((sdG D δ c' : ℚ) : ZMod p) * ((sdDelta D c c' : ℤ) : ZMod p)) by
      unfold sdDelta; push_cast
      rw [show ((sdG D δ c' : ℚ) : ZMod p) * ((frameW s D.fr c' : ℤ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p) *
          (((frameA D.fr c' : ℤ) : ZMod p) - ((frameA D.fr c : ℤ) : ZMod p)) =
          (((sdG D δ c' : ℚ) : ZMod p) * (((frameW s D.fr c' : ℤ) : ZMod p) *
            (((frameA D.fr c' : ℤ) : ZMod p) - ((frameA D.fr c : ℤ) : ZMod p)))) *
              ((frameW s D.fr c : ℤ) : ZMod p) by ring,
        show (sdTheta p δ L T) * (((sdG D δ c : ℚ) : ZMod p) * ((frameW s D.fr c : ℤ) : ZMod p)) =
          ((sdTheta p δ L T) * ((sdG D δ c : ℚ) : ZMod p)) * ((frameW s D.fr c : ℤ) : ZMod p) by ring,
        mul_div_mul_right _ _ hW]]
    rw [hG c, hG c']
    refine quot_id _ _ _ _ _ _ _ (hGY c) (hGY c') (hGX c') (sdDelta_ne_p D hpa h) ?_
    unfold sdTheta; push_cast; push_cast at hZp
    linear_combination hZp
  refine ⟨hθ, hlam, fun c c' hc h => hkap c c' h _ ?_, fun j hj => ?_⟩
  · push_cast; rw [Rat.coe_int_num_of_den_eq_one (lemR_int D δ L hL hc h)]
  · obtain ⟨hx1, hodd, hN⟩ := lemR_half D hD δ L hL hj
    set m := ((L : ℚ) / D.Q j).num
    have hxz : (m : ℚ) = (L : ℚ) / D.Q j := Rat.coe_int_num_of_den_eq_one hx1
    -- `2 κ_{⋆←j} = T m`
    have hcs : D.cs ≠ j := Ne.symm hj
    have h2k : 2 * kapL (sdTheta p δ L T) (sdLam D p δ) zθ D.cs j = (((T : ℤ) * m : ℤ) : ZMod p) := by
      -- apply `hkap` to `2θ`-free form: use the identity with `R = T m` for `2κ`
      have hR : (T : ℚ) * sdN D δ L D.cs j * 2 = (((T : ℤ) * m : ℤ) : ℚ) := by
        unfold sdN; rw [if_pos rfl]; push_cast; rw [hxz]
        have hQ := sdQ_ne D hD hj
        field_simp
      have hZ := lemR_rat D hD δ L T hcs
      unfold sdKap at hZ
      rw [sdG_eq D hD δ D.cs, sdG_eq D hD δ j] at hZ
      have hZ2 : (2 ^ δ * L * T : ℚ) * (sdGX D δ D.cs / sdGY D δ D.cs) /
          ((sdGX D δ j / sdGY D δ j) * sdDelta D D.cs j) * 2 = (((T : ℤ) * m : ℤ) : ℚ) := by
        rw [hZ, hR]
      have hX0 : sdGX D δ D.cs = 1 := by simp [sdGX]
      have hY0 : sdGY D δ D.cs = 1 := by simp [sdGY]
      rw [hX0, hY0] at hZ2
      have hZi : (2 ^ δ * L * T : ℤ) * 2 * sdGY D δ j = (T * m) * sdGX D δ j * sdDelta D D.cs j := by
        have hY := sdGY_ne_q D hD δ j
        have hX := sdGX_ne_q D hD δ j
        have hΔ := sdDelta_ne_q D hD hcs
        field_simp at hZ2
        have : ((2 ^ δ * L * T : ℤ) : ℚ) * 2 * (sdGY D δ j : ℚ) =
            (((T : ℤ) * m : ℤ) : ℚ) * (sdGX D δ j : ℚ) * (sdDelta D D.cs j : ℚ) := by
          push_cast at hZ2 ⊢; linear_combination hZ2
        exact_mod_cast this
      have hZp := congrArg (fun z : ℤ => (z : ZMod p)) hZi
      push_cast at hZp
      unfold kapL sdLam
      rw [frame_placeDer s D.fr zθ hplace D.cs]
      simp only [ssPlace, hplace]
      rw [hG, hG, hX0, hY0]
      have hW := frameW_ne_p D hpa D.cs
      have hWj := frameW_ne_p D hpa j
      have hdj := hpa j D.cs hj
      have hY := hGY j
      have hX := hGX j
      push_cast at hdj
      refine half_id _ _ _ _ _ _ _ _ hW hWj hX hY hdj ?_
      unfold sdTheta
      unfold sdDelta at hZp
      push_cast at hZp ⊢
      linear_combination hZp
    refine ⟨h2k, ?_⟩
    -- `κ = ½ + (Tm - 1)/2`
    have hTm : ((T : ℤ) * m) % 2 = 1 := by
      have h1 : Odd (T : ℤ) := by rw [Int.odd_iff]; omega
      have h2 : Odd m := Int.odd_iff.mpr hodd
      exact Int.odd_iff.mp (h1.mul h2)
    have hk : (T : ℤ) * m = 2 * (((T : ℤ) * m - 1) / 2) + 1 := by omega
    have hhalf : (2 : ZMod p) * ((halfZ p : ℤ) : ZMod p) = 1 := by
      have := halfZ_two' p (by have := (Fact.out : p.Prime).two_le; omega)
      have h' : ((2 * halfZ p : ℤ) : ZMod p) = ((p + 1 : ℤ) : ZMod p) := by rw [this]
      push_cast at h'; rw [h']; simp
    apply mul_left_cancel₀ h2p
    rw [h2k, mul_add, hhalf]
    conv_lhs => rw [hk]
    push_cast; ring

end R

end GeoSeq
