/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_1Defs
public import GeoSeq.V93Thm
public import GeoSeq.V95Gen

@[expose] public section

/-!
# GeoSeq stage V10-1 (part 5): `rem:randomize`(a) — digital shifts

A digital shift `y_{c,n}(V) ↦ y_{c,n}(V) + σ_{c,n}` (`shiftY`) of a sequence covered by `thm:nonqu` is still not
quasi-uniform. As in the paper: the first `L = eλ` digits of the radical-inverse coordinate `ĉ` are an onto function
of `V mod b^λ` (`radInv_prefix`), so there is `V_1` of degree `< L` whose SHIFTED digits are
`(0^{eη}, 0, -1, …, -1)` (`y° = 0`, `ȳ = -1`) on the positions `< L`; the pair `V_1`, `V_1 + D` works as before, the
other coordinates sharing their first `L` shifted digits. The only change: a shifted coordinate may have infinitely
many digits `p - 1`, so the tails lie in `[0, p^{-L}]` (`real_carry_le`) and the bound is `≤ √(s+3) p^{-L}`
(`shift_pair`); `V_1` is not the paper's `g̃ b^η + g' b^{η+1} S` (whose digits are only right before the shift), and the
digits of `V_1` below `eη` are free.

* `real_carry_le`: the carry estimate with non-strict tails, `|y(x') - y(x)| ≤ 2 p^{-L}`.
* `badicDigit_sum`, **`radInv_prefix`**: prescribed first `eλ` digits of a radical inverse.
* **`shift_pair`** (`lem:carrypair` for shifted sequences), `nonquD_props` (the conditions (i)–(iii) of
  `lem:carrypair` for the `D_Q` of `thm:nonqu`), **`shift_nonqu`** (`rem:randomize`(a)).
-/

namespace GeoSeq

open Finset Polynomial

section Real

/-- The carry with arbitrary tails: digits `x = ⋯ a (p-1)^{L-k-1} ⋯` and `x' = ⋯ (a+1) 0^{L-k-1} ⋯` (equal before
position `k`): `|y(x') - y(x)| ≤ 2 p^{-L}`. -/
theorem real_carry_le {p : ℕ} (hp : 2 ≤ p) (d d' : ℕ → ℕ) (hd : ∀ j, d j < p) (hd' : ∀ j, d' j < p)
    {k L : ℕ} (hkL : k < L) (h0 : ∀ j, j < k → d j = d' j) (h1 : d' k = d k + 1)
    (h2 : ∀ j, k < j → j < L → d j = p - 1 ∧ d' j = 0) :
    |∑' j, (d' j : ℝ) / (p : ℝ) ^ (j + 1) - ∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1)| ≤ 2 / (p : ℝ) ^ L := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  obtain ⟨τ, h0τ, h1τ, -, he⟩ := tsum_split hp d hd L
  obtain ⟨τ', h0τ', h1τ', -, he'⟩ := tsum_split hp d' hd' L
  have hpre : ∀ t, k + 1 + t ≤ L →
      ∑ j ∈ range (k + 1 + t), ((d' j : ℝ) / (p : ℝ) ^ (j + 1) - (d j : ℝ) / (p : ℝ) ^ (j + 1)) =
        1 / (p : ℝ) ^ (k + 1 + t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [add_zero, Finset.sum_range_succ,
        Finset.sum_eq_zero fun j hj => by rw [h0 j (Finset.mem_range.mp hj), sub_self], zero_add, h1]
      push_cast; ring
    | succ t ih =>
      intro ht'
      rw [show k + 1 + (t + 1) = (k + 1 + t) + 1 by ring, Finset.sum_range_succ, ih (by omega)]
      obtain ⟨ha, hb⟩ := h2 (k + 1 + t) (by omega) (by omega)
      rw [ha, hb, Nat.cast_sub (by omega)]
      push_cast
      rw [pow_succ]
      field_simp
      ring
  have hL := hpre (L - k - 1) (by omega)
  rw [show k + 1 + (L - k - 1) = L by omega, Finset.sum_sub_distrib] at hL
  have hpL : (0 : ℝ) < 1 / (p : ℝ) ^ L := by positivity
  have h2L : 2 / (p : ℝ) ^ L = 2 * (1 / (p : ℝ) ^ L) := by ring
  rw [he, he', abs_le, h2L]
  constructor <;> linarith

end Real

section Prefix
variable {F : Type*} [Field F]

/-- The `b`-adic digits of `∑_{j<n} a_j b^j` (`deg a_j < deg b`) are the `a_j`. -/
lemma badicDigit_sum {b : F[X]} :
    ∀ (n : ℕ) (as : ℕ → F[X]), (∀ j, (as j).natDegree < b.natDegree) →
      ∀ Q, badicDigit b (∑ j ∈ range n, as j * b ^ j) Q = if Q < n then as Q else 0 := by
  intro n
  induction n with
  | zero => intro as _ Q; simp [badicDigit_zero]
  | succ n ih =>
    intro as has Q
    have e : ∑ j ∈ range (n + 1), as j * b ^ j = as 0 + b * ∑ j ∈ range n, as (j + 1) * b ^ j := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    rcases Q with _ | Q
    · rw [badicDigit_base (has 0), if_pos (Nat.succ_pos n)]
    · rw [badicDigit_succ (has 0), ih (fun j => as (j + 1)) (fun j => has _) Q]
      by_cases h : Q < n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

/-- **Prescribed leading digits of a radical inverse**: for a `b`-adic radical inverse (digit map onto the digit
blocks) and any target digits `t`, some `W` of degree `< e λ` has the digits `t_n` at all positions `n < e λ`. -/
theorem radInv_prefix {Y : F[X] → ℕ → F} {b : F[X]} {π : F[X] → ℕ → F} (hb : 1 ≤ b.natDegree)
    (hrad : IsRadInv Y b π) (t : ℕ → F) (l : ℕ) (hl : 1 ≤ l) :
    ∃ W : F[X], W.natDegree < b.natDegree * l ∧ ∀ n, n < b.natDegree * l → Y W n = t n := by
  set e := b.natDegree with he
  choose a ha hπ using fun Q : ℕ => hrad.1 (fun i => t (Q * e + i))
  refine ⟨∑ j ∈ range l, a j * b ^ j, ?_, fun n hn => ?_⟩
  · have h1 : ∀ j ∈ range l, (a j * b ^ j).natDegree ≤ e * l - 1 := by
      intro j hj
      have hj := Finset.mem_range.mp hj
      refine natDegree_mul_le.trans ?_
      rw [natDegree_pow]
      have h2 := ha j
      have h3 : (j + 1) * e ≤ l * e := Nat.mul_le_mul_right _ hj
      have h4 : e * l = l * e := mul_comm _ _
      rw [← he] at h2 ⊢
      have : (a j).natDegree + j * e + 1 ≤ e * l := by nlinarith
      omega
    have h5 := natDegree_sum_le_of_forall_le _ _ h1
    have : 1 ≤ e * l := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  · have hn' := Nat.div_add_mod' n e
    have hQ : n / e < l := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [mul_comm]; exact hn)
    rw [← hn', hrad.2 _ _ _ (Nat.mod_lt _ (by omega)), badicDigit_sum l a ha, if_pos hQ,
      hπ _ _ (Nat.mod_lt _ (by omega))]

end Prefix

section Pair
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`lem:carrypair` for digitally shifted sequences** (`rem:randomize`(a)): with the hypotheses of `lem:carrypair`
on the linear coordinates `Y` (only `g` with `π(g) = (1, …, 1)` is needed) and ANY digital shift `σ`, some `V_1` of
degree `< m` and `V_1 + D` (indices `< p^m`, distinct) have shifted points at Euclidean distance
`≤ √(s+3) p^{-L}`, `L = eλ`. -/
theorem shift_pair (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (σ : Fin s → ℕ → ZMod p) (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g : (ZMod p)[X]) (hg : g.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (D : (ZMod p)[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    ∃ V : (ZMod p)[X], polyIdx p V < p ^ m ∧ polyIdx p (V + D) < p ^ m ∧ polyIdx p V ≠ polyIdx p (V + D) ∧
      euclDist (linPt p (shiftY Y σ) (polyIdx p V)) (linPt p (shiftY Y σ) (polyIdx p (V + D))) ≤
        Real.sqrt (s + 3) / (p : ℝ) ^ ((b ch).natDegree * l) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have he1 : 1 ≤ (b ch).natDegree := hdeg ch
  set B := b ch with hB
  set e := B.natDegree with he
  set L := e * l with hL
  set T : ℕ → ZMod p := fun n => if n ≤ e * η then 0 else -1 with hT
  obtain ⟨V, hVdeg, hVdig⟩ := radInv_prefix he1 hrad (fun n => T n - σ ch n) l (by omega)
  have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs
  obtain ⟨c0, hc0⟩ := exists_ne ch
  obtain ⟨j0, hj0, hdj0⟩ := hii c0 hc0
  have hLD : L ≤ D.natDegree := by
    have h := natDegree_le_of_dvd hdj0 hD
    rw [natDegree_pow] at h
    exact hj0.trans (by rw [mul_comm]; exact h)
  have hVL : V.natDegree < L := hVdeg
  have hVm : V.natDegree < m := by omega
  have hV2m : (V + D).natDegree < m := lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hVm hiii)
  have hne : V ≠ V + D := fun h => hD (left_eq_add.mp h)
  refine ⟨V, polyIdx_lt _ hVm, polyIdx_lt _ hV2m, fun h => hne (polyIdx_injective h), ?_⟩
  /- the other coordinates share their first `L` shifted digits -/
  have hother : ∀ c, c ≠ ch → |linPt p (shiftY Y σ) (polyIdx p V) c - linPt p (shiftY Y σ) (polyIdx p (V + D)) c| ≤
      1 / (p : ℝ) ^ L := by
    intro c hc
    rw [linPt_polyIdx, linPt_polyIdx]
    refine real_prefix hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) L fun j hj => ?_
    obtain ⟨jc, hjc, hdc⟩ := hii c hc
    simp only [shiftY]
    rw [hY c V D j, hbad c hc jc D hdc j (lt_of_lt_of_le hj hjc), add_zero]
  /- the digits of `D` in coordinate `ĉ` -/
  have hpi0 : ∀ i, i < e → π 0 i = 0 := fun i hi => hrad.pi_zero (hY ch) hi
  have hgf : g * B ^ η * runS B (l - η) = B ^ η * (g * runS B (l - η)) := by ring
  have hdigD' : ∀ n, n < L → Y ch D n = if n < e * η then 0 else 1 := by
    intro n hn
    have hn' := Nat.div_add_mod' n e
    have hQl : n / e < l := (Nat.div_lt_iff_lt_mul he1).mpr (by rw [hL] at hn; linarith)
    rw [← hn', hrad.2 D (n / e) (n % e) (Nat.mod_lt _ he1), badicDigit_congr he1 hi hQl, hgf,
      badicDigit_pow_mul he1, hn']
    by_cases hQ : n / e < η
    · rw [ite_eq_left hQ, hpi0 _ (Nat.mod_lt _ he1),
        ite_eq_left (by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul he1).mp hQ)]
    · rw [ite_eq_right hQ, badicDigit_run hg, ite_eq_left (by omega), hπg _ (Nat.mod_lt _ he1),
        ite_eq_right (by rw [mul_comm]; intro h; exact hQ ((Nat.div_lt_iff_lt_mul he1).mpr h))]
  /- the shifted digits of `V` and `V + D` in coordinate `ĉ` below `L` -/
  have hsV : ∀ n, n < L → shiftY Y σ ch V n = T n := fun n hn => by
    simp only [shiftY]; rw [hVdig n (by exact hn)]; ring
  have hsV2 : ∀ n, n < L → shiftY Y σ ch (V + D) n = T n + Y ch D n := fun n hn => by
    have := hsV n hn
    simp only [shiftY] at this ⊢
    rw [hY ch V D n]; linear_combination this
  obtain ⟨hvm1, hv0, hv1, -, -⟩ := (carrydigit_prime : (-1 : ZMod p).val = p - 1 ∧ _)
  have hkL : e * η < L := by rw [hL]; exact Nat.mul_lt_mul_of_pos_left hηl he1
  have hch : |linPt p (shiftY Y σ) (polyIdx p (V + D)) ch - linPt p (shiftY Y σ) (polyIdx p V) ch| ≤
      2 / (p : ℝ) ^ L := by
    rw [linPt_polyIdx, linPt_polyIdx]
    refine real_carry_le hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) hkL ?_ ?_ ?_
    · intro j hj
      rw [hsV2 j (by omega), hsV j (by omega), hdigD' j (by omega), if_pos hj, add_zero]
    · rw [hsV2 _ hkL, hsV _ hkL, hdigD' _ hkL, if_neg (lt_irrefl _)]
      simp only [hT, if_pos le_rfl, zero_add]
      rw [hv1]
    · intro j hj1 hj2
      rw [hsV2 j hj2, hsV j hj2, hdigD' j hj2, if_neg (by omega)]
      simp only [hT, if_neg (show ¬ j ≤ e * η by omega)]
      exact ⟨hvm1, (congrArg ZMod.val (neg_add_cancel (1 : ZMod p))).trans hv0⟩
  /- the distance -/
  set x := linPt p (shiftY Y σ) (polyIdx p V)
  set y := linPt p (shiftY Y σ) (polyIdx p (V + D))
  have hpL : (0 : ℝ) < 1 / (p : ℝ) ^ L := by positivity
  have hsq_ch : (x ch - y ch) ^ 2 ≤ 4 * (1 / (p : ℝ) ^ L) ^ 2 := by
    have h := hch
    rw [abs_sub_comm] at h
    have h2 : (2 : ℝ) / (p : ℝ) ^ L = 2 * (1 / (p : ℝ) ^ L) := by ring
    rw [h2] at h
    have := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
    nlinarith
  have hsq_o : ∑ c ∈ univ.erase ch, (x c - y c) ^ 2 ≤ ((s : ℝ) - 1) * (1 / (p : ℝ) ^ L) ^ 2 := by
    have h1 : ∀ c ∈ univ.erase ch, (x c - y c) ^ 2 ≤ (1 / (p : ℝ) ^ L) ^ 2 := by
      intro c hc
      have h := hother c (Finset.ne_of_mem_erase hc)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega)]
    simp
  have hsum : ∑ c, (x c - y c) ^ 2 ≤ ((s : ℝ) + 3) * (1 / (p : ℝ) ^ L) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ch)]
    linarith
  unfold euclDist
  calc Real.sqrt (∑ c, (x c - y c) ^ 2) ≤ Real.sqrt (((s : ℝ) + 3) * (1 / (p : ℝ) ^ L) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (s + 3) / (p : ℝ) ^ L := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpL.le]; ring

/-- The conditions (i)–(iii) of `lem:carrypair` for the difference `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}` of `thm:nonqu`
(`Q = p^w`), and `e λ_Q = L_Q = Q E (k+1)` (the computation inside `nonqu_pair`). -/
theorem nonquD_props (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g : (ZMod p)[X]) (hg : g.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (hs : 1 ≤ s) (w : ℕ) :
    nonquD b ch g ν k η (p ^ w) ≠ 0 ∧
      b ch ^ (p ^ w * (η + ν)) ∣ nonquD b ch g ν k η (p ^ w) -
        g * b ch ^ (p ^ w * η) * runS (b ch) (p ^ w * (η + ν) - p ^ w * η) ∧
      (∀ c, c ≠ ch → ∃ j, (b ch).natDegree * (p ^ w * (η + ν)) ≤ (b c).natDegree * j ∧
        b c ^ j ∣ nonquD b ch g ν k η (p ^ w)) ∧
      (nonquD b ch g ν k η (p ^ w)).natDegree < p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) ∧
      (b ch).natDegree * (p ^ w * (η + ν)) = p ^ w * lcmDeg b * (k + 1) := by
  have hp : p.Prime := Fact.out
  have hQ1 : 1 ≤ p ^ w := Nat.one_le_pow _ _ hp.pos
  set B := b ch with hBdef
  set e := B.natDegree with hedef
  set E := lcmDeg b with hEdef
  set Θ := thetaP b ch with hΘdef
  have he1 : 1 ≤ e := hdeg ch
  have hEe : e * (E / e) = E := Nat.mul_div_cancel' (lcmDeg_dvd b ch)
  have hlam : e * (p ^ w * (η + ν)) = p ^ w * E * (k + 1) := by
    rw [hη]
    calc e * (p ^ w * (E / e * (k + 1))) = p ^ w * (e * (E / e)) * (k + 1) := by ring
      _ = p ^ w * E * (k + 1) := by rw [hEe]
  have hB0 : B ≠ 0 := ne_zero_of_natDegree he1
  have hΘ0 : Θ ≠ 0 := thetaP_ne_zero b hdeg ch
  have h1B : (1 : (ZMod p)[X]) - B ≠ 0 := one_sub_ne_zero he1
  have hQν : 1 ≤ p ^ w * ν := Nat.one_le_iff_ne_zero.mpr (by positivity)
  obtain ⟨H, hH⟩ := hΘ
  have hΘQ : Θ ^ (p ^ w * k) = 1 + B ^ (p ^ w * ν) * H ^ p ^ w := by
    have h1 : Θ ^ k = 1 + B ^ ν * H := by linear_combination hH
    rw [mul_comm (p ^ w) k, pow_mul, h1, add_pow_char_pow, one_pow, mul_pow, ← pow_mul, mul_comm ν]
  set D := nonquD b ch g ν k η (p ^ w) with hDdef
  have hi : B ^ (p ^ w * (η + ν)) ∣ D - g * B ^ (p ^ w * η) * runS B (p ^ w * (η + ν) - p ^ w * η) := by
    rw [show p ^ w * (η + ν) - p ^ w * η = p ^ w * ν by rw [mul_add]; omega]
    refine ⟨g * runS B (p ^ w * ν) * H ^ p ^ w, ?_⟩
    rw [hDdef, nonquD, ← hBdef, ← hΘdef, hΘQ,
      show p ^ w * (η + ν) = p ^ w * η + p ^ w * ν by ring, pow_add]
    ring
  have hS : Θ ^ p ^ w ∣ runS B (p ^ w * ν) := by
    obtain ⟨Rq, hRq⟩ := hR
    refine dvd_of_sub_one_mul hQ1 h1B (Rq := Rq ^ p ^ w) ?_
    have h1 : B ^ (p ^ w * ν) - 1 = (B ^ ν - 1) ^ p ^ w := by
      rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm]
    rw [runS_mul, h1, hRq, mul_pow]
    rfl
  obtain ⟨S', hS'⟩ := hS
  have hΘD : Θ ^ (p ^ w * (k + 1)) ∣ D :=
    ⟨g * B ^ (p ^ w * η) * S', by rw [hDdef, nonquD, ← hBdef, ← hΘdef, hS']; ring⟩
  have hii : ∀ c, c ≠ ch → ∃ j, e * (p ^ w * (η + ν)) ≤ (b c).natDegree * j ∧ b c ^ j ∣ D := by
    intro c hc
    refine ⟨E / (b c).natDegree * (p ^ w * (k + 1)), le_of_eq ?_, ?_⟩
    · rw [hlam, ← mul_assoc, Nat.mul_div_cancel' (lcmDeg_dvd b c)]; ring
    · refine dvd_trans ?_ hΘD
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ c⟩)) _
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h := hπg 0 he1
    rw [hrad.pi_zero (hY ch) he1] at h
    exact zero_ne_one h
  have hD0 : D ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hg0 (pow_ne_zero _ hB0)) (runS_ne_zero he1 hQν))
      (pow_ne_zero _ hΘ0)
  have hdegD : D.natDegree < p ^ w * (s * E * (k + 1) - (s - 1) * E) := by
    have h1 : D.natDegree ≤ g.natDegree + (p ^ w * η) * e + e * (p ^ w * ν - 1) +
        (p ^ w * k) * ((s - 1) * E) := by
      rw [hDdef, nonquD]
      refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_mul_le.trans (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add_left natDegree_pow_le _)) (natDegree_runS _ _)))
        (natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_thetaP b ch))))
    rw [nonqu_m_eq s E k hs]
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    obtain ⟨n', hn'⟩ : ∃ n', p ^ w * ν = n' + 1 := ⟨p ^ w * ν - 1, by omega⟩
    have h2 : e * (p ^ w * η) + e * (p ^ w * ν) = p ^ w * E * (k + 1) := by rw [← hlam]; ring
    rw [hn', Nat.add_sub_cancel] at h1
    rw [hn', he'] at h2
    rw [he'] at h1 hg
    have h3 : p ^ w * k * ((s - 1) * E) = p ^ w * ((s - 1) * E * k) := by ring
    rw [mul_add]
    nlinarith
  exact ⟨hD0, hi, hii, hdegD, hlam⟩

/-- **`rem:randomize`(a)** (digital shifts): let the linear coordinates `Y` satisfy the hypotheses of `thm:nonqu`
(pairwise coprime bases of degree `≥ 1`, coordinate `ĉ` a `b_ĉ`-adic radical inverse, the others `b_c`-adic), and
let `σ_{c,n} ∈ 𝔽_p` be any digital shift. Then for every `ε > 0` some prefix `P_m` of the shifted sequence contains
two points at Euclidean distance `< ε p^{-m/s}`, and the shifted sequence is not quasi-uniform. -/
theorem shift_nonqu (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (σ : Fin s → ℕ → ZMod p) (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (linPt p (shiftY Y σ) v) (linPt p (shiftY Y σ) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPt p (shiftY Y σ)) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨g, hg, hπg⟩ := hrad.1 fun _ => 1
  obtain ⟨ν, k, η, hν, -, hR, hΘ, hη⟩ := nonqu_exists b hdeg hcop ch
  set E := lcmDeg b with hE
  have hE1 : 1 ≤ E := lcmDeg_pos b hdeg
  have hs0 : s ≠ 0 := by omega
  have hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (linPt p (shiftY Y σ) v) (linPt p (shiftY Y σ) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
    intro ε hε
    set ε2 := ε / 2 with hε2
    have hε2p : 0 < ε2 := by positivity
    set K := Real.sqrt (s + 3) ^ s with hK
    obtain ⟨w, hw⟩ := exists_nat_gt (K / ε2 ^ s)
    have hQw : (w : ℝ) < (p ^ w : ℕ) := by exact_mod_cast Nat.lt_pow_self hp.one_lt
    set Q := p ^ w with hQ
    set L := Q * E * (k + 1) with hL
    set m := Q * (s * E * (k + 1) - (s - 1) * E) with hm
    obtain ⟨hD0, hi, hii, hdegD, hlam⟩ := nonquD_props Y hY b hdeg ch π hrad g hg hπg ν k η hν hR hΘ hη
      (by omega) w
    have hηl : Q * η < Q * (η + ν) := by rw [mul_add]; have : 1 ≤ Q * ν := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
    obtain ⟨V, h1, h2, h3, h4⟩ := shift_pair hs Y hY σ b hdeg ch hbad π hrad g hg hπg _ hD0 (Q * η) (Q * (η + ν))
      m hηl hi hii hdegD
    rw [hlam] at h4
    set a := ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨m, _, _, h1, h2, h3, h4.trans_lt (lt_of_le_of_lt (b := ε2 * a) ?_ (by rw [hε2]; nlinarith))⟩
    refine le_of_pow_le_pow_left₀ hs0 (by positivity) ?_
    have hexc : (p : ℝ) ^ (s * L) = (p : ℝ) ^ m * (p : ℝ) ^ (Q * ((s - 1) * E)) := by
      rw [← pow_add]; congr 1; exact nonqu_excess s E k Q (by omega)
    have hX : (Q : ℝ) ≤ (p : ℝ) ^ (Q * ((s - 1) * E)) := by
      have h5 : Q < p ^ Q := Nat.lt_pow_self hp.one_lt
      have h6 : p ^ Q ≤ p ^ (Q * ((s - 1) * E)) :=
        Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hE1))
      exact_mod_cast (h5.trans_le h6).le
    have hKQ : K < ε2 ^ s * Q := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε2 ^ s)).mp (hw.trans hQw)
      linarith
    rw [div_pow, mul_pow, ha, rpow_neg_inv_pow (by positivity) hs0, ← pow_mul, mul_comm L s, hexc,
      div_le_iff₀ (by positivity)]
    rw [← hK]
    calc K ≤ ε2 ^ s * (p : ℝ) ^ (Q * ((s - 1) * E)) := by
          nlinarith [pow_pos hε2p s]
      _ = ε2 ^ s * ((p : ℝ) ^ m)⁻¹ * ((p : ℝ) ^ m * (p : ℝ) ^ (Q * ((s - 1) * E))) := by
          field_simp
  exact ⟨hclose, not_qu_of_close hp2 (by omega) _ (fun v c => linPt_mem _ v c) hclose⟩

end Pair

end GeoSeq
