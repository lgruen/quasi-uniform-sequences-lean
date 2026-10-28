/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V95Defs
public import GeoSeq.V93Halton

@[expose] public section

/-!
# GeoSeq stage V9-5 (part 1): generator matrices, scrambles, reorderings (`cor:unscrambled`, `rem:randomize`(b))

* `genY_lin`, `seqPoint_eq_linPt`: a generator-matrix sequence over `ℤ/pℤ` is the linear-coordinate sequence
  `linPt p (genY C)`.
* `scrY_lin`, `scrY_isBAdic`, `smul_isRadInv`: a lower-triangular scramble of a `b`-adic coordinate is `b`-adic, and
  `μ` times a radical inverse with digit map `π` is a radical inverse with digit map `μπ` (`sec:polybases`).
* `not_qu_of_close`: close pairs at the prefixes `P_m` with `δ(P_m) p^{m/s} → 0` exclude quasi-uniformity (the last
  step of `thm:nonqu`, for any point sequence in `[0,1]^s`).
* **`unscrambled`**, **`unscrambled_frame`** (`cor:unscrambled`): one coordinate a scalar multiple of a radical inverse
  and every other a lower-triangular scramble of a `b_c`-adic coordinate (pairwise coprime bases) ⇒ not
  quasi-uniform; in particular the scrambled frame `C_ĉ = μ diag(β^n) P_{a_ĉ}`, `C_c = L_c P_{a_c}`.
* `close_comp`, `not_qu_comp`, `gray_*`, **`not_qu_gray`** (`rem:randomize`(b), the Gray-code order of
  `cor:sobol`): a reordering that permutes every prefix `{0, …, p^m - 1}` keeps the close pairs, so the reordered
  sequence is not quasi-uniform either; the Gray code permutes every `{0, …, 2^m - 1}`.
-/

namespace GeoSeq

open Finset Polynomial

section Field
variable {F : Type*} [Field F] {s : ℕ}

theorem genY_lin (C : Gen s F) (c : Fin s) : IsLinCoord (genY C c) := by
  intro V W n
  unfold genY
  rw [Polynomial.sum_add_index] <;> intros <;> ring

lemma genY_comb (P : ℕ → ℕ → F) (L : ℕ → ℕ → F) (V : F[X]) (n : ℕ) :
    V.sum (fun k a => (∑ j ∈ range (n + 1), L n j * P j k) * a) =
      ∑ j ∈ range (n + 1), L n j * V.sum (fun k a => P j k * a) := by
  unfold Polynomial.sum
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The Taylor coordinate at `a`: `Y(V)_n = [(z - a)^n] V` is the coordinate of the frame row `P_a`. -/
lemma pas_sum (a : F) (V : F[X]) (n : ℕ) :
    V.sum (fun k r => pas a n k * r) = (taylor a V).coeff n := by
  induction V using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.sum_add_index _ _ _ (fun _ => by ring) (fun _ _ _ => by ring), hP, hQ, map_add,
      coeff_add]
  | monomial k r =>
    rw [Polynomial.sum_monomial_index _ _ (by ring), ← C_mul_X_pow_eq_monomial, taylor_mul, taylor_C,
      taylor_X_pow, coeff_C_mul, coeff_X_add_C_pow, pas]
    ring

theorem scrY_lin (L : ℕ → ℕ → F) (Y : F[X] → ℕ → F) (hY : IsLinCoord Y) : IsLinCoord (scrY L Y) := by
  intro V W n
  unfold scrY
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [hY]; ring

/-- A lower-triangular scramble of a `b`-adic coordinate is `b`-adic (`sec:polybases`). -/
theorem scrY_isBAdic (L : ℕ → ℕ → F) (Y : F[X] → ℕ → F) (b : F[X]) (hY : IsBAdic Y b) :
    IsBAdic (scrY L Y) b := by
  intro Q V hV n hn
  unfold scrY
  exact Finset.sum_eq_zero fun j hj => by
    rw [hY Q V hV j (by have := Finset.mem_range.mp hj; omega), mul_zero]

/-- `μ` times a radical inverse with digit map `π` is a radical inverse with digit map `μπ` (`μ ≠ 0`). -/
theorem smul_isRadInv (μ : F) (hμ : μ ≠ 0) (Y : F[X] → ℕ → F) (b : F[X]) (π : F[X] → ℕ → F)
    (h : IsRadInv Y b π) : IsRadInv (fun V n => μ * Y V n) b (fun a i => μ * π a i) := by
  refine ⟨fun u => ?_, fun V Q i hi => by dsimp only; rw [h.2 V Q i hi]⟩
  obtain ⟨a, ha, hu⟩ := h.1 fun i => μ⁻¹ * u i
  exact ⟨a, ha, fun i hi => by dsimp only; rw [hu i hi, ← mul_assoc, mul_inv_cancel₀ hμ, one_mul]⟩

/-- The Taylor coordinate is `(z - a)`-adic. -/
theorem taylor_isBAdic (a : F) : IsBAdic (fun V n => (taylor a V).coeff n) (X - C a) := by
  intro Q V hV n hn
  rw [natDegree_X_sub_C, one_mul] at hn
  exact ((X_sub_C_pow_dvd_iff a Q V).mp hV) n hn

lemma taylor_lin (a : F) : IsLinCoord (fun V n => (taylor a V).coeff n) := by
  intro V W n; simp [map_add]

/-- The `β^{-1}(z - a)`-adic digits are `β^Q [(z-a)^Q] V` (constants). -/
lemma badicDigit_scaled (a β : F) (hβ : β ≠ 0) :
    ∀ (Q : ℕ) (V : F[X]), badicDigit (C β⁻¹ * (X - C a)) V Q = C (β ^ Q * (taylor a V).coeff Q) := by
  have hb : (C β⁻¹ * (X - C a)).natDegree = 1 := by
    rw [natDegree_C_mul (inv_ne_zero hβ), natDegree_X_sub_C]
  have hdec : ∀ V : F[X], V = C (V.eval a) + C β⁻¹ * (X - C a) * (C β * (V /ₘ (X - C a))) := by
    intro V
    have h := modByMonic_add_div V (X - C a)
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    have : C β⁻¹ * (X - C a) * (C β * (V /ₘ (X - C a))) = (X - C a) * (V /ₘ (X - C a)) := by
      rw [show C β⁻¹ * (X - C a) * (C β * (V /ₘ (X - C a))) =
        (C β⁻¹ * C β) * ((X - C a) * (V /ₘ (X - C a))) by ring, ← map_mul, inv_mul_cancel₀ hβ, map_one,
        one_mul]
    rw [this, h]
  have h0 : (C (eval a (0 : F[X]) : F) : F[X]).natDegree < 1 := by simp
  intro Q
  induction Q with
  | zero =>
    intro V
    rw [hdec V, badicDigit_base (by rw [natDegree_C, hb]; omega), pow_zero, one_mul,
      taylor_coeff_zero, ← hdec V]
  | succ Q ih =>
    intro V
    rw [hdec V, badicDigit_succ (by rw [natDegree_C, hb]; omega), ih, ← hdec V]
    congr 1
    have ht : (taylor a V).coeff (Q + 1) = (taylor a (V /ₘ (X - C a))).coeff Q := by
      have e : taylor a V = C (V.eval a) + X * taylor a (V /ₘ (X - C a)) := by
        conv_lhs => rw [← modByMonic_add_div V (X - C a)]
        rw [map_add, taylor_mul, taylor_X_sub_C, modByMonic_X_sub_C_eq_C_eval, taylor_C]
      rw [e, coeff_add, coeff_C, if_neg (Nat.succ_ne_zero Q), zero_add, coeff_X_mul]
    rw [ht, taylor_mul, taylor_C, coeff_C_mul, pow_succ]; ring

/-- The diagonally scaled frame coordinate `μ β^n [(z - a)^n] V` is the `β^{-1}(z - a)`-adic radical inverse with
digit map `a ↦ μ [z^0] a` (`cor:unscrambled`). -/
theorem scaledFrame_isRadInv (a μ β : F) (hμ : μ ≠ 0) (hβ : β ≠ 0) :
    IsRadInv (fun V n => μ * β ^ n * (taylor a V).coeff n) (C β⁻¹ * (X - C a))
      (fun r _ => μ * r.coeff 0) := by
  have hb : (C β⁻¹ * (X - C a)).natDegree = 1 := by
    rw [natDegree_C_mul (inv_ne_zero hβ), natDegree_X_sub_C]
  refine ⟨fun u => ⟨C (μ⁻¹ * u 0), by rw [natDegree_C, hb]; omega, fun i hi => ?_⟩, fun V Q i hi => ?_⟩
  · rw [hb] at hi
    obtain rfl : i = 0 := by omega
    dsimp only
    rw [coeff_C_zero, ← mul_assoc, mul_inv_cancel₀ hμ, one_mul]
  · rw [hb] at hi ⊢
    obtain rfl : i = 0 := by omega
    dsimp only
    rw [badicDigit_scaled a β hβ Q V, coeff_C_zero, mul_one, add_zero]; ring

lemma isCoprime_C_mul (u : F) (hu : u ≠ 0) {f g : F[X]} (h : IsCoprime f g) : IsCoprime (C u * f) g := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨C u⁻¹ * x, y, ?_⟩
  rw [show C u⁻¹ * x * (C u * f) = (C u⁻¹ * C u) * (x * f) by ring, ← map_mul, inv_mul_cancel₀ hu,
    map_one, one_mul, hxy]

end Field

section Prime
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

lemma genY_idx (C : Gen s (ZMod p)) (c : Fin s) (v n : ℕ) :
    genY C c (idxPolyP p v) n = seqDigit (zcode p) C v c n := by
  unfold genY seqDigit
  rw [Polynomial.sum_over_range' _ (fun k => by simp) (v + 1)
    (by have := natDegree_idxPolyP (p := p) v; omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_idxPolyP, if_pos (Finset.mem_range.mp hk)]; rfl

/-- A generator-matrix sequence over `ℤ/pℤ` is the linear-coordinate sequence of its rows. -/
theorem seqPoint_eq_linPt (C : Gen s (ZMod p)) : seqPoint (zcode p) C = linPt p (genY C) := by
  funext v c
  unfold seqPoint seqCoord linPt
  refine tsum_congr fun n => ?_
  rw [genY_idx]; rfl

end Prime

section Close
variable {s : ℕ}

/-- **Close pairs exclude quasi-uniformity** (last step of `thm:nonqu`): if for every `ε > 0` some prefix `P_m`
(`N = p^m` points, `p ≥ 2`) contains two distinct points closer than `ε p^{-m/s}`, the sequence is not quasi-uniform
(the covering radius of `p^m` points is `≥ p^{-m/s}/(2p)`). -/
theorem not_qu_of_close {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform pt := by
  rintro ⟨B, hB⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set ε := 1 / (2 * p * (|B| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨m, v, w, hv, hw, hvw, hd⟩ := hclose ε hε
  have hN : 2 ≤ p ^ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hv hw; omega
    · exact le_trans hp (Nat.le_self_pow (by omega) p)
  have hcov := covRadIdx_ge_pow hp hs pt hpt m
  have hsep := sepDistIdx_le_pair pt hv hw hvw
  have hsep0 := sepDistIdx_nonneg pt (p ^ m)
  set a := ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have h1 := hB _ hN
  have h2 : B * sepDistIdx pt (p ^ m) ≤ |B| * (ε * a) :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) hsep0).trans
      (mul_le_mul_of_nonneg_left (hsep.trans hd.le) (abs_nonneg B))
  have h3 : |B| * (ε * a) < a / (2 * p) := by
    rw [hεdef]
    have hB0 : 0 ≤ |B| := abs_nonneg B
    rw [show |B| * (1 / (2 * p * (|B| + 1)) * a) = (|B| / (|B| + 1)) * (a / (2 * p)) by field_simp]
    have : |B| / (|B| + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have hpos : 0 < a / (2 * p) := by positivity
    nlinarith
  linarith

/-- Reorderings that permute every prefix `{0, …, p^m - 1}` keep the close pairs (`rem:randomize`(b)). -/
theorem close_comp {p : ℕ} (pt : ℕ → Fin s → ℝ) (σ : ℕ → ℕ)
    (hσ : ∀ m v, v < p ^ m → ∃ v', v' < p ^ m ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist ((pt ∘ σ) v) ((pt ∘ σ) w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
  intro ε hε
  obtain ⟨m, v, w, hv, hw, hvw, hd⟩ := hclose ε hε
  obtain ⟨v', hv', rfl⟩ := hσ m v hv
  obtain ⟨w', hw', rfl⟩ := hσ m w hw
  exact ⟨m, v', w', hv', hw', fun h => hvw (by rw [h]), hd⟩

/-- `rem:randomize`(b): a sequence with close pairs stays non-quasi-uniform under every reordering that permutes
each prefix `{0, …, p^m - 1}`. -/
theorem not_qu_comp {p : ℕ} (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (σ : ℕ → ℕ)
    (hσ : ∀ m v, v < p ^ m → ∃ v', v' < p ^ m ∧ σ v' = v)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (pt v) (pt w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) :
    ¬ IsQuasiUniform (pt ∘ σ) :=
  not_qu_of_close hp hs _ (fun v c => hpt (σ v) c) (close_comp pt σ hσ hclose)

lemma gray_injective : Function.Injective gray := by
  intro a b h
  unfold gray at h
  have hx : a ^^^ b = (a ^^^ b) / 2 := by
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun x => Nat.testBit x i) h
    simp only [Nat.testBit_xor, Nat.testBit_div_two] at this ⊢
    revert this
    cases a.testBit i <;> cases b.testBit i <;> cases a.testBit (i + 1) <;> cases b.testBit (i + 1) <;>
      simp
  have h0 : a ^^^ b = 0 := by
    by_contra hne
    have := Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by norm_num : 1 < 2)
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun x => Nat.testBit x i) h0
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this
  cases a.testBit i <;> cases b.testBit i <;> simp

lemma gray_lt {m n : ℕ} (hn : n < 2 ^ m) : gray n < 2 ^ m :=
  Nat.xor_lt_two_pow hn (lt_of_le_of_lt (Nat.div_le_self n 2) hn)

/-- The Gray code permutes every prefix `{0, …, 2^m - 1}`. -/
theorem gray_surj (m v : ℕ) (hv : v < 2 ^ m) : ∃ v', v' < 2 ^ m ∧ gray v' = v := by
  obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (s := range (2 ^ m)) (t := range (2 ^ m))
    (fun a _ => gray a) (fun a ha => Finset.mem_range.mpr (gray_lt (Finset.mem_range.mp ha)))
    (fun a₁ a₂ _ _ h => gray_injective h) le_rfl v (Finset.mem_range.mpr hv)
  exact ⟨a, Finset.mem_range.mp ha, h.symm⟩

end Close

section Unscr
variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- **`cor:unscrambled`** (linear-coordinate form): let `b_0, …, b_{s-1}` be pairwise coprime of degrees `≥ 1`; let
coordinate `ĉ` be `μ` times a `b_ĉ`-adic radical inverse `Y_ĉ` (`μ ≠ 0`) and every other coordinate `c` be the
lower-triangular scramble `L_c` (arbitrary, fixed) of a `b_c`-adic coordinate `Y_c`. Then the sequence is not
quasi-uniform. -/
theorem unscrambled (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (μ : ZMod p) (hμ : μ ≠ 0) (L : Fin s → ℕ → ℕ → ZMod p) :
    ¬ IsQuasiUniform (linPt p fun c => if c = ch then fun V n => μ * Y ch V n else scrY (L c) (Y c)) := by
  classical
  refine (nonqu hs _ (fun c => ?_) b hdeg hcop ch (fun c hc => ?_) (fun a i => μ * π a i) ?_).2
  · by_cases h : c = ch
    · subst h; rw [if_pos rfl]; intro V W n; show μ * Y c (V + W) n = μ * Y c V n + μ * Y c W n
      rw [hY c V W n]; ring
    · simp only [if_neg h]; exact scrY_lin _ _ (hY c)
  · simp only [if_neg hc]; exact scrY_isBAdic _ _ _ (hbad c hc)
  · rw [if_pos rfl]; exact smul_isRadInv μ hμ _ _ _ hrad

/-- **`cor:unscrambled`**, "in particular": for distinct places, the scrambled frame `C_ĉ = μ diag(β^n) P_{a_ĉ}`,
`C_c = L_c P_{a_c}` (`c ≠ ĉ`, any `L_c`) is not quasi-uniform for any `μ, β ∈ 𝔽_p^*`. -/
theorem unscrambled_frame (hs : 2 ≤ s) (a : Fin s → ZMod p) (ha : Function.Injective a) (ch : Fin s)
    (μ β : ZMod p) (hμ : μ ≠ 0) (hβ : β ≠ 0) (L : Fin s → ℕ → ℕ → ZMod p) :
    ¬ IsQuasiUniform (seqPoint (zcode p) (scrFrame a ch μ β L)) := by
  classical
  set b : Fin s → (ZMod p)[X] := fun c => if c = ch then C β⁻¹ * (X - C (a ch)) else X - C (a c) with hbdef
  set Y : Fin s → (ZMod p)[X] → ℕ → ZMod p := fun c =>
    if c = ch then fun V n => β ^ n * (taylor (a ch) V).coeff n else fun V n => (taylor (a c) V).coeff n
    with hYdef
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := by
    intro c; by_cases h : c = ch
    · simp only [hbdef, if_pos h]; rw [natDegree_C_mul (inv_ne_zero hβ), natDegree_X_sub_C]
    · simp only [hbdef, if_neg h]; rw [natDegree_X_sub_C]
  have hcop : Pairwise fun c c' => IsCoprime (b c) (b c') := by
    intro c c' hcc
    have hX := pairwise_coprime_X_sub_C ha hcc
    by_cases h : c = ch
    · subst h
      simp only [hbdef, if_pos rfl, if_neg (Ne.symm hcc)]
      exact isCoprime_C_mul _ (inv_ne_zero hβ) hX
    · by_cases h' : c' = ch
      · subst h'
        simp only [hbdef, if_neg h, if_pos rfl]
        exact (isCoprime_C_mul _ (inv_ne_zero hβ) hX.symm).symm
      · simp only [hbdef, if_neg h, if_neg h']; exact hX
  have hY : ∀ c, IsLinCoord (Y c) := by
    intro c; by_cases h : c = ch
    · simp only [hYdef, if_pos h]; intro V W n; simp [map_add]; ring
    · simp only [hYdef, if_neg h]; exact taylor_lin _
  have hrad : IsRadInv (Y ch) (b ch) (fun r _ => r.coeff 0) := by
    have := scaledFrame_isRadInv (a ch) 1 β one_ne_zero hβ
    simp only [one_mul] at this
    simpa [hYdef, hbdef] using this
  have hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c) := fun c hc => by
    simp only [hYdef, hbdef, if_neg hc]; exact taylor_isBAdic _
  have key := unscrambled hs Y hY b hdeg hcop ch hbad _ hrad μ hμ L
  have e : seqPoint (zcode p) (scrFrame a ch μ β L) =
      linPt p (fun c => if c = ch then fun V n => μ * Y ch V n else scrY (L c) (Y c)) := by
    rw [seqPoint_eq_linPt]
    congr 1
    funext c V n
    by_cases h : c = ch
    · subst h
      simp only [scrFrame, genY, if_pos rfl, hYdef, ite_true]
      rw [← pas_sum]
      unfold Polynomial.sum
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [scrFrame, genY, if_neg h, hYdef, scrY]
      rw [genY_comb (fun j k => pas (a c) j k) (L c) V n]
      exact Finset.sum_congr rfl fun j _ => by rw [pas_sum]
  rw [e]; exact key

end Unscr

end GeoSeq
