/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V93Carry

@[expose] public section

/-!
# GeoSeq stage V9-3 (part 3): polynomial-base digital sequences are not quasi-uniform (`thm:nonqu`)

Prime base `q = p` (the paper states `thm:nonqu` over `𝔽_q`; prime powers are stage V9-5).

* `exists_pow_sub_one_dvd`: a unit modulo `R ≠ 0` over a finite field has a power `≡ 1 (mod R)` (the order
  in the finite ring `𝔽[z]/(R)`, as `AdjoinRoot R`).
* `nonqu_exists`: admissible `ν`, `k`, `η` exist (`thm:nonqu`, "Existence of `ν` and `k`").
* **`nonqu_pair`** (`thm:nonqu`, the explicit pairs): for `Q = p^w`, `D_Q` satisfies (i)–(iii) of
  `lem:carrypair`, so the indices `ι(V_1)`, `ι(V_1 + D_Q)` are distinct, `< p^{m_Q}`, and the points are at
  distance `< √(s+3) p^{-L_Q}`, `L_Q = Q E (k+1)`, `m_Q = Q (s E (k+1) - (s-1) E)`. Frobenius:
  `(1 + b^ν H)^Q = 1 + b^{Qν} H^Q` and `(b^ν - 1)^Q = b^{Qν} - 1` (`add_pow_char_pow`, `sub_pow_char_pow`).
* `nonqu_excess`: `s L_Q = m_Q + Q (s-1) E` (the excess `sL - m` of `lem:carrypair` grows linearly in `Q`).
* `covRadIdx_ge`: `h(P_{[N]}) ≥ 1/(2M)` whenever `N < M^s` (pigeonhole: an empty grid cell; this replaces the
  paper's volume bound `h ≥ ω_s^{-1/s} N^{-1/s}`, plan §2.4), and `covRadIdx_ge_pow`: `h(P_m) ≥ p^{-m/s}/(2p)`.
* **`nonqu`** (`thm:nonqu`): for every `ε > 0` some prefix `P_m` contains two points at Euclidean distance
  `< ε p^{-m/s}`, and the sequence is not quasi-uniform.
-/

namespace GeoSeq

open Finset Polynomial

/-! ## Orders modulo `R` -/

lemma exists_pow_sub_one_dvd {F : Type*} [Field F] [Finite F] {R a : F[X]} (hR : R ≠ 0)
    (hc : IsCoprime a R) : ∃ ν, 1 ≤ ν ∧ R ∣ a ^ ν - 1 := by
  have : Module.Finite F (AdjoinRoot R) := (AdjoinRoot.powerBasis hR).finite
  have : Finite (AdjoinRoot R) := Module.finite_of_finite F
  obtain ⟨x, y, hxy⟩ := hc
  have hu : IsUnit (AdjoinRoot.mk R a) := by
    refine IsUnit.of_mul_eq_one (AdjoinRoot.mk R x) ?_
    have := congrArg (AdjoinRoot.mk R) hxy
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] at this
    rw [mul_comm]; exact this
  obtain ⟨u, hu⟩ := hu
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  have h1 : (AdjoinRoot.mk R a) ^ orderOf u = AdjoinRoot.mk R 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one]; simp
  rw [← map_pow] at h1
  exact AdjoinRoot.mk_eq_mk.mp h1

section Alg
variable {F : Type*} [Field F] {s : ℕ}

lemma one_sub_ne_zero {B : F[X]} (hB : 1 ≤ B.natDegree) : (1 : F[X]) - B ≠ 0 := by
  intro h
  have : B = 1 := (sub_eq_zero.mp h).symm
  rw [this, natDegree_one] at hB; omega

lemma thetaP_ne_zero (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s) :
    thetaP b ch ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun c _ => pow_ne_zero _ (ne_zero_of_natDegree (hdeg c))

lemma lcmDeg_dvd (b : Fin s → F[X]) (c : Fin s) : (b c).natDegree ∣ lcmDeg b :=
  Finset.dvd_lcm (Finset.mem_univ c)

lemma lcmDeg_pos (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) : 0 < lcmDeg b := by
  rcases Nat.eq_zero_or_pos (lcmDeg b) with h | h
  · rw [lcmDeg, Finset.lcm_eq_zero_iff] at h
    obtain ⟨c', -, hc'⟩ := h
    have := hdeg c'
    omega
  · exact h

lemma natDegree_thetaP (b : Fin s → F[X]) (ch : Fin s) :
    (thetaP b ch).natDegree ≤ (s - 1) * lcmDeg b := by
  unfold thetaP
  refine (natDegree_prod_le _ _).trans ?_
  have h1 : ∀ c ∈ univ.erase ch, (b c ^ (lcmDeg b / (b c).natDegree)).natDegree ≤ lcmDeg b := by
    intro c _
    refine natDegree_pow_le.trans (le_of_eq ?_)
    exact Nat.div_mul_cancel (lcmDeg_dvd b c)
  refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul]

lemma coprime_b_carryR (b : Fin s → F[X]) (hcop : Pairwise fun c c' => IsCoprime (b c) (b c'))
    (ch : Fin s) : IsCoprime (b ch) (thetaP b ch) ∧ IsCoprime (b ch) (carryR b ch) := by
  have h1 : IsCoprime (b ch) (thetaP b ch) :=
    IsCoprime.prod_right fun c hc => (hcop (Finset.ne_of_mem_erase hc).symm).pow_right
  refine ⟨h1, IsCoprime.mul_right ⟨1, 1, by ring⟩ h1⟩

/-- From `(b - 1) S = ((1 - b) Θ)^n Rq` with `n ≥ 1`, cancel one factor `1 - b`: `Θ^n ∣ S`. -/
lemma dvd_of_sub_one_mul {B Θ Rq S : F[X]} {n : ℕ} (hn : 1 ≤ n) (h1B : 1 - B ≠ 0)
    (h : (B - 1) * S = ((1 - B) * Θ) ^ n * Rq) : Θ ^ n ∣ S := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [mul_pow] at h
  have h2 : (1 - B) * (-S) = (1 - B) * ((1 - B) ^ n' * Θ ^ (n' + 1) * Rq) := by linear_combination h
  have h3 := mul_left_cancel₀ h1B h2
  exact ⟨-((1 - B) ^ n' * Rq), by linear_combination -h3⟩

end Alg

/-! ## The explicit pairs -/

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- `thm:nonqu`, existence of `ν` and `k`: `R ∣ b^ν - 1` with `ν ≥ 1`, and `b^ν ∣ Θ^k - 1` with
`k ≥ 1` and `(E/e)(k + 1) ≥ ν`; then `η = (E/e)(k + 1) - ν`. -/
theorem nonqu_exists (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s) :
    ∃ ν k η : ℕ, 1 ≤ ν ∧ 1 ≤ k ∧ carryR b ch ∣ b ch ^ ν - 1 ∧ b ch ^ ν ∣ thetaP b ch ^ k - 1 ∧
      η + ν = lcmDeg b / (b ch).natDegree * (k + 1) := by
  obtain ⟨hcΘ, hcR⟩ := coprime_b_carryR b hcop ch
  have hR0 : carryR b ch ≠ 0 :=
    mul_ne_zero (one_sub_ne_zero (hdeg ch)) (thetaP_ne_zero b hdeg ch)
  obtain ⟨ν, hν, hR⟩ := exists_pow_sub_one_dvd hR0 hcR
  have hb0 : b ch ^ ν ≠ 0 := pow_ne_zero _ (ne_zero_of_natDegree (hdeg ch))
  obtain ⟨k0, hk0, hk⟩ := exists_pow_sub_one_dvd hb0 hcΘ.symm.pow_right
  have hk' : b ch ^ ν ∣ thetaP b ch ^ (k0 * ν) - 1 := by
    refine hk.trans ?_
    have := sub_dvd_pow_sub_pow (thetaP b ch ^ k0) 1 ν
    rwa [one_pow, ← pow_mul] at this
  have hE : 1 ≤ lcmDeg b / (b ch).natDegree :=
    Nat.div_pos (Nat.le_of_dvd (lcmDeg_pos b hdeg) (lcmDeg_dvd b ch)) (by have := hdeg ch; omega)
  have hkν : ν ≤ k0 * ν := Nat.le_mul_of_pos_left _ hk0
  have hle : ν ≤ lcmDeg b / (b ch).natDegree * (k0 * ν + 1) :=
    hkν.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hE))
  exact ⟨ν, k0 * ν, lcmDeg b / (b ch).natDegree * (k0 * ν + 1) - ν, hν, hkν.trans' hν, hR, hk',
    Nat.sub_add_cancel hle⟩

lemma nonqu_m_eq (s E k : ℕ) (hs : 1 ≤ s) :
    s * E * (k + 1) - (s - 1) * E = E * (k + 1) + (s - 1) * E * k := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add; ring

/-- `s L_Q = m_Q + Q (s-1) E`: the excess `s L - m` of `lem:carrypair` is `Q (s-1) E`. -/
theorem nonqu_excess (s E k Q : ℕ) (hs : 1 ≤ s) :
    s * (Q * E * (k + 1)) = Q * (s * E * (k + 1) - (s - 1) * E) + Q * ((s - 1) * E) := by
  rw [nonqu_m_eq s E k hs]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel]; ring

/-- **`thm:nonqu`** (prime `q = p`), the explicit pairs. Let the bases `b_c` have degrees `e_c ≥ 1` (pairwise
coprimality is used only for the existence of `ν`, `k`, `nonqu_exists`), coordinate `ĉ` a `b_ĉ`-adic radical inverse with digit map `π`, every other coordinate `b_c`-adic,
`g, g̃, g'` as in `lem:carrypair`, `R ∣ b^ν - 1` (`ν ≥ 1`), `b^ν ∣ Θ^k - 1`, `η + ν = (E/e)(k + 1)`. For
`Q = p^w` put `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}`, `L_Q = Q E (k+1)`, `m_Q = Q (s E (k+1) - (s-1) E)`. Then the
indices `ι(V_1)`, `ι(V_1 + D_Q)` of `lem:carrypair` (with `(η, λ) = (Qη, Q(η+ν))`) are `< p^{m_Q}` and
distinct, and the two points are at Euclidean distance `< √(s+3) p^{-L_Q}`. -/
theorem nonqu_pair (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    polyIdx p (nonquV1 b ch gt g' ν η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) <
        p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdx p (nonquV1 b ch gt g' ν η (p ^ w)) ≠
        polyIdx p (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) ∧
      euclDist (linPt p Y (polyIdx p (nonquV1 b ch gt g' ν η (p ^ w))))
        (linPt p Y (polyIdx p (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)))) <
        Real.sqrt (s + 3) / (p : ℝ) ^ (p ^ w * lcmDeg b * (k + 1)) := by
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
  /- (i): Frobenius on `Θ^k = 1 + b^ν H` -/
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
  /- (ii): `Θ^Q ∣ S_{Qν}`, so `Θ^{Q(k+1)} ∣ D_Q` -/
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
  /- (iii): the degree -/
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
    rw [nonqu_m_eq s E k (by omega)]
    obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    obtain ⟨n', hn'⟩ : ∃ n', p ^ w * ν = n' + 1 := ⟨p ^ w * ν - 1, by omega⟩
    have h2 : e * (p ^ w * η) + e * (p ^ w * ν) = p ^ w * E * (k + 1) := by rw [← hlam]; ring
    rw [hn', Nat.add_sub_cancel] at h1
    rw [hn', he'] at h2
    rw [he'] at h1 hg
    have h3 : p ^ w * k * ((s - 1) * E) = p ^ w * ((s - 1) * E * k) := by ring
    rw [mul_add]
    nlinarith
  have hηl : p ^ w * η < p ^ w * (η + ν) := by rw [mul_add]; omega
  have key := carrypair hs Y hY b hdeg ch hbad π hrad g gt g' hg hgt hg' hπg hπgt hπg' D hD0
    (p ^ w * η) (p ^ w * (η + ν)) _ hηl hi hii hdegD
  rw [← hlam]
  exact key

/-! ## The covering radius from below (pigeonhole) -/

omit [Fact p.Prime] in
lemma rpow_neg_inv_pow {y : ℝ} (hy : 0 ≤ y) (hs : s ≠ 0) : (y ^ (-(1 : ℝ) / s)) ^ s = y⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy, show -(1 : ℝ) / s * s = -1 by field_simp,
    Real.rpow_neg_one]

lemma linPt_mem (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (n : ℕ) (c : Fin s) :
    0 ≤ linPt p Y n c ∧ linPt p Y n c ≤ 1 := by
  obtain ⟨τ, h0, h1, -, he⟩ := tsum_split (Fact.out : p.Prime).two_le
    (fun j => (Y c (idxPolyP p n) j).val) (fun _ => ZMod.val_lt _) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, div_one] at he h1
  unfold linPt; rw [he]; exact ⟨h0, h1⟩

omit [Fact p.Prime] in
/-- Pigeonhole lower bound for the covering radius: if `N < M^s`, some cell of the grid of side `1/M` contains
none of the first `N` points, and its centre is at distance `≥ 1/(2M)` from all of them. -/
theorem covRadIdx_ge (pt : ℕ → Fin s → ℝ) (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : N < M ^ s) : 1 / (2 * (M : ℝ)) ≤ covRadIdx pt N := by
  classical
  set cell : ℕ → Fin s → ℕ := fun v c => min ⌊(M : ℝ) * pt v c⌋₊ (M - 1) with hcell
  have hcard : ((range N).image cell).card < (Fintype.piFinset fun _ : Fin s => range M).card := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_image_le (by rw [Finset.card_range]; exact hNM)
  obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hkM : ∀ c, k c < M := fun c => Finset.mem_range.mp (Fintype.mem_piFinset.mp hk c)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set x : Fin s → ℝ := fun c => ((k c : ℝ) + 1 / 2) / M with hxdef
  have hx : ∀ c, x c ∈ Set.Icc (0 : ℝ) 1 := by
    intro c
    have h1 : (k c : ℝ) + 1 ≤ M := by exact_mod_cast hkM c
    constructor
    · positivity
    · rw [hxdef, div_le_one hMpos]; linarith
  have hfar : ∀ v, v < N → 1 / (2 * (M : ℝ)) ≤ euclDist x (pt v) := by
    intro v hv
    have hne : cell v ≠ k := fun h => hkn (Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, h⟩)
    obtain ⟨c, hc⟩ : ∃ c, cell v c ≠ k c := Function.ne_iff.mp hne
    set t := (M : ℝ) * pt v c with htdef
    have ht0 : 0 ≤ t := mul_nonneg hMpos.le (hpt v c).1
    have htM : t ≤ M := by have := (hpt v c).2; nlinarith
    have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have hfl' : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have hhalf : (1 : ℝ) / 2 ≤ |(k c : ℝ) + 1 / 2 - t| := by
      rcases le_or_gt ⌊t⌋₊ (M - 1) with hle | hgt
      · have hcv : cell v c = ⌊t⌋₊ := min_eq_left hle
        rw [hcv] at hc
        rcases lt_or_gt_of_ne hc with h1 | h1
        · have : (⌊t⌋₊ : ℝ) + 1 ≤ (k c : ℝ) := by exact_mod_cast h1
          rw [le_abs]; left; linarith
        · have : (k c : ℝ) + 1 ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
          rw [abs_sub_comm, le_abs]; left; linarith
      · have hcv : cell v c = M - 1 := min_eq_right hgt.le
        rw [hcv] at hc
        have h1 : k c + 2 ≤ M := by have := hkM c; omega
        have h2 : M ≤ ⌊t⌋₊ := by omega
        have h1' : (k c : ℝ) + 2 ≤ M := by exact_mod_cast h1
        have h2' : (M : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast h2
        rw [abs_sub_comm, le_abs]; left; linarith
    have hcoord : 1 / (2 * (M : ℝ)) ≤ |x c - pt v c| := by
      have : x c - pt v c = ((k c : ℝ) + 1 / 2 - t) / M := by
        rw [hxdef, htdef]; field_simp
      rw [this, abs_div, abs_of_pos hMpos, le_div_iff₀ hMpos]
      calc 1 / (2 * (M : ℝ)) * M = 1 / 2 := by field_simp
        _ ≤ _ := hhalf
    refine hcoord.trans ?_
    unfold euclDist
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun c => (x c - pt v c) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c))
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hinner : 1 / (2 * (M : ℝ)) ≤ ⨅ v : Fin N, euclDist x (pt v) := le_ciInf fun v => hfar v v.2
  have hbdd : BddAbove (Set.range fun x : {x : Fin s → ℝ // ∀ c, x c ∈ Set.Icc (0 : ℝ) 1} =>
      ⨅ v : Fin N, euclDist x.1 (pt v)) := by
    refine ⟨Real.sqrt s, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hb : BddBelow (Set.range fun v : Fin N => euclDist z.1 (pt v)) :=
      ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
    refine (ciInf_le hb ⟨0, hN⟩).trans ?_
    unfold euclDist
    refine Real.sqrt_le_sqrt ?_
    calc ∑ c, (z.1 c - pt 0 c) ^ 2 ≤ ∑ _c : Fin s, (1 : ℝ) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have := z.2 c; have := hpt 0 c
          simp only [Set.mem_Icc] at *
          nlinarith
      _ = s := by simp
  exact hinner.trans (le_ciSup hbdd ⟨x, hx⟩)

omit [Fact p.Prime] in
/-- `h(P_m) ≥ p^{-m/s}/(2p)` (grid of side `p^{-(⌊m/s⌋+1)}`). -/
theorem covRadIdx_ge_pow (hp : 2 ≤ p) (hs : 1 ≤ s) (pt : ℕ → Fin s → ℝ)
    (hpt : ∀ v c, 0 ≤ pt v c ∧ pt v c ≤ 1) (m : ℕ) :
    ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) / (2 * p) ≤ covRadIdx pt (p ^ m) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hNM : p ^ m < (p ^ (m / s + 1)) ^ s := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) (by rw [mul_comm]; exact Nat.lt_mul_div_succ m (by omega))
  have h := covRadIdx_ge pt hpt (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (by omega)) hNM
  refine le_trans ?_ h
  set a := ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  have hale : a ≤ 1 / (p : ℝ) ^ (m / s) := by
    refine le_of_pow_le_pow_left₀ (n := s) (by omega) (by positivity) ?_
    rw [ha, rpow_neg_inv_pow (by positivity) (by omega), div_pow, one_pow, ← pow_mul, one_div]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ p)) (Nat.div_mul_le_self m s)
  push_cast
  rw [pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
  calc a * (2 * ((p : ℝ) ^ (m / s) * p)) = 2 * p * (a * (p : ℝ) ^ (m / s)) := by ring
    _ ≤ 2 * p * (1 / (p : ℝ) ^ (m / s) * (p : ℝ) ^ (m / s)) := by gcongr
    _ = 1 * (2 * p) := by field_simp

/-! ## `thm:nonqu` -/

/-- **`thm:nonqu`** (prime `q = p`). Let `s ≥ 2`, let the bases `b_0, …, b_{s-1} ∈ 𝔽_p[z]` be pairwise coprime
of degrees `≥ 1`, coordinate `ĉ` a `b_ĉ`-adic radical inverse, and every other coordinate `b_c`-adic. Then for
every `ε > 0` some prefix `P_m` contains two points at Euclidean distance `< ε p^{-m/s}` (the explicit pairs of
`nonqu_pair`), and the sequence is not quasi-uniform. -/
theorem nonqu (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
        euclDist (linPt p Y v) (linPt p Y w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPt p Y) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have he1 := hdeg ch
  obtain ⟨g, hg, hπg⟩ := hrad.1 fun _ => 1
  obtain ⟨gt, hgt, hπgt⟩ := hrad.1 fun i => if i = 0 then 0 else -1
  obtain ⟨g', hg', hπg'⟩ := hrad.1 fun _ => -1
  obtain ⟨ν, k, η, hν, -, hR, hΘ, hη⟩ := nonqu_exists b hdeg hcop ch
  set E := lcmDeg b with hE
  have hE1 : 1 ≤ E := lcmDeg_pos b hdeg
  have hs0 : s ≠ 0 := by omega
  have hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < p ^ m ∧ w < p ^ m ∧ v ≠ w ∧
      euclDist (linPt p Y v) (linPt p Y w) < ε * ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
    intro ε hε
    set K := Real.sqrt (s + 3) ^ s with hK
    obtain ⟨w, hw⟩ := exists_nat_gt (K / ε ^ s)
    have hQw : (w : ℝ) < (p ^ w : ℕ) := by exact_mod_cast Nat.lt_pow_self hp.one_lt
    set Q := p ^ w with hQ
    set L := Q * E * (k + 1) with hL
    set m := Q * (s * E * (k + 1) - (s - 1) * E) with hm
    obtain ⟨h1, h2, h3, h4⟩ := nonqu_pair hs Y hY b hdeg ch hbad π hrad g gt g' hg hgt hg' hπg hπgt hπg'
      ν k η hν hR hΘ hη w
    refine ⟨m, _, _, h1, h2, h3, h4.trans_le ?_⟩
    set a := ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
    have ha0 : 0 ≤ a := Real.rpow_nonneg (by positivity) _
    refine le_of_pow_le_pow_left₀ hs0 (by positivity) ?_
    have hexc : (p : ℝ) ^ (s * L) = (p : ℝ) ^ m * (p : ℝ) ^ (Q * ((s - 1) * E)) := by
      rw [← pow_add]; congr 1; exact nonqu_excess s E k Q (by omega)
    have hX : (Q : ℝ) ≤ (p : ℝ) ^ (Q * ((s - 1) * E)) := by
      have h5 : Q < p ^ Q := Nat.lt_pow_self hp.one_lt
      have h6 : p ^ Q ≤ p ^ (Q * ((s - 1) * E)) :=
        Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hE1))
      exact_mod_cast (h5.trans_le h6).le
    have hKQ : K < ε ^ s * Q := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ s)).mp (hw.trans hQw)
      linarith
    rw [div_pow, mul_pow, ha, rpow_neg_inv_pow (by positivity) hs0, ← pow_mul, mul_comm L s, hexc,
      div_le_iff₀ (by positivity)]
    rw [← hK]
    calc K ≤ ε ^ s * (p : ℝ) ^ (Q * ((s - 1) * E)) := by
          nlinarith [pow_pos hε s]
      _ = ε ^ s * ((p : ℝ) ^ m)⁻¹ * ((p : ℝ) ^ m * (p : ℝ) ^ (Q * ((s - 1) * E))) := by
          field_simp
  refine ⟨hclose, ?_⟩
  rintro ⟨B, hB⟩
  set ε := 1 / (2 * p * (|B| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨m, v, w, hv, hw, hvw, hd⟩ := hclose ε hε
  have hN : 2 ≤ p ^ m := by omega
  have hcov := covRadIdx_ge_pow hp2 (by omega) (linPt p Y) (fun v c => linPt_mem Y v c) m
  have hsep := sepDistIdx_le_pair (linPt p Y) hv hw hvw
  have hsep0 := sepDistIdx_nonneg (linPt p Y) (p ^ m)
  set a := ((p : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have h1 := hB _ hN
  have h2 : B * sepDistIdx (linPt p Y) (p ^ m) ≤ |B| * (ε * a) :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) hsep0).trans
      (mul_le_mul_of_nonneg_left (hsep.trans hd.le) (abs_nonneg B))
  have h3 : |B| * (ε * a) < a / (2 * p) := by
    rw [hεdef]
    have hB0 : 0 ≤ |B| := abs_nonneg B
    rw [show |B| * (1 / (2 * p * (|B| + 1)) * a) = (|B| / (|B| + 1)) * (a / (2 * p)) by
      field_simp]
    have : |B| / (|B| + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have hpos : 0 < a / (2 * p) := by positivity
    nlinarith
  linarith

/-- `thm:nonqu`, the normalized separations along the levels `m_Q`: with `X_Q = Q (s-1) E`,
`sep(P_{m_Q}) = δ(P_{m_Q}) p^{m_Q/s} < √(s+3) p^{-X_Q/s}`, and for `K_Q = ⌈m_Q/s⌉` the full level `P_{s K_Q}`:
`sep(P_{s K_Q}) = δ(P_{s K_Q}) p^{K_Q} < √(s+3) p^{1 - X_Q/s}`. -/
theorem nonqu_sep (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    sepDistIdx (linPt p Y) (p ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b))) *
        ((p : ℝ) ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b))) ^ ((1 : ℝ) / s) <
        Real.sqrt (s + 3) * (p : ℝ) ^ (-((p ^ w * ((s - 1) * lcmDeg b) : ℕ) : ℝ) / s) ∧
      sepDistIdx (linPt p Y)
          (p ^ (s * ((p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) + s - 1) / s))) *
        (p : ℝ) ^ ((p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) + s - 1) / s) <
        Real.sqrt (s + 3) * (p : ℝ) ^ (1 - ((p ^ w * ((s - 1) * lcmDeg b) : ℕ) : ℝ) / s) := by
  have hp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  obtain ⟨h1, h2, h3, h4⟩ := nonqu_pair hs Y hY b hdeg ch hbad π hrad g gt g' hg hgt hg' hπg hπgt hπg'
    ν k η hν hR hΘ hη w
  set m := p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b) with hm
  set L := p ^ w * lcmDeg b * (k + 1) with hL
  set Xq := p ^ w * ((s - 1) * lcmDeg b) with hX
  set K := (m + s - 1) / s with hK
  have hexc : s * L = m + Xq := nonqu_excess s (lcmDeg b) k (p ^ w) (by omega)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hLr : (L : ℝ) = ((m : ℝ) + Xq) / s := by
    rw [eq_div_iff hs0.ne']; exact_mod_cast (by rw [mul_comm]; exact hexc)
  have hsep : sepDistIdx (linPt p Y) (p ^ m) < Real.sqrt (s + 3) / (p : ℝ) ^ L :=
    (sepDistIdx_le_pair _ h1 h2 h3).trans_lt h4
  have hpL : 1 / (p : ℝ) ^ L = (p : ℝ) ^ (-(L : ℝ)) := by
    rw [Real.rpow_neg hp0.le, Real.rpow_natCast, one_div]
  have hmr : ((p : ℝ) ^ m) ^ ((1 : ℝ) / s) = (p : ℝ) ^ ((m : ℝ) / s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; ring_nf
  constructor
  · rw [hmr]
    calc sepDistIdx (linPt p Y) (p ^ m) * (p : ℝ) ^ ((m : ℝ) / s)
        < Real.sqrt (s + 3) / (p : ℝ) ^ L * (p : ℝ) ^ ((m : ℝ) / s) :=
          mul_lt_mul_of_pos_right hsep (by positivity)
      _ = Real.sqrt (s + 3) * ((p : ℝ) ^ (-(L : ℝ)) * (p : ℝ) ^ ((m : ℝ) / s)) := by
          rw [← hpL]; ring
      _ = _ := by
          rw [← Real.rpow_add hp0, hLr]; congr 2; field_simp; ring
  · have hmK : m ≤ s * K := by
      rw [hK]
      have := Nat.div_add_mod (m + s - 1) s
      have := Nat.mod_lt (m + s - 1) (by omega : 0 < s)
      omega
    have hKr : (K : ℝ) ≤ (m : ℝ) / s + 1 := by
      have h5 : K * s ≤ m + s - 1 := Nat.div_mul_le_self _ _
      have h6 : (K : ℝ) * s ≤ m + s := by exact_mod_cast (by omega : K * s ≤ m + s)
      rw [div_add_one hs0.ne', le_div_iff₀ hs0]; exact h6
    have hsepK : sepDistIdx (linPt p Y) (p ^ (s * K)) < Real.sqrt (s + 3) / (p : ℝ) ^ L := by
      refine (sepDistIdx_le_pair _ (h1.trans_le ?_) (h2.trans_le ?_) h3).trans_lt h4 <;>
        exact Nat.pow_le_pow_right hp.pos hmK
    calc sepDistIdx (linPt p Y) (p ^ (s * K)) * (p : ℝ) ^ K
        < Real.sqrt (s + 3) / (p : ℝ) ^ L * (p : ℝ) ^ K := mul_lt_mul_of_pos_right hsepK (by positivity)
      _ = Real.sqrt (s + 3) * (p : ℝ) ^ ((K : ℝ) - L) := by
          rw [Real.rpow_sub hp0, Real.rpow_natCast, Real.rpow_natCast]; ring
      _ ≤ Real.sqrt (s + 3) * (p : ℝ) ^ (1 - (Xq : ℝ) / s) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 ?_) (Real.sqrt_nonneg _)
          rw [hLr]
          have : (m : ℝ) / s + 1 - ((m : ℝ) + Xq) / s = 1 - (Xq : ℝ) / s := by field_simp; ring
          linarith

end GeoSeq
