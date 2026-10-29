/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V10_3Defs
public import GeoSeq.V93Thm
public import GeoSeq.V95Gen
public import GeoSeq.V95Nied

@[expose] public section

/-!
# GeoSeq stage V10-3: `sec:fail` over `𝔽_q` with a general digit code

The V9-3/V9-5 proofs are for prime `q = p` (`enc = val`). Here the same statements are proved over every finite
field `F` of characteristic `p` with `q` elements read through ANY digit code `D` that has a carry pair
(`IsCarryPair D ȳ y°`: `enc ȳ = q - 1`, `enc(y° - ȳ) = enc y° + 1`, the content of `eq:carrydigit`):

* index polynomials over `F` (`idxPolyD_polyIdxD`, `polyIdxD_lt`, `polyIdxD_injective`);
* **`carrypairD`** (`lem:carrypair`), **`nonqu_pairD`**, **`nonqu_code`** (`thm:nonqu`: close pairs at every scale, not
  quasi-uniform), the Frobenius step with `Q = p^w` (`CharP F p`);
* **`carryPair_pb`**: the power-basis code of every model `PF p d fc` has the carry pair
  `ȳ = enc⁻¹(q - 1)`, `y° = enc⁻¹(q/p - 1)` (`eq:carrydigit` for the natural identification);
* the corollaries over `𝔽_q`: **`unscrambledD`**, **`unscrambled_frameD`** (`cor:unscrambled`; with `μ = β = 1`,
  `L = I` it is **`faure_code`**, `cor:faure` for prime powers), **`niedGen_not_quD`**, **`nied_not_quD`** (`cor:nied`
  for prime powers).
-/

namespace GeoSeq

open Finset Polynomial

/-! ## Index polynomials over `F` -/

section Idx
variable {F : Type*} [Field F] {q : ℕ} [NeZero q]

/-- The coefficients of the index polynomial are the index digits. -/
theorem coeff_idxPolyD (D : DigitCode F q) (n k : ℕ) :
    (idxPolyD D n).coeff k = if k < n + 1 then idxDigit D n k else 0 := by
  unfold idxPolyD
  rw [finsetSum_coeff]
  simp_rw [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

/-- `deg idxPolyD D n ≤ n`. -/
theorem natDegree_idxPolyD (D : DigitCode F q) (n : ℕ) : (idxPolyD D n).natDegree ≤ n := by
  unfold idxPolyD
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => (natDegree_monomial_le _).trans ?_
  have := Finset.mem_range.mp hk; omega

/-- The base-`q` digits of `ι(V)` are the codes of the coefficients of `V`. -/
theorem polyIdxD_digit (D : DigitCode F q) (V : F[X]) (k : ℕ) :
    polyIdxD D V / q ^ k % q = if k < V.natDegree + 1 then (D.enc (V.coeff k) : ℕ) else 0 :=
  natDigits_sum (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) _ (fun j => (D.enc (V.coeff j) : ℕ))
    (fun _ => (D.enc _).isLt) k

omit [NeZero q] in
/-- `enc x = 0 ↔ x = 0`. -/
theorem enc_eq_zero_iff (D : DigitCode F q) (x : F) : (D.enc x : ℕ) = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact D.enc.injective (Fin.ext (by rw [h, D.enc_zero]))
  · rintro rfl; exact D.enc_zero

/-- `idxPolyD D (ι(V)) = V`. -/
theorem idxPolyD_polyIdxD (D : DigitCode F q) (hq : 2 ≤ q) (V : F[X]) : idxPolyD D (polyIdxD D V) = V := by
  ext k
  rw [coeff_idxPolyD]
  have hdig := polyIdxD_digit D V k
  by_cases hk : k < polyIdxD D V + 1
  · rw [if_pos hk, idxDigit]
    by_cases hd : k < V.natDegree + 1
    · rw [if_pos hd] at hdig
      have e : (⟨polyIdxD D V / q ^ k % q, Nat.mod_lt _ (NeZero.pos q)⟩ : Fin q) = D.enc (V.coeff k) :=
        Fin.ext hdig
      rw [e, Equiv.symm_apply_apply]
    · rw [if_neg hd] at hdig
      rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      have e : (⟨polyIdxD D V / q ^ k % q, Nat.mod_lt _ (NeZero.pos q)⟩ : Fin q) = D.enc 0 := by
        apply Fin.ext
        show polyIdxD D V / q ^ k % q = (D.enc 0 : ℕ)
        rw [hdig, D.enc_zero]
      rw [e, Equiv.symm_apply_apply]
  · rw [if_neg hk]
    have hlt : polyIdxD D V < q ^ k := lt_of_lt_of_le (by omega) (Nat.lt_pow_self (by omega : 1 < q)).le
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod] at hdig
    by_cases hd : k < V.natDegree + 1
    · rw [if_pos hd] at hdig
      exact ((enc_eq_zero_iff D _).mp hdig.symm).symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem polyIdxD_lt (D : DigitCode F q) (V : F[X]) {m : ℕ} (hV : V.natDegree < m) : polyIdxD D V < q ^ m :=
  lt_of_lt_of_le (natSum_lt (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) _ _ (fun j => (D.enc _).isLt))
    (Nat.pow_le_pow_right (NeZero.pos q) (by omega))

theorem polyIdxD_injective (D : DigitCode F q) (hq : 2 ≤ q) : Function.Injective (polyIdxD D) := fun V W h => by
  rw [← idxPolyD_polyIdxD D hq V, ← idxPolyD_polyIdxD D hq W, h]

/-- The point with index `ι(V)` reads the digits of `Y_c(V)`. -/
theorem linPtD_polyIdxD {s : ℕ} (D : DigitCode F q) (hq : 2 ≤ q) (Y : Fin s → F[X] → ℕ → F) (V : F[X])
    (c : Fin s) :
    linPtD D Y (polyIdxD D V) c = ∑' j : ℕ, ((D.enc (Y c V j) : ℕ) : ℝ) / (q : ℝ) ^ (j + 1) := by
  simp only [linPtD, idxPolyD_polyIdxD D hq]

/-- The coordinates of the points lie in `[0, 1]`. -/
theorem linPtD_mem {s : ℕ} (D : DigitCode F q) (hq : 2 ≤ q) (Y : Fin s → F[X] → ℕ → F) (n : ℕ) (c : Fin s) :
    0 ≤ linPtD D Y n c ∧ linPtD D Y n c ≤ 1 := by
  obtain ⟨τ, h0, h1, -, he⟩ := tsum_split hq (fun j => (D.enc (Y c (idxPolyD D n) j) : ℕ))
    (fun _ => (D.enc _).isLt) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, div_one] at he h1
  unfold linPtD; rw [he]; exact ⟨h0, h1⟩

end Idx

/-! ## `lem:carrypair` over `𝔽_q` -/

section Carry
variable {F : Type*} [Field F] {q s : ℕ} [NeZero q]

/-- **`lem:carrypair`** over `𝔽_q` with a general digit code `D` (`q ≥ 2`) having a carry pair `(ȳ, y°)`
(`eq:carrydigit`). Coordinate `ĉ` is a `b`-adic radical inverse with digit map `π`, every other coordinate `c` is
`b_c`-adic; `deg g, deg g̃, deg g' < e` with `π(g) = -ȳ(1, …, 1)`, `π(g̃) = (y°, ȳ, …, ȳ)`, `π(g') = ȳ(1, …, 1)`;
`D ≠ 0`, `η < λ`, (i) `D ≡ g b^η S_{λ-η} (mod b^λ)`, (ii) `b_c^{j_c} ∣ D` with `e_c j_c ≥ L = eλ`, (iii) `deg D < m`.
Then the indices `ι(V_1)`, `ι(V_1 + D)` are `< q^m`, distinct, and the points are at distance `< √(s+3) q^{-L}`. -/
theorem carrypairD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : F[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = -yb)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then yo else yb)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = yb)
    (D : F[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    polyIdxD Dc (carryV1 (b ch) gt g' η l) < q ^ m ∧
      polyIdxD Dc (carryV1 (b ch) gt g' η l + D) < q ^ m ∧
      polyIdxD Dc (carryV1 (b ch) gt g' η l) ≠ polyIdxD Dc (carryV1 (b ch) gt g' η l + D) ∧
      euclDist (linPtD Dc Y (polyIdxD Dc (carryV1 (b ch) gt g' η l)))
        (linPtD Dc Y (polyIdxD Dc (carryV1 (b ch) gt g' η l + D))) <
        Real.sqrt (s + 3) / (q : ℝ) ^ ((b ch).natDegree * l) := by
  have he1 : 1 ≤ (b ch).natDegree := hdeg ch
  set B := b ch with hB
  set e := B.natDegree with he
  set V1 := carryV1 B gt g' η l with hV1
  set L := e * l with hL
  /- degrees -/
  have hdegV1 : V1.natDegree < L := by
    have t1 : (gt * B ^ η).natDegree < L := by
      have : (gt * B ^ η).natDegree ≤ gt.natDegree + η * e :=
        natDegree_mul_le.trans (Nat.add_le_add_left natDegree_pow_le _)
      have h2 : (η + 1) * e ≤ l * e := Nat.mul_le_mul_right _ hηl
      rw [hL]; nlinarith
    have t2 : (g' * B ^ (η + 1) * runS B (l - η - 1)).natDegree < L := by
      rcases Nat.eq_zero_or_pos (l - η - 1) with h0 | h0
      · rw [h0, runS_zero, mul_zero, natDegree_zero, hL]; exact Nat.mul_pos (by omega) (by omega)
      · obtain ⟨r, hr⟩ : ∃ r, l = η + 2 + r := ⟨l - η - 2, by omega⟩
        have h3 : (g' * B ^ (η + 1) * runS B (l - η - 1)).natDegree ≤
            (g'.natDegree + (η + 1) * e) + e * (l - η - 1 - 1) :=
          natDegree_mul_le.trans (Nat.add_le_add (natDegree_mul_le.trans
            (Nat.add_le_add_left natDegree_pow_le _)) (natDegree_runS _ _))
        rw [show l - η - 1 - 1 = r by omega] at h3
        refine lt_of_le_of_lt h3 ?_
        rw [hL, hr]; nlinarith
    exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt t1 t2)
  have : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs
  obtain ⟨c0, hc0⟩ := exists_ne ch
  obtain ⟨j0, hj0, hdj0⟩ := hii c0 hc0
  have hLD : L ≤ D.natDegree := by
    have h := natDegree_le_of_dvd hdj0 hD
    rw [natDegree_pow] at h
    exact hj0.trans (by rw [mul_comm]; exact h)
  have hV1m : V1.natDegree < m := by omega
  have hdegV2 : (V1 + D).natDegree < m :=
    lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hV1m hiii)
  have hne : V1 ≠ V1 + D := fun h => hD (left_eq_add.mp h)
  refine ⟨polyIdxD_lt Dc _ hV1m, polyIdxD_lt Dc _ hdegV2, fun h => hne (polyIdxD_injective Dc hq h), ?_⟩
  /- the other coordinates share `L` digits -/
  have hother : ∀ c, c ≠ ch → |linPtD Dc Y (polyIdxD Dc V1) c - linPtD Dc Y (polyIdxD Dc (V1 + D)) c| ≤
      1 / (q : ℝ) ^ L := by
    intro c hc
    rw [linPtD_polyIdxD Dc hq, linPtD_polyIdxD Dc hq]
    refine real_prefix hq _ _ (fun _ => (Dc.enc _).isLt) (fun _ => (Dc.enc _).isLt) L fun j hj => ?_
    obtain ⟨jc, hjc, hdc⟩ := hii c hc
    rw [hY c V1 D j, hbad c hc jc D hdc j (lt_of_lt_of_le hj hjc), add_zero]
  /- the digits of coordinate `ĉ` -/
  have hpi0 : ∀ i, i < e → π 0 i = 0 := fun i hi => hrad.pi_zero (hY ch) hi
  have hV1f : V1 = B ^ η * (gt + B * (g' * runS B (l - η - 1))) := by
    rw [hV1, carryV1]; ring
  have hdigV1 : ∀ Q i, i < e →
      Y ch V1 (Q * e + i) = if Q * e + i < e * η then 0 else if Q * e + i = e * η then yo else
        if Q * e + i < L then yb else 0 := by
    intro Q i hie
    rw [hrad.2 V1 Q i hie, hV1f, badicDigit_pow_mul he1]
    rcases lt_trichotomy Q η with hQ | hQ | hQ
    · rw [if_pos hQ, hpi0 i hie, if_pos]
      have : (Q + 1) * e ≤ η * e := Nat.mul_le_mul_right _ hQ
      nlinarith
    · subst hQ
      rw [if_neg (lt_irrefl _), Nat.sub_self, badicDigit_base hgt, hπgt i hie]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; rw [if_pos rfl, if_neg (by rw [mul_comm]; omega), if_pos (by rw [mul_comm]; omega)]
      · rw [if_neg (by omega), if_neg (by rw [mul_comm]; omega), if_neg (by rw [mul_comm]; omega)]
        have h2 : (Q + 1) * e ≤ l * e := Nat.mul_le_mul_right _ hηl
        rw [if_pos (by rw [hL]; nlinarith)]
    · obtain ⟨t, ht⟩ : ∃ t, Q - η = t + 1 := ⟨Q - η - 1, by omega⟩
      rw [if_neg (by omega), ht, badicDigit_succ hgt, badicDigit_run hg']
      have h1 : (η + 1) * e ≤ Q * e := Nat.mul_le_mul_right _ hQ
      rw [if_neg (show ¬ Q * e + i < e * η by nlinarith), if_neg (show Q * e + i ≠ e * η by intro h; nlinarith)]
      by_cases hQl : Q < l
      · rw [if_pos (show t < l - η - 1 by omega), hπg' i hie]
        have h2 : (Q + 1) * e ≤ l * e := Nat.mul_le_mul_right _ hQl
        rw [if_pos (by rw [hL]; nlinarith)]
      · rw [if_neg (show ¬ t < l - η - 1 by omega), hpi0 i hie]
        have h2 : l * e ≤ Q * e := Nat.mul_le_mul_right _ (by omega)
        have h3 : ¬ Q * e + i < L := not_lt.mpr (le_trans (by rw [hL, mul_comm]; exact h2) (Nat.le_add_right _ _))
        rw [if_neg h3]
  have hdigV1' : ∀ n, Y ch V1 n = if n < e * η then 0 else if n = e * η then yo else
      if n < L then yb else 0 := by
    intro n
    have h := hdigV1 (n / e) (n % e) (Nat.mod_lt _ he1)
    rwa [Nat.div_add_mod' n e] at h
  have hgf : g * B ^ η * runS B (l - η) = B ^ η * (g * runS B (l - η)) := by ring
  have hdigD' : ∀ n, n < L → Y ch D n = if n < e * η then 0 else -yb := by
    intro n hn
    have hn' := Nat.div_add_mod' n e
    have hQl : n / e < l := (Nat.div_lt_iff_lt_mul he1).mpr (by rw [hL] at hn; linarith)
    rw [← hn', hrad.2 D (n / e) (n % e) (Nat.mod_lt _ he1), badicDigit_congr he1 hi hQl, hgf,
      badicDigit_pow_mul he1, hn']
    by_cases hQ : n / e < η
    · rw [if_pos hQ, hpi0 _ (Nat.mod_lt _ he1),
        if_pos (by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul he1).mp hQ)]
    · rw [if_neg hQ, badicDigit_run hg, if_pos (by omega), hπg _ (Nat.mod_lt _ he1),
        if_neg (by rw [mul_comm]; intro h; exact hQ ((Nat.div_lt_iff_lt_mul he1).mpr h))]
  have hdigV2 : ∀ n, Y ch (V1 + D) n = Y ch V1 n + Y ch D n := fun n => hY ch V1 D n
  have hkL : e * η < L := by rw [hL]; exact Nat.mul_lt_mul_of_pos_left hηl he1
  have h00 : (Dc.enc (0 : F) : ℕ) = 0 := Dc.enc_zero
  have hch : |linPtD Dc Y (polyIdxD Dc (V1 + D)) ch - linPtD Dc Y (polyIdxD Dc V1) ch| <
      2 / (q : ℝ) ^ L := by
    rw [linPtD_polyIdxD Dc hq, linPtD_polyIdxD Dc hq]
    refine real_carry hq _ _ (fun _ => (Dc.enc _).isLt) (fun _ => (Dc.enc _).isLt) hkL ?_ ?_ ?_ ?_
    · intro j hj
      rw [hdigV2, hdigD' j (by omega), if_pos hj, add_zero]
    · rw [hdigV2, hdigD' _ hkL, hdigV1', if_neg (lt_irrefl _), if_pos rfl, if_neg (lt_irrefl _),
        ← sub_eq_add_neg]
      exact hcp.2
    · intro j hj1 hj2
      rw [hdigV2, hdigD' j hj2, hdigV1', if_neg (by omega), if_neg (by omega), if_pos hj2,
        if_neg (by omega), add_neg_cancel, h00]
      exact ⟨hcp.1, rfl⟩
    · refine ⟨e * ((V1 + D).natDegree + 1 + L),
        le_trans (by omega) (Nat.le_mul_of_pos_left _ he1), ?_⟩
      rw [IsRadInv.digit_high he1 (hY ch) hrad, h00]; omega
  /- the distance -/
  set x := linPtD Dc Y (polyIdxD Dc V1)
  set y := linPtD Dc Y (polyIdxD Dc (V1 + D))
  have hpL : (0 : ℝ) < 1 / (q : ℝ) ^ L := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hsq_ch : (x ch - y ch) ^ 2 < 4 * (1 / (q : ℝ) ^ L) ^ 2 := by
    have h := hch
    rw [abs_sub_comm] at h
    have h2 : (2 : ℝ) / (q : ℝ) ^ L = 2 * (1 / (q : ℝ) ^ L) := by ring
    rw [h2] at h
    have := sq_lt_sq' (abs_lt.mp h).1 (abs_lt.mp h).2
    nlinarith
  have hsq_o : ∑ c ∈ univ.erase ch, (x c - y c) ^ 2 ≤ ((s : ℝ) - 1) * (1 / (q : ℝ) ^ L) ^ 2 := by
    have h1 : ∀ c ∈ univ.erase ch, (x c - y c) ^ 2 ≤ (1 / (q : ℝ) ^ L) ^ 2 := by
      intro c hc
      have h := hother c (Finset.ne_of_mem_erase hc)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    refine (Finset.sum_le_card_nsmul _ _ _ h1).trans (le_of_eq ?_)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega)]
    simp
  have hsum : ∑ c, (x c - y c) ^ 2 < ((s : ℝ) + 3) * (1 / (q : ℝ) ^ L) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ch)]
    linarith
  unfold euclDist
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrhs : (0 : ℝ) < Real.sqrt (s + 3) / (q : ℝ) ^ L := by positivity
  rw [Real.sqrt_lt' hrhs, div_pow, Real.sq_sqrt (by positivity)]
  calc ∑ c, (x c - y c) ^ 2 < ((s : ℝ) + 3) * (1 / (q : ℝ) ^ L) ^ 2 := hsum
    _ = ((s : ℝ) + 3) / ((q : ℝ) ^ L) ^ 2 := by ring

end Carry

/-! ## `thm:nonqu` over `𝔽_q` -/

section NonQU
variable {F : Type*} [Field F] {s : ℕ}

/-- `thm:nonqu`, existence of `ν` and `k`, over every finite field. -/
theorem nonqu_existsD [Finite F] (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
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

variable {p : ℕ} [Fact p.Prime] [CharP F p] {q : ℕ} [NeZero q]

/-- **`thm:nonqu`** over `𝔽_q` (characteristic `p`, any digit code with a carry pair), the explicit pairs: for
`Q = p^w`, `D_Q = g b^{Qη} S_{Qν} Θ^{Qk}`, the indices `ι(V_1)`, `ι(V_1 + D_Q)` are `< q^{m_Q}`,
`m_Q = Q(sE(k+1) - (s-1)E)`, distinct, and the points are at distance `< √(s+3) q^{-L_Q}`, `L_Q = QE(k+1)`. -/
theorem nonqu_pairD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : F[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = -yb)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then yo else yb)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = yb)
    (ν k η : ℕ) (hν : 1 ≤ ν) (hR : carryR b ch ∣ b ch ^ ν - 1) (hΘ : b ch ^ ν ∣ thetaP b ch ^ k - 1)
    (hη : η + ν = lcmDeg b / (b ch).natDegree * (k + 1)) (w : ℕ) :
    polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w)) <
        q ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) <
        q ^ (p ^ w * (s * lcmDeg b * (k + 1) - (s - 1) * lcmDeg b)) ∧
      polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w)) ≠
        polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)) ∧
      euclDist (linPtD Dc Y (polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w))))
        (linPtD Dc Y (polyIdxD Dc (nonquV1 b ch gt g' ν η (p ^ w) + nonquD b ch g ν k η (p ^ w)))) <
        Real.sqrt (s + 3) / (q : ℝ) ^ (p ^ w * lcmDeg b * (k + 1)) := by
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
  have h1B : (1 : F[X]) - B ≠ 0 := one_sub_ne_zero he1
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
  have hyb : yb ≠ 0 := by
    intro h
    have := hcp.1
    rw [h, Dc.enc_zero] at this
    omega
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h := hπg 0 he1
    rw [hrad.pi_zero (hY ch) he1] at h
    exact hyb (neg_eq_zero.mp h.symm)
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
  have key := carrypairD Dc hq yb yo hcp hs Y hY b hdeg ch hbad π hrad g gt g' hg hgt hg' hπg hπgt hπg' D hD0
    (p ^ w * η) (p ^ w * (η + ν)) _ hηl hi hii hdegD
  rw [← hlam]
  exact key

include p in
/-- **`thm:nonqu`** over `𝔽_q` (every finite field `F` of characteristic `p`, `q ≥ 2` elements read through a digit
code with a carry pair, e.g. the natural identification `carryPair_pb`). Let `s ≥ 2`, the bases `b_c ∈ 𝔽_q[z]`
pairwise coprime of degrees `≥ 1`, coordinate `ĉ` a `b_ĉ`-adic radical inverse, every other coordinate `b_c`-adic.
Then for every `ε > 0` some prefix `P_m` contains two points at distance `< ε q^{-m/s}`, and the sequence is not
quasi-uniform. -/
theorem nonqu_code [Finite F] (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo)
    (hs : 2 ≤ s) (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < q ^ m ∧ w < q ^ m ∧ v ≠ w ∧
        euclDist (linPtD Dc Y v) (linPtD Dc Y w) < ε * ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPtD Dc Y) := by
  have hp : p.Prime := Fact.out
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have he1 := hdeg ch
  obtain ⟨g, hg, hπg⟩ := hrad.1 fun _ => -yb
  obtain ⟨gt, hgt, hπgt⟩ := hrad.1 fun i => if i = 0 then yo else yb
  obtain ⟨g', hg', hπg'⟩ := hrad.1 fun _ => yb
  obtain ⟨ν, k, η, hν, -, hR, hΘ, hη⟩ := nonqu_existsD b hdeg hcop ch
  set E := lcmDeg b with hE
  have hE1 : 1 ≤ E := lcmDeg_pos b hdeg
  have hs0 : s ≠ 0 := by omega
  have hclose : ∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < q ^ m ∧ w < q ^ m ∧ v ≠ w ∧
      euclDist (linPtD Dc Y v) (linPtD Dc Y w) < ε * ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s) := by
    intro ε hε
    set K := Real.sqrt (s + 3) ^ s with hK
    obtain ⟨w, hw⟩ := exists_nat_gt (K / ε ^ s)
    have hQw : (w : ℝ) < (p ^ w : ℕ) := by exact_mod_cast Nat.lt_pow_self hp.one_lt
    set Q := p ^ w with hQ
    set L := Q * E * (k + 1) with hL
    set m := Q * (s * E * (k + 1) - (s - 1) * E) with hm
    obtain ⟨h1, h2, h3, h4⟩ := nonqu_pairD Dc hq yb yo hcp hs Y hY b hdeg ch hbad π hrad g gt g' hg hgt hg'
      hπg hπgt hπg' ν k η hν hR hΘ hη w
    refine ⟨m, _, _, h1, h2, h3, h4.trans_le ?_⟩
    set a := ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
    have ha0 : 0 ≤ a := Real.rpow_nonneg (by positivity) _
    refine le_of_pow_le_pow_left₀ hs0 (by positivity) ?_
    have hexc : (q : ℝ) ^ (s * L) = (q : ℝ) ^ m * (q : ℝ) ^ (Q * ((s - 1) * E)) := by
      rw [← pow_add]; congr 1; exact nonqu_excess s E k Q (by omega)
    have hX : (Q : ℝ) ≤ (q : ℝ) ^ (Q * ((s - 1) * E)) := by
      have h5 : Q < q ^ Q := Nat.lt_pow_self (by omega)
      have h6 : q ^ Q ≤ q ^ (Q * ((s - 1) * E)) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hE1))
      exact_mod_cast (h5.trans_le h6).le
    have hKQ : K < ε ^ s * Q := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ s)).mp (hw.trans hQw)
      linarith
    rw [div_pow, mul_pow, ha, rpow_neg_inv_pow (by positivity) hs0, ← pow_mul, mul_comm L s, hexc,
      div_le_iff₀ (by positivity)]
    rw [← hK]
    calc K ≤ ε ^ s * (q : ℝ) ^ (Q * ((s - 1) * E)) := by
          nlinarith [pow_pos hε s]
      _ = ε ^ s * ((q : ℝ) ^ m)⁻¹ * ((q : ℝ) ^ m * (q : ℝ) ^ (Q * ((s - 1) * E))) := by
          field_simp
  refine ⟨hclose, ?_⟩
  rintro ⟨B, hB⟩
  set ε := 1 / (2 * q * (|B| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨m, v, w, hv, hw, hvw, hd⟩ := hclose ε hε
  have hN : 2 ≤ q ^ m := by omega
  have hcov := covRadIdx_ge_pow hq (by omega) (linPtD Dc Y) (fun v c => linPtD_mem Dc hq Y v c) m
  have hsep := sepDistIdx_le_pair (linPtD Dc Y) hv hw hvw
  have hsep0 := sepDistIdx_nonneg (linPtD Dc Y) (q ^ m)
  set a := ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have h1 := hB _ hN
  have h2 : B * sepDistIdx (linPtD Dc Y) (q ^ m) ≤ |B| * (ε * a) :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) hsep0).trans
      (mul_le_mul_of_nonneg_left (hsep.trans hd.le) (abs_nonneg B))
  have h3 : |B| * (ε * a) < a / (2 * q) := by
    rw [hεdef]
    have hB0 : 0 ≤ |B| := abs_nonneg B
    rw [show |B| * (1 / (2 * q * (|B| + 1)) * a) = (|B| / (|B| + 1)) * (a / (2 * q)) by
      field_simp]
    have : |B| / (|B| + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have hpos : 0 < a / (2 * q) := by positivity
    nlinarith
  linarith

end NonQU

/-! ## `eq:carrydigit` for every natural identification -/

section Nat
variable {F : Type*} [AddCommGroup F] {q : ℕ}

/-- `∑_{i<d} (p-1) p^i + 1 = p^d`. -/
theorem geom_aux (p : ℕ) (hp : 1 ≤ p) (d : ℕ) : (∑ i : Fin d, (p - 1) * p ^ (i : ℕ)) + 1 = p ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [pow_succ]
    nlinarith

/-- `val(-1) = p - 1` in `ℤ/pℤ`. -/
theorem val_neg_one_eq {p : ℕ} [NeZero p] : (-1 : ZMod p).val = p - 1 := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  rw [ZMod.val_neg_one]; omega

/-- **`eq:carrydigit` for every natural identification**: if `enc y = ∑_i φ(y)_i p^i` for an additive bijection
`φ : F ≃+ 𝔽_p^{d+1}` (`p ≥ 2`), then `ȳ = φ⁻¹(-1, …, -1)` has code `p^{d+1} - 1 = q - 1`,
`y° = φ⁻¹(-1, …, -1, 0)` has code `p^d - 1 = q/p - 1`, and `(ȳ, y°)` is a carry pair: `enc(y° - ȳ) = p^d`. -/
theorem carryPair_nat {p : ℕ} [NeZero p] (hp : 2 ≤ p) (D : DigitCode F q) (d : ℕ) (φ : F ≃+ (Fin (d + 1) → ZMod p))
    (hnat : IsNatCode D d φ) :
    (D.enc (φ.symm fun _ => -1) : ℕ) = p ^ (d + 1) - 1 ∧
      (D.enc (φ.symm fun i => if (i : ℕ) = d then 0 else -1) : ℕ) = p ^ d - 1 ∧
      IsCarryPair D (φ.symm fun _ => -1) (φ.symm fun i => if (i : ℕ) = d then 0 else -1) := by
  have hp1 : 1 ≤ p := by omega
  have hq : q = p ^ (d + 1) := by
    have h := Fintype.card_congr (D.enc.symm.trans φ.toEquiv)
    simpa [Fintype.card_fin, ZMod.card] using h
  have e1 : (D.enc (φ.symm fun _ => -1) : ℕ) = p ^ (d + 1) - 1 := by
    rw [hnat, AddEquiv.apply_symm_apply]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans
      (show ∑ i : Fin (d + 1), (p - 1) * p ^ (i : ℕ) = p ^ (d + 1) - 1 by
        have := geom_aux p hp1 (d + 1); omega)
    exact congrArg (· * p ^ (i : ℕ)) val_neg_one_eq
  have e2 : (D.enc (φ.symm fun i => if (i : ℕ) = d then 0 else -1) : ℕ) = p ^ d - 1 := by
    rw [hnat, AddEquiv.apply_symm_apply, Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin d, (if ((Fin.castSucc i : Fin (d + 1)) : ℕ) = d then (0 : ZMod p) else -1).val *
        p ^ ((Fin.castSucc i : Fin (d + 1)) : ℕ) = (p - 1) * p ^ (i : ℕ) := fun i => by
      rw [if_neg (by simp; omega)]
      exact congrArg (· * p ^ (i : ℕ)) val_neg_one_eq
    have h2 : (if ((Fin.last d : Fin (d + 1)) : ℕ) = d then (0 : ZMod p) else -1).val *
        p ^ ((Fin.last d : Fin (d + 1)) : ℕ) = 0 := by
      rw [if_pos (by simp)]; simp
    rw [Finset.sum_congr rfl fun i _ => h1 i, h2, add_zero]
    have := geom_aux p hp1 d
    omega
  refine ⟨e1, e2, by rw [e1, hq], ?_⟩
  have hw : φ ((φ.symm fun i => if (i : ℕ) = d then 0 else -1) - φ.symm fun _ => -1) =
      fun i : Fin (d + 1) => if (i : ℕ) = d then (1 : ZMod p) else 0 := by
    rw [map_sub, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    funext i
    simp only [Pi.sub_apply]
    split_ifs <;> ring
  rw [e2, hnat, hw, Fin.sum_univ_castSucc]
  have hz : ∀ i : Fin d, (i : ℕ) ≠ d := fun i => Nat.ne_of_lt i.isLt
  simp only [Fin.val_castSucc, Fin.val_last, hz, if_false, if_true, ZMod.val_zero, zero_mul,
    Finset.sum_const_zero, ZMod.val_one'' (show p ≠ 1 by omega), one_mul, zero_add]
  have := Nat.one_le_pow d p (by omega)
  omega

/-- The power-basis code of `PF p d fc` is a natural identification (`φ = PF.v`, `PF.vEquiv`). -/
theorem PF.code_isNat {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [Fact p.Prime] [NeZero p] :
    IsNatCode (PF.code : DigitCode (PF p d fc) (p ^ (d + 1))) d PF.vEquiv := fun _ => rfl

/-- **`eq:carrydigit` for the power-basis code** of every model `PF p d fc` (`sec:primepower`):
`ȳ = (-1, …, -1)` (code `q - 1`), `y° = (-1, …, -1, 0)` (code `q/p - 1`) is a carry pair. -/
theorem carryPair_pb {p d : ℕ} {fc : Fin (d + 1) → ZMod p} [Fact p.Prime] [NeZero p] :
    IsCarryPair (PF.code : DigitCode (PF p d fc) (p ^ (d + 1))) ⟨fun _ => -1⟩
      ⟨fun i => if (i : ℕ) = d then 0 else -1⟩ :=
  (carryPair_nat (F := PF p d fc) (Fact.out : p.Prime).two_le PF.code d PF.vEquiv PF.code_isNat).2.2

end Nat

/-! ## The corollaries over `𝔽_q` -/

section Cor
variable {F : Type*} [Field F] {s : ℕ}

/-- The rows of the generator matrices read the index polynomial (any digit code). -/
theorem genY_idxD {q : ℕ} [NeZero q] (Dc : DigitCode F q) (C : Gen s F) (c : Fin s) (v n : ℕ) :
    genY C c (idxPolyD Dc v) n = seqDigit Dc C v c n := by
  unfold genY seqDigit
  rw [Polynomial.sum_over_range' _ (fun k => by simp) (v + 1)
    (by have := natDegree_idxPolyD Dc v; omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_idxPolyD, if_pos (Finset.mem_range.mp hk)]

/-- A generator-matrix sequence over `𝔽_q` is the linear-coordinate sequence of its rows (any digit code). -/
theorem seqPoint_eq_linPtD {q : ℕ} [NeZero q] (Dc : DigitCode F q) (C : Gen s F) :
    seqPoint Dc C = linPtD Dc (genY C) := by
  funext v c
  unfold seqPoint seqCoord linPtD
  refine tsum_congr fun n => ?_
  rw [genY_idxD]

variable [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p] {q : ℕ} [NeZero q]

include p in
/-- **`cor:unscrambled`** over `𝔽_q` (linear-coordinate form, any digit code with a carry pair). -/
theorem unscrambledD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (Y : Fin s → F[X] → ℕ → F) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → F[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree)
    (hcop : Pairwise fun c c' => IsCoprime (b c) (b c')) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : F[X] → ℕ → F)
    (hrad : IsRadInv (Y ch) (b ch) π) (μ : F) (hμ : μ ≠ 0) (L : Fin s → ℕ → ℕ → F) :
    ¬ IsQuasiUniform (linPtD Dc fun c => if c = ch then fun V n => μ * Y ch V n else scrY (L c) (Y c)) := by
  classical
  refine (nonqu_code (p := p) Dc hq yb yo hcp hs _ (fun c => ?_) b hdeg hcop ch (fun c hc => ?_)
    (fun a i => μ * π a i) ?_).2
  · by_cases h : c = ch
    · subst h; rw [if_pos rfl]; intro V W n; show μ * Y c (V + W) n = μ * Y c V n + μ * Y c W n
      rw [hY c V W n]; ring
    · simp only [if_neg h]; exact scrY_lin _ _ (hY c)
  · simp only [if_neg hc]; exact scrY_isBAdic _ _ _ (hbad c hc)
  · rw [if_pos rfl]; exact smul_isRadInv μ hμ _ _ _ hrad

include p in
/-- **`cor:unscrambled`**, frames, over `𝔽_q` (any digit code with a carry pair): for distinct places the scrambled
frame `C_ĉ = μ diag(β^n) P_{a_ĉ}`, `C_c = L_c P_{a_c}` (`c ≠ ĉ`) is not quasi-uniform, for all `μ, β ∈ 𝔽_q^*`. -/
theorem unscrambled_frameD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo)
    (hs : 2 ≤ s) (a : Fin s → F) (ha : Function.Injective a) (ch : Fin s)
    (μ β : F) (hμ : μ ≠ 0) (hβ : β ≠ 0) (L : Fin s → ℕ → ℕ → F) :
    ¬ IsQuasiUniform (seqPoint Dc (scrFrameF a ch μ β L)) := by
  classical
  set b : Fin s → F[X] := fun c => if c = ch then C β⁻¹ * (X - C (a ch)) else X - C (a c) with hbdef
  set Y : Fin s → F[X] → ℕ → F := fun c =>
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
  have key := unscrambledD (p := p) Dc hq yb yo hcp hs Y hY b hdeg hcop ch hbad _ hrad μ hμ L
  have e : seqPoint Dc (scrFrameF a ch μ β L) =
      linPtD Dc (fun c => if c = ch then fun V n => μ * Y ch V n else scrY (L c) (Y c)) := by
    rw [seqPoint_eq_linPtD]
    congr 1
    funext c V n
    by_cases h : c = ch
    · subst h
      simp only [scrFrameF, genY, if_pos rfl, hYdef, ite_true]
      rw [← pas_sum]
      unfold Polynomial.sum
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [scrFrameF, genY, if_neg h, hYdef, scrY]
      rw [genY_comb (fun j k => pas (a c) j k) (L c) V n]
      exact Finset.sum_congr rfl fun j _ => by rw [pas_sum]
  rw [e]; exact key

include p in
/-- **`cor:faure` for prime powers**: for every finite field `𝔽_q` of characteristic `p`, every digit code with a carry
pair (every natural identification, `carryPair_nat`), every `s ≥ 2` and all distinct places `a_c ∈ 𝔽_q`, the
unscrambled frame `(P_{a_0}, …, P_{a_{s-1}})` is not quasi-uniform. -/
theorem faure_code (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (a : Fin s → F) (ha : Function.Injective a) :
    ¬ IsQuasiUniform (seqPoint Dc (fun c n k => pas (a c) n k)) := by
  have ch : Fin s := ⟨0, by omega⟩
  have h := unscrambled_frameD (p := p) Dc hq yb yo hcp hs a ha ch 1 1 one_ne_zero one_ne_zero
    (fun _ n j => if j = n then 1 else 0)
  have e : scrFrameF a ch 1 1 (fun _ n j => if j = n then 1 else 0) = fun c n k => pas (a c) n k := by
    funext c n k
    unfold scrFrameF
    split_ifs with hc
    · subst hc; simp
    · rw [Finset.sum_eq_single n (fun j _ hj => by simp [hj]) (fun h => absurd
        (Finset.mem_range.mpr (Nat.lt_succ_self n)) h)]
      simp
  rwa [e] at h

variable [DecidableEq F]

include p in
/-- **`cor:nied` for prime powers** (generalized form): distinct monic irreducible bases `b_c ∈ 𝔽_q[z]`,
generalized Niederreiter coordinates, one coordinate `ĉ` with `ϑ_{ĉ,Q,i} ≡ ϑ̄_{ĉ,i} (mod b_ĉ^{Q+1})` and
`ϑ_{ĉ,0,i}` linearly independent modulo `b_ĉ`; digits read through any code with a carry pair. -/
theorem niedGen_not_quD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo)
    (hs : 2 ≤ s) (b : Fin s → F[X]) (hm : ∀ c, (b c).Monic)
    (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) (ϑ : Fin s → ℕ → ℕ → F[X])
    (ch : Fin s) (hcong : ∀ Q i, i < (b ch).natDegree → b ch ^ (Q + 1) ∣ ϑ ch Q i - ϑ ch 0 i %ₘ b ch)
    (hind : ∀ κ : Fin (b ch).natDegree → F, b ch ∣ ∑ i, C (κ i) * ϑ ch 0 i → κ = 0) :
    (∀ ε : ℝ, 0 < ε → ∃ m v w : ℕ, v < q ^ m ∧ w < q ^ m ∧ v ≠ w ∧
        euclDist (linPtD Dc (fun c => niedY (b c) (ϑ c)) v) (linPtD Dc (fun c => niedY (b c) (ϑ c)) w) <
          ε * ((q : ℝ) ^ m) ^ (-(1 : ℝ) / s)) ∧
      ¬ IsQuasiUniform (linPtD Dc fun c => niedY (b c) (ϑ c)) := by
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := fun c =>
    Nat.one_le_iff_ne_zero.mpr fun h => (hirr c).not_isUnit (by
      rw [eq_one_of_monic_natDegree_zero (hm c) h]; exact isUnit_one)
  exact nonqu_code (p := p) Dc hq yb yo hcp hs _ (fun c => niedY_lin _ _) b hdeg
    (monic_irred_coprime b hm hirr hinj) ch (fun c _ => nied_isBAdic (b c) (hm c) (hdeg c) (ϑ c)) _
    (nied_radInv (b ch) (hm ch) (hirr ch) (hdeg ch) (ϑ ch) hcong hind)

include p in
/-- **`cor:nied` for prime powers** (classical): every classical Niederreiter sequence over `𝔽_q` (`s ≥ 2`, distinct
monic irreducible bases, `ϑ_{c,Q,i} = z^i`, digits read through any code with a carry pair, in particular every
natural identification) is not quasi-uniform. -/
theorem nied_not_quD (Dc : DigitCode F q) (hq : 2 ≤ q) (yb yo : F) (hcp : IsCarryPair Dc yb yo) (hs : 2 ≤ s)
    (b : Fin s → F[X]) (hm : ∀ c, (b c).Monic) (hirr : ∀ c, Irreducible (b c)) (hinj : Function.Injective b) :
    ¬ IsQuasiUniform (linPtD Dc fun c => niedY (b c) (fun _ i => X ^ i)) := by
  have hdeg : ∀ c, 1 ≤ (b c).natDegree := fun c =>
    Nat.one_le_iff_ne_zero.mpr fun h => (hirr c).not_isUnit (by
      rw [eq_one_of_monic_natDegree_zero (hm c) h]; exact isUnit_one)
  have ch : Fin s := ⟨0, by omega⟩
  exact (niedGen_not_quD (p := p) Dc hq yb yo hcp hs b hm hirr hinj (fun _ _ i => X ^ i) ch
    (fun Q i hi => classical_cong (b ch) (hm ch) Q i hi)
    (fun κ h => classical_ind (b ch) (hm ch) (hdeg ch) κ h)).2

end Cor

end GeoSeq
