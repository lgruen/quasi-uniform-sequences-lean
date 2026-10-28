/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V93Poly

@[expose] public section

/-!
# GeoSeq stage V9-3 (part 2): a close pair from a carry (`lem:carrypair`, prime `q = p`)

* Real digit expansions: splitting `∑_j d_j p^{-j-1}` after `L` digits with a tail in `[0, p^{-L}]`, strictly
  below `p^{-L}` when some later digit is `< p - 1` (`tsum_split`); a shared prefix of `L` digits gives a
  coordinate difference `≤ p^{-L}` (`real_prefix`); the carry `0.a(p-1)⋯(p-1) → 0.(a+1)0⋯0` with a strict tail
  gives a difference `< 2 p^{-L}` (`real_carry`).
* `carrydigit_prime` (`eq:carrydigit` for prime `q`: `ȳ = -1`, `y° = 0`, `enc = val`).
* **`carrypair`** (`lem:carrypair`): the two points with indices `ι(V_1)`, `ι(V_1 + D)` lie in `P_m`, are
  distinct, and are at Euclidean distance `< √(s+3) p^{-L}`, `L = e λ`; `carrypair_sep`: hence
  `δ(P_m) < √(s+3) p^{-L}`.

Hypotheses as in the paper, for prime `q`: `π(g) = (1, …, 1)`, `π(g̃) = (0, -1, …, -1)`, `π(g') = (-1, …, -1)`;
only coordinate `ĉ` needs to be a radical inverse, the others only `b_c`-adic (`IsBAdic`, required for `c ≠ ĉ`
only, which is weaker than the paper's "every coordinate").
-/

namespace GeoSeq

open Finset Polynomial

/-! ## Real digit expansions -/

section Real

lemma tsum_split {p : ℕ} (hp : 2 ≤ p) (d : ℕ → ℕ) (hd : ∀ j, d j < p) (L : ℕ) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 / (p : ℝ) ^ L ∧ ((∃ M, L ≤ M ∧ d M + 1 < p) → τ < 1 / (p : ℝ) ^ L) ∧
      ∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1) = ∑ j ∈ range L, (d j : ℝ) / (p : ℝ) ^ (j + 1) + τ := by
  have hqr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq0 : (p : ℝ) ≠ 0 := by positivity
  have hqpos : (0 : ℝ) < p := by positivity
  set f : ℕ → ℝ := fun n => (d n : ℝ) / (p : ℝ) ^ (n + 1) with hf
  set g : ℕ → ℝ := fun n => ((p : ℝ) - 1) / (p : ℝ) ^ (n + 1) with hg
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one hqpos]; linarith
  have hg_eq : ∀ M n, g (n + M) = ((p : ℝ) - 1) / (p : ℝ) ^ (M + 1) * (1 / p) ^ n := by
    intro M n
    simp only [hg, one_div, inv_pow]
    rw [show n + M + 1 = (M + 1) + n by ring, pow_add]
    field_simp
  have hgs : ∀ M, Summable fun n => g (n + M) := by
    intro M
    simp_rw [hg_eq M]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    simp only [hf, hg]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : d n + 1 ≤ p := hd n
    have : (d n : ℝ) + 1 ≤ p := by exact_mod_cast this
    linarith
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfg (by simpa using hgs 0)
  have hsplit := hfs.sum_add_tsum_nat_add L
  set T := ∑' i, f (i + L) with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun i => hf0 _
  have hgL : ∑' i, g (i + L) = 1 / (p : ℝ) ^ L := by
    simp_rw [hg_eq L]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [pow_succ]
    field_simp
  have hTle : T ≤ 1 / (p : ℝ) ^ L := by
    rw [← hgL]
    exact Summable.tsum_le_tsum (fun i => hfg _) ((summable_nat_add_iff L).mpr hfs) (hgs L)
  refine ⟨T, hT0, hTle, ?_, hsplit.symm⟩
  rintro ⟨M, hLM, hM⟩
  rw [← hgL]
  refine Summable.tsum_lt_tsum_of_nonneg (i := M - L) (fun i => hf0 _) (fun i => hfg _) ?_ (hgs L)
  simp only [hf, hg, show M - L + L = M by omega]
  apply div_lt_div_of_pos_right _ (by positivity)
  have : (d M : ℝ) + 1 < p := by exact_mod_cast hM
  linarith

/-- A shared prefix of `L` digits: the two values differ by at most `p^{-L}`. -/
theorem real_prefix {p : ℕ} (hp : 2 ≤ p) (d d' : ℕ → ℕ) (hd : ∀ j, d j < p) (hd' : ∀ j, d' j < p)
    (L : ℕ) (h : ∀ j, j < L → d j = d' j) :
    |∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1) - ∑' j, (d' j : ℝ) / (p : ℝ) ^ (j + 1)| ≤ 1 / (p : ℝ) ^ L := by
  obtain ⟨τ, h0, h1, -, he⟩ := tsum_split hp d hd L
  obtain ⟨τ', h0', h1', -, he'⟩ := tsum_split hp d' hd' L
  have hs : ∑ j ∈ range L, (d j : ℝ) / (p : ℝ) ^ (j + 1) = ∑ j ∈ range L, (d' j : ℝ) / (p : ℝ) ^ (j + 1) :=
    Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]
  rw [he, he', hs, abs_le]
  constructor <;> linarith

/-- The carry: digits `x = 0^k · a · (p-1)^{L-k-1} ⋯` and `x' = 0^k · (a+1) · 0^{L-k-1} ⋯` (equal before
position `k`), with a strict tail for `x'`: `|y(x') - y(x)| < 2 p^{-L}`. -/
theorem real_carry {p : ℕ} (hp : 2 ≤ p) (d d' : ℕ → ℕ) (hd : ∀ j, d j < p) (hd' : ∀ j, d' j < p)
    {k L : ℕ} (hkL : k < L) (h0 : ∀ j, j < k → d j = d' j) (h1 : d' k = d k + 1)
    (h2 : ∀ j, k < j → j < L → d j = p - 1 ∧ d' j = 0) (ht : ∃ M, L ≤ M ∧ d' M + 1 < p) :
    |∑' j, (d' j : ℝ) / (p : ℝ) ^ (j + 1) - ∑' j, (d j : ℝ) / (p : ℝ) ^ (j + 1)| < 2 / (p : ℝ) ^ L := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  obtain ⟨τ, h0τ, h1τ, -, he⟩ := tsum_split hp d hd L
  obtain ⟨τ', h0τ', -, hlt', he'⟩ := tsum_split hp d' hd' L
  have hlt := hlt' ht
  -- the prefixes differ by exactly one unit of the last digit
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
  rw [he, he', abs_lt, h2L]
  constructor <;> linarith

end Real

/-! ## Digits of linear coordinates -/

section Lin
variable {F : Type*} [Field F]

lemma IsLinCoord.zero {Y : F[X] → ℕ → F} (hY : IsLinCoord Y) (n : ℕ) : Y 0 n = 0 := by
  have h := hY 0 0 n
  rw [add_zero] at h
  exact left_eq_add.mp h

lemma IsRadInv.pi_zero {Y : F[X] → ℕ → F} {b : F[X]} {π : F[X] → ℕ → F} (hY : IsLinCoord Y)
    (hr : IsRadInv Y b π) {i : ℕ} (hi : i < b.natDegree) : π 0 i = 0 := by
  have h := hr.2 0 0 i hi
  rw [badicDigit_zero, hY.zero] at h
  exact h.symm

/-- `sec:polybases`: a radical inverse is `b`-adic. -/
theorem IsRadInv.isBAdic {Y : F[X] → ℕ → F} {b : F[X]} {π : F[X] → ℕ → F} (hb : 1 ≤ b.natDegree)
    (hY : IsLinCoord Y) (hr : IsRadInv Y b π) : IsBAdic Y b := by
  intro Q V hV n hn
  obtain ⟨W, rfl⟩ := hV
  have hn' : n = n / b.natDegree * b.natDegree + n % b.natDegree := (Nat.div_add_mod' n _).symm
  have hQ : n / b.natDegree < Q := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
  rw [hn', hr.2 _ _ _ (Nat.mod_lt _ (by omega)), badicDigit_pow_mul hb, ite_eq_left hQ]
  exact hr.pi_zero hY (Nat.mod_lt _ (by omega))

/-- Radical-inverse digits vanish beyond `e (deg V + 1)`. -/
lemma IsRadInv.digit_high {Y : F[X] → ℕ → F} {b : F[X]} {π : F[X] → ℕ → F} (hb : 1 ≤ b.natDegree)
    (hY : IsLinCoord Y) (hr : IsRadInv Y b π) (V : F[X]) (t : ℕ) :
    Y V (b.natDegree * (V.natDegree + 1 + t)) = 0 := by
  have h := hr.2 V (V.natDegree + 1 + t) 0 (by omega)
  rw [add_zero, mul_comm] at h
  rw [h, badicDigit_high hb (by nlinarith)]
  exact hr.pi_zero hY (by omega)

end Lin

/-! ## `lem:carrypair` -/

variable {p : ℕ} [Fact p.Prime] {s : ℕ}

/-- `eq:carrydigit` for prime `q = p`: `ȳ = -1` has digit `p - 1`, `y° = 0`, and adding `-ȳ = 1` to
`y° ȳ ⋯ ȳ` digitwise gives `1 0 ⋯ 0`, one unit of the last digit more. -/
theorem carrydigit_prime :
    (-1 : ZMod p).val = p - 1 ∧ (0 : ZMod p).val = 0 ∧ (1 : ZMod p).val = (0 : ZMod p).val + 1 ∧
      (0 : ZMod p) + 1 = 1 ∧ (-1 : ZMod p) + 1 = 0 := by
  have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  refine ⟨?_, ZMod.val_zero, by rw [h1, ZMod.val_zero], zero_add 1, neg_add_cancel 1⟩
  have hpos := (Fact.out : p.Prime).pos
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact (ZMod.val_neg_one n).trans (by omega)

lemma linPt_polyIdx (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (V : (ZMod p)[X]) (c : Fin s) :
    linPt p Y (polyIdx p V) c = ∑' j : ℕ, ((Y c V j).val : ℝ) / (p : ℝ) ^ (j + 1) := by
  simp only [linPt, idxPolyP_polyIdx]

lemma sepDistIdx_le_pair (pt : ℕ → Fin s → ℝ) {N v w : ℕ} (hv : v < N) (hw : w < N) (hvw : v ≠ w) :
    sepDistIdx pt N ≤ euclDist (pt v) (pt w) := by
  have hbdd : BddBelow (Set.range fun vw : {vw : Fin N × Fin N // vw.1 ≠ vw.2} =>
      euclDist (pt vw.1.1) (pt vw.1.2)) :=
    ⟨0, by rintro _ ⟨vw, rfl⟩; exact Real.sqrt_nonneg _⟩
  exact ciInf_le hbdd ⟨(⟨v, hv⟩, ⟨w, hw⟩), fun h => hvw (Fin.ext_iff.mp h)⟩

lemma sepDistIdx_nonneg (pt : ℕ → Fin s → ℝ) (N : ℕ) : 0 ≤ sepDistIdx pt N :=
  Real.iInf_nonneg fun _ => Real.sqrt_nonneg _

/-- **`lem:carrypair`** (prime `q = p`). Coordinate `ĉ` is a `b`-adic radical inverse with digit map `π`
(`b = b_ĉ`, `e = deg b`), every other coordinate `c` is `b_c`-adic. Let `deg g, deg g̃, deg g' < e` with
`π(g) = (1, …, 1)`, `π(g̃) = (0, -1, …, -1)`, `π(g') = (-1, …, -1)`, and let `D ≠ 0`, `η < λ` with
(i) `D ≡ g b^η S_{λ-η} (mod b^λ)`, (ii) `b_c^{j_c} ∣ D` with `e_c j_c ≥ L = e λ` for every `c ≠ ĉ`,
(iii) `deg D < m`. Then the indices `ι(V_1)`, `ι(V_1 + D)` (`V_1 = g̃ b^η + g' b^{η+1} S_{λ-η-1}`) are `< p^m`,
distinct, and the two points are at Euclidean distance `< √(s+3) p^{-L}`. -/
theorem carrypair (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (D : (ZMod p)[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    polyIdx p (carryV1 (b ch) gt g' η l) < p ^ m ∧
      polyIdx p (carryV1 (b ch) gt g' η l + D) < p ^ m ∧
      polyIdx p (carryV1 (b ch) gt g' η l) ≠ polyIdx p (carryV1 (b ch) gt g' η l + D) ∧
      euclDist (linPt p Y (polyIdx p (carryV1 (b ch) gt g' η l)))
        (linPt p Y (polyIdx p (carryV1 (b ch) gt g' η l + D))) <
        Real.sqrt (s + 3) / (p : ℝ) ^ ((b ch).natDegree * l) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
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
  refine ⟨polyIdx_lt _ hV1m, polyIdx_lt _ hdegV2, fun h => hne (polyIdx_injective h), ?_⟩
  /- the other coordinates share `L` digits -/
  have hother : ∀ c, c ≠ ch → |linPt p Y (polyIdx p V1) c - linPt p Y (polyIdx p (V1 + D)) c| ≤
      1 / (p : ℝ) ^ L := by
    intro c hc
    rw [linPt_polyIdx, linPt_polyIdx]
    refine real_prefix hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) L fun j hj => ?_
    obtain ⟨jc, hjc, hdc⟩ := hii c hc
    rw [hY c V1 D j, hbad c hc jc D hdc j (lt_of_lt_of_le hj hjc), add_zero]
  /- the digits of coordinate `ĉ` -/
  have hpi0 : ∀ i, i < e → π 0 i = 0 := fun i hi => hrad.pi_zero (hY ch) hi
  have hV1f : V1 = B ^ η * (gt + B * (g' * runS B (l - η - 1))) := by
    rw [hV1, carryV1]; ring
  have hdigV1 : ∀ Q i, i < e →
      Y ch V1 (Q * e + i) = if Q * e + i ≤ e * η then 0 else if Q * e + i < L then -1 else 0 := by
    intro Q i hie
    rw [hrad.2 V1 Q i hie, hV1f, badicDigit_pow_mul he1]
    rcases lt_trichotomy Q η with hQ | hQ | hQ
    · rw [ite_eq_left hQ, hpi0 i hie, ite_eq_left]
      have : (Q + 1) * e ≤ η * e := Nat.mul_le_mul_right _ hQ
      nlinarith
    · subst hQ
      rw [ite_eq_right (lt_irrefl _), Nat.sub_self, badicDigit_base hgt, hπgt i hie]
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0; rw [ite_eq_left rfl, ite_eq_left (by rw [mul_comm]; omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by rw [mul_comm]; omega)]
        have h2 : (Q + 1) * e ≤ l * e := Nat.mul_le_mul_right _ hηl
        rw [ite_eq_left (by rw [hL]; nlinarith)]
    · obtain ⟨t, ht⟩ : ∃ t, Q - η = t + 1 := ⟨Q - η - 1, by omega⟩
      rw [ite_eq_right (by omega), ht, badicDigit_succ hgt, badicDigit_run hg']
      have h1 : (η + 1) * e ≤ Q * e := Nat.mul_le_mul_right _ hQ
      rw [ite_eq_right (show ¬ Q * e + i ≤ e * η by nlinarith)]
      by_cases hQl : Q < l
      · rw [ite_eq_left (show t < l - η - 1 by omega), hπg' i hie]
        have h2 : (Q + 1) * e ≤ l * e := Nat.mul_le_mul_right _ hQl
        rw [ite_eq_left (by rw [hL]; nlinarith)]
      · rw [ite_eq_right (show ¬ t < l - η - 1 by omega), hpi0 i hie]
        have h2 : l * e ≤ Q * e := Nat.mul_le_mul_right _ (by omega)
        rw [ite_eq_right (by rw [hL]; nlinarith)]
  have hdigV1' : ∀ n, Y ch V1 n = if n ≤ e * η then 0 else if n < L then -1 else 0 := by
    intro n
    have h := hdigV1 (n / e) (n % e) (Nat.mod_lt _ he1)
    rwa [Nat.div_add_mod' n e] at h
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
  have hdigV2 : ∀ n, Y ch (V1 + D) n = Y ch V1 n + Y ch D n := fun n => hY ch V1 D n
  obtain ⟨hvm1, hv0, hv1, -, -⟩ := (carrydigit_prime : (-1 : ZMod p).val = p - 1 ∧ _)
  have hkL : e * η < L := by rw [hL]; exact Nat.mul_lt_mul_of_pos_left hηl he1
  have hch : |linPt p Y (polyIdx p (V1 + D)) ch - linPt p Y (polyIdx p V1) ch| < 2 / (p : ℝ) ^ L := by
    rw [linPt_polyIdx, linPt_polyIdx]
    refine real_carry hp2 _ _ (fun _ => ZMod.val_lt _) (fun _ => ZMod.val_lt _) hkL ?_ ?_ ?_ ?_
    · intro j hj
      rw [hdigV2, hdigD' j (by omega), ite_eq_left hj, add_zero]
    · rw [hdigV2, hdigD' _ hkL, hdigV1', ite_eq_left le_rfl, ite_eq_right (lt_irrefl _), zero_add, hv1]
    · intro j hj1 hj2
      rw [hdigV2, hdigD' j hj2, hdigV1', ite_eq_right (by omega), ite_eq_left hj2,
        ite_eq_right (by omega)]
      exact ⟨hvm1, (congrArg ZMod.val (neg_add_cancel (1 : ZMod p))).trans hv0⟩
    · refine ⟨e * ((V1 + D).natDegree + 1 + L),
        le_trans (by omega) (Nat.le_mul_of_pos_left _ he1), ?_⟩
      rw [IsRadInv.digit_high he1 (hY ch) hrad, hv0]; omega
  /- the distance -/
  set x := linPt p Y (polyIdx p V1)
  set y := linPt p Y (polyIdx p (V1 + D))
  have hpL : (0 : ℝ) < 1 / (p : ℝ) ^ L := by positivity
  have hsq_ch : (x ch - y ch) ^ 2 < 4 * (1 / (p : ℝ) ^ L) ^ 2 := by
    have h := hch
    rw [abs_sub_comm] at h
    have h2 : (2 : ℝ) / (p : ℝ) ^ L = 2 * (1 / (p : ℝ) ^ L) := by ring
    rw [h2] at h
    have := sq_lt_sq' (abs_lt.mp h).1 (abs_lt.mp h).2
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
  have hsum : ∑ c, (x c - y c) ^ 2 < ((s : ℝ) + 3) * (1 / (p : ℝ) ^ L) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ch)]
    linarith
  unfold euclDist
  have hrhs : (0 : ℝ) < Real.sqrt (s + 3) / (p : ℝ) ^ L := by positivity
  rw [Real.sqrt_lt' hrhs, div_pow, Real.sq_sqrt (by positivity)]
  calc ∑ c, (x c - y c) ^ 2 < ((s : ℝ) + 3) * (1 / (p : ℝ) ^ L) ^ 2 := hsum
    _ = ((s : ℝ) + 3) / ((p : ℝ) ^ L) ^ 2 := by ring

/-- `lem:carrypair`, "in particular": `δ(P_m) < √(s+3) p^{-L}`. -/
theorem carrypair_sep (hs : 2 ≤ s) (Y : Fin s → (ZMod p)[X] → ℕ → ZMod p) (hY : ∀ c, IsLinCoord (Y c))
    (b : Fin s → (ZMod p)[X]) (hdeg : ∀ c, 1 ≤ (b c).natDegree) (ch : Fin s)
    (hbad : ∀ c, c ≠ ch → IsBAdic (Y c) (b c)) (π : (ZMod p)[X] → ℕ → ZMod p)
    (hrad : IsRadInv (Y ch) (b ch) π) (g gt g' : (ZMod p)[X])
    (hg : g.natDegree < (b ch).natDegree) (hgt : gt.natDegree < (b ch).natDegree)
    (hg' : g'.natDegree < (b ch).natDegree)
    (hπg : ∀ i, i < (b ch).natDegree → π g i = 1)
    (hπgt : ∀ i, i < (b ch).natDegree → π gt i = if i = 0 then 0 else -1)
    (hπg' : ∀ i, i < (b ch).natDegree → π g' i = -1)
    (D : (ZMod p)[X]) (hD : D ≠ 0) (η l m : ℕ) (hηl : η < l)
    (hi : b ch ^ l ∣ D - g * b ch ^ η * runS (b ch) (l - η))
    (hii : ∀ c, c ≠ ch → ∃ j, (b ch).natDegree * l ≤ (b c).natDegree * j ∧ b c ^ j ∣ D)
    (hiii : D.natDegree < m) :
    sepDistIdx (linPt p Y) (p ^ m) < Real.sqrt (s + 3) / (p : ℝ) ^ ((b ch).natDegree * l) := by
  obtain ⟨h1, h2, h3, h4⟩ := carrypair hs Y hY b hdeg ch hbad π hrad g gt g' hg hgt hg' hπg hπgt hπg' D hD
    η l m hηl hi hii hiii
  exact (sepDistIdx_le_pair _ h1 h2 h3).trans_lt h4

end GeoSeq
