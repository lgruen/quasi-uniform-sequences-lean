/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.WFLaw

@[expose] public section

/-!
# GeoSeq stage S5 (part A): the covering half of `lem:prefix`, and `cor:WF` (mesh ratio)

* `prefix_cov_level`: if `P_{sK}` is a `(0,sK,s)`-net, every point of `[0,1]^s` is within Euclidean
  distance `√s q^{-K}` of a point of `P_{[N]}`, `N ≥ q^{sK}` (one point in every closed cell of side
  `q^{-K}`; the point of the cell `⌊q^K x⌋` (clamped to `q^K - 1`) is found from the net property, and
  its coordinates lie in the closed cell by `coord_split` with `j = 0`). `K = 0` is included
  (`h ≤ √s` for every nonempty set).
* `prefix_cov`: `h(P_{[N]}) ≤ √s q N^{-1/s}` for every `N ≥ 1` (paper's second inequality).
* `prefix_mesh`: with `c(P_{sK}) ≥ LB > 0` for all `K ≥ 1`, `h/δ ≤ √s q/LB` along all `N ≥ 2`
  (comparison of the intermediate bounds, as in the paper), `δ = 2 · sepRad` (toroidal).
* `WF_mesh` (`cor:WF`): `h/δ ≤ 2√2 p²/(p-3)` for the brick walls.
-/

namespace GeoSeq

open Finset

variable {R : Type*} [CommRing R] {q s : ℕ}

/-- The coordinates of a point lie in the closed cell given by its first `K` digits:
`cellIdx ≤ q^K y_c ≤ cellIdx + 1` (`coord_split` with `j = 0`). -/
lemma coord_cell [NeZero q] (hq : 2 ≤ q) (D : DigitCode R q) (C : Gen s R) (v : ℕ) (c : Fin s)
    (K : ℕ) :
    (cellIdx D C v c K : ℝ) ≤ (q : ℝ) ^ K * seqPoint D C v c ∧
      (q : ℝ) ^ K * seqPoint D C v c ≤ (cellIdx D C v c K : ℝ) + 1 := by
  obtain ⟨ε, hε0, hε1, he⟩ := coord_split hq (fun n => (D.enc (seqDigit D C v c n) : ℕ))
    (fun n => (D.enc _).isLt) K 0
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_div, add_zero,
    pow_zero, div_one] at he hε1
  have hcell : ((∑ n : Fin K, (D.enc (seqDigit D C v c n) : ℕ) * q ^ (K - 1 - (n : ℕ)) : ℕ) : ℝ) =
      (cellIdx D C v c K : ℝ) := rfl
  have hpt : seqPoint D C v c =
      ∑' n, (((D.enc (seqDigit D C v c n) : ℕ) : ℝ)) / (q : ℝ) ^ (n + 1) := rfl
  rw [hpt, he, hcell]
  constructor <;> linarith

/-- **`lem:prefix`, covering half (one level)**: if `P_{sK}` is a `(0,sK,s)`-net and `N ≥ q^{sK}`,
then every `x ∈ [0,1]^s` has a point of `P_{[N]}` within Euclidean distance `√s · q^{-K}`. -/
theorem prefix_cov_level [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (K : ℕ)
    (hnet : BlockNet0 D C (s * K) 0) (N : ℕ) (hN : q ^ (s * K) ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤ Real.sqrt s / (q : ℝ) ^ K := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ K := by positivity
  have hQn : 1 ≤ q ^ K := Nat.one_le_pow _ _ (by omega)
  haveI : Nonempty {x : Fin s → ℝ // ∀ j, 0 ≤ x j ∧ x j ≤ 1} :=
    ⟨⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩⟩
  apply ciSup_le
  rintro ⟨x, hx⟩
  -- the cell of `x`
  let a : Fin s → ℕ := fun c => min (⌊(q : ℝ) ^ K * x c⌋₊) (q ^ K - 1)
  have ha : ∀ c, a c < q ^ K := fun c => lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hsum : ∑ _c : Fin s, K = s * K := by simp
  obtain ⟨v, ⟨⟨_, hv⟩, hcell⟩, _⟩ := hnet (fun _ => K) hsum a ha
  have hvN : v < N := lt_of_lt_of_le (by simpa using hv) hN
  have hmem : seqPoint D C v ∈ prefixSet N (seqPoint D C) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hvN, rfl⟩
  have hbdd : BddBelow (Set.range fun y : prefixSet N (seqPoint D C) => euclDist x y.1) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd ⟨_, hmem⟩).trans ?_
  -- coordinatewise `|x_c - y_c| ≤ q^{-K}`
  have hcoord : ∀ c, (x c - seqPoint D C v c) ^ 2 ≤ (1 / (q : ℝ) ^ K) ^ 2 := by
    intro c
    obtain ⟨h1, h2⟩ := coord_cell hq D C v c K
    rw [hcell c] at h1 h2
    have hxa : (a c : ℝ) ≤ (q : ℝ) ^ K * x c ∧ (q : ℝ) ^ K * x c ≤ (a c : ℝ) + 1 := by
      have hx0 : 0 ≤ (q : ℝ) ^ K * x c := mul_nonneg hQ.le (hx c).1
      have hx1 : (q : ℝ) ^ K * x c ≤ (q : ℝ) ^ K := by
        have := mul_le_mul_of_nonneg_left (hx c).2 hQ.le
        linarith
      by_cases hfl : ⌊(q : ℝ) ^ K * x c⌋₊ ≤ q ^ K - 1
      · have hac : a c = ⌊(q : ℝ) ^ K * x c⌋₊ := min_eq_left hfl
        rw [hac]
        exact ⟨Nat.floor_le hx0, (Nat.lt_floor_add_one _).le⟩
      · have hac : a c = q ^ K - 1 := min_eq_right (by omega)
        have hfl' : q ^ K ≤ ⌊(q : ℝ) ^ K * x c⌋₊ := by omega
        have hge : ((q ^ K : ℕ) : ℝ) ≤ (q : ℝ) ^ K * x c :=
          le_trans (by exact_mod_cast hfl') (Nat.floor_le hx0)
        have hcast : ((q ^ K - 1 : ℕ) : ℝ) = (q : ℝ) ^ K - 1 := by
          rw [Nat.cast_sub hQn]; push_cast; ring
        rw [hac, hcast]
        push_cast at hge
        constructor <;> linarith
    have hd : |x c - seqPoint D C v c| ≤ 1 / (q : ℝ) ^ K := by
      have hm : |(q : ℝ) ^ K * (x c - seqPoint D C v c)| ≤ 1 := by
        rw [mul_sub]; exact abs_le.mpr ⟨by linarith [hxa.1, h2], by linarith [hxa.2, h1]⟩
      rw [abs_mul, abs_of_pos hQ] at hm
      rw [le_div_iff₀ hQ, mul_comm]; exact hm
    have := sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2
    simpa using this
  unfold euclDist
  calc Real.sqrt (∑ c, (x c - seqPoint D C v c) ^ 2)
      ≤ Real.sqrt (∑ _c : Fin s, (1 / (q : ℝ) ^ K) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => hcoord c)
    _ = Real.sqrt s / (q : ℝ) ^ K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul
          (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
        ring

/-- The level of `N`: `q^{sK} ≤ N < q^{s(K+1)}` with `K = ⌊log_q N⌋ / s` (as in `prefix_sep`). -/
lemma level_of (hq : 2 ≤ q) (hs : 1 ≤ s) (N : ℕ) (hN : 1 ≤ N) :
    q ^ (s * (Nat.log q N / s)) ≤ N ∧ N < q ^ (s * (Nat.log q N / s + 1)) := by
  set k := Nat.log q N
  set K := k / s with hK
  refine ⟨?_, ?_⟩
  · have h1 : q ^ (s * K) ≤ q ^ k := Nat.pow_le_pow_right (by omega) (Nat.mul_div_le k s)
    exact h1.trans (Nat.pow_log_le_self q (by omega))
  · have h1 : N < q ^ (k + 1) := Nat.lt_pow_succ_log_self (by omega) N
    have h2 : k + 1 ≤ s * (K + 1) := by
      have := Nat.lt_mul_div_succ k (show 0 < s by omega)
      rw [hK]; linarith
    exact h1.trans_le (Nat.pow_le_pow_right (by omega) h2)

/-- **`lem:prefix`, covering half**: for a `(0,s)`-sequence, `h(P_{[N]}) ≤ √s · q · N^{-1/s}` for every
`N ≥ 1`. -/
theorem prefix_cov [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (N : ℕ) (hN : 1 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) := by
  obtain ⟨hlo, hhi⟩ := level_of hq hs N hN
  set K := Nat.log q N / s
  refine (prefix_cov_level D C hq K (hseq _ 0) N hlo).trans ?_
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- `N^{1/s} ≤ q^{K+1}`
  have hroot : (N : ℝ) ^ (1 / (s : ℝ)) ≤ (q : ℝ) ^ (K + 1) := by
    have e1 : ((q : ℝ) ^ (K + 1)) = (((q : ℝ) ^ (K + 1)) ^ s) ^ ((s : ℝ)⁻¹) :=
      (Real.pow_rpow_inv_natCast (by positivity) (by omega)).symm
    rw [e1, one_div]
    apply Real.rpow_le_rpow hNpos.le _ (by positivity)
    rw [← pow_mul, mul_comm]
    exact_mod_cast hhi.le
  have hNs : ((q : ℝ) ^ (K + 1))⁻¹ ≤ (N : ℝ) ^ (-(1 / (s : ℝ))) := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ (by positivity) hroot
  have hs0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  calc Real.sqrt s / (q : ℝ) ^ K = Real.sqrt s * q * ((q : ℝ) ^ (K + 1))⁻¹ := by
        rw [pow_succ]; field_simp
    _ ≤ Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) :=
        mul_le_mul_of_nonneg_left hNs (by positivity)

/-- `2 · sepRad ≥ LB · q^{-(K+1)}` for `P_{[N]}`, `N < q^{s(K+1)}`, `N ≥ 2`, from the separation of the
full level `P_{s(K+1)}`. -/
lemma sepRad_ge [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (K N : ℕ) (hN : 2 ≤ N)
    (hNlt : N < q ^ (s * (K + 1))) (LB : ℝ) (hLB : 0 < LB)
    (hsep : SepAtLevel q s (K + 1) (seqPoint D C) LB) :
    LB / (q : ℝ) ^ (K + 1) ≤
      2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ (K + 1) := by positivity
  -- separation of two distinct indices
  have hpair : ∀ v w, v < N → w < N → v ≠ w →
      LB / (q : ℝ) ^ (K + 1) ≤ Z3NetDGS.torDist2 (seqPoint D C v) (seqPoint D C w) := by
    intro v w hv hw hvw
    have := hsep v w (hv.trans hNlt) (hw.trans hNlt) hvw
    rw [div_le_iff₀ hQ]; linarith
  -- the points `y(0)`, `y(1)` are distinct
  have h01 : seqPoint D C 0 ≠ seqPoint D C 1 := by
    intro h
    have := hpair 0 1 (by omega) (by omega) (by omega)
    rw [h] at this
    have h0 : Z3NetDGS.torDist2 (seqPoint D C 1) (seqPoint D C 1) = 0 := by
      simp [Z3NetDGS.torDist2, Z3NetDGS.torCoord]
    rw [h0] at this
    have : 0 < LB / (q : ℝ) ^ (K + 1) := div_pos hLB hQ
    linarith
  have hmem : ∀ v, v < N → seqPoint D C v ∈ prefixSet N (seqPoint D C) := fun v hv =>
    Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, rfl⟩
  haveI : Nonempty {xy : (Fin s → ℝ) × (Fin s → ℝ) // xy.1 ∈ prefixSet N (seqPoint D C) ∧
      xy.2 ∈ prefixSet N (seqPoint D C) ∧ xy.1 ≠ xy.2} :=
    ⟨⟨(seqPoint D C 0, seqPoint D C 1), hmem 0 (by omega), hmem 1 (by omega), h01⟩⟩
  have : LB / (q : ℝ) ^ (K + 1) / 2 ≤
      Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C)) := by
    apply le_ciInf
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    have hvw : v ≠ w := fun h => hab (by rw [h])
    have := hpair v w (Finset.mem_range.mp hv) (Finset.mem_range.mp hw) hvw
    show LB / (q : ℝ) ^ (K + 1) / 2 ≤ Z3NetDGS.torDist2 (seqPoint D C v) (seqPoint D C w) / 2
    linarith
  linarith

/-- **`lem:prefix`, mesh ratio**: for a `(0,s)`-sequence with `c(P_{sK}) ≥ LB > 0` for all `K ≥ 1`,
`h(P_{[N]}) ≤ (√s q / LB) · δ(P_{[N]})` for every `N ≥ 2` (`h` Euclidean covering radius,
`δ = 2 · sepRad` toroidal separation). -/
theorem prefix_mesh [NeZero q] (D : DigitCode R q) (C : Gen s R) (hq : 2 ≤ q) (hs : 1 ≤ s)
    (hseq : IsSeq0 D C) (LB : ℝ) (hLB : 0 < LB)
    (h : ∀ K : ℕ, 1 ≤ K → SepAtLevel q s K (seqPoint D C) LB) (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤
      Real.sqrt s * q / LB *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint D C))) := by
  obtain ⟨hlo, hhi⟩ := level_of hq hs N (by omega)
  set K := Nat.log q N / s
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcov := prefix_cov_level D C hq K (hseq _ 0) N hlo
  have hsep := sepRad_ge D C hq K N hN hhi LB hLB (h (K + 1) (Nat.le_add_left 1 K))
  have hfac : 0 ≤ Real.sqrt s * q / LB := by positivity
  calc Z3NetDGS.covRad euclDist (prefixSet N (seqPoint D C)) ≤ Real.sqrt s / (q : ℝ) ^ K := hcov
    _ = Real.sqrt s * q / LB * (LB / (q : ℝ) ^ (K + 1)) := by
        rw [pow_succ]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsep hfac

/-- **`cor:WF`** (mesh ratio along all `N`): `h(P_{[N]}) ≤ 2√2 p²/(p-3) · δ(P_{[N]})`, with `h` the
Euclidean covering radius and `δ = 2 · sepRad` the toroidal separation. -/
theorem WF_mesh (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (a : ZMod p) (ha : a = 1 ∨ a = -1)
    (N : ℕ) (hN : 2 ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (seqPoint (zcode p) (WFgen p a))) ≤
      2 * Real.sqrt 2 * (p : ℝ) ^ 2 / ((p : ℝ) - 3) *
        (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (seqPoint (zcode p) (WFgen p a)))) := by
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hLB : (0 : ℝ) < ((p : ℝ) - 3) / (2 * p) := div_pos (by linarith) (by positivity)
  have h := prefix_mesh (zcode p) (WFgen p a) (by omega) (by norm_num) (WF_net p hp a ha)
    _ hLB (fun K hK => WF_sep p hp a ha K hK) N hN
  have e : Real.sqrt ((2 : ℕ) : ℝ) * p / (((p : ℝ) - 3) / (2 * p)) =
      2 * Real.sqrt 2 * (p : ℝ) ^ 2 / ((p : ℝ) - 3) := by
    have : (p : ℝ) - 3 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by linarith
    push_cast
    field_simp
  rwa [e] at h

end GeoSeq
