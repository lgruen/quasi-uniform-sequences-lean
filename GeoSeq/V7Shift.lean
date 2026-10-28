/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7Defs
public import GeoSeq.Cert
public import GeoSeq.SeqNet
public import GeoSeq.Mesh

@[expose] public section

/-!
# GeoSeq stage V7: digital shifts (`lem:shift`)

For any digit code `D` (in particular `q` prime with `enc = val`, and `q = 2^r` with an `𝔽_2`-linear code) and any
array `ς` of digits:

* **`shift_seq0`**: the shifted sequence (digits `y_{c,n}(v) + ς_{c,n}`) is a `(0,s)`-sequence iff the unshifted one
  is (a shift maps every elementary box onto one of the same shape, `cond_shift`).
* **`cert_shift`**: every bound `c(P_{sK}) ≥ min(1, LB_j)` that `lem:cert` gives for the unshifted sequence (i.e.
  under exactly the hypotheses of `cert`) holds for the shifted prefix `P_{sK}`. The proof is the proof of `cert`
  run on the shifted digits: the shifted cell indices step by `e` with a carry pattern of the SHIFTED digits, and
  the unshifted digits change by the same amounts (the shift is additive), so the geometric digits change by the
  expression of `lem:cert` with the shifted stop digit.
* **`shift_prefix`** (the "in particular" clause): if `lem:cert` gives `0 < LB ≤ 1` at every level `K` with
  `q^K ≥ 4` (`CertAt`), then for every `K_0` with `q^{K_0} ≥ 4` and every `N > q^{s(K_0-1)}` the bounds of
  `lem:prefix` hold for the shifted sequence: `δ(P_{[N]}) ≥ (LB/q) N^{-1/s}`, `h(P_{[N]}) ≤ √s q N^{-1/s}`,
  `h ≤ (√s q/LB) δ`; **`shift_prefix_q4`**: for `q ≥ 4` this is every `N ≥ 2`.
-/

namespace GeoSeq

open Finset

section Cells

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- The cell index of a digit sequence `x` with `K` digits (most significant first). -/
def cellOf (D : DigitCode R q) (x : ℕ → R) (K : ℕ) : ℕ :=
  ∑ n : Fin K, (D.enc (x n) : ℕ) * q ^ (K - 1 - (n : ℕ))

lemma cellOf_lt (D : DigitCode R q) (x : ℕ → R) (K : ℕ) : cellOf D x K < q ^ K :=
  Z3Net.Proofs.digSum_lt q K _ (fun _ => (D.enc _).isLt)

lemma cellOf_digit (D : DigitCode R q) (x : ℕ → R) (K n : ℕ) (hn : n < K) :
    (D.enc (x n) : ℕ) = cellOf D x K / q ^ (K - 1 - n) % q :=
  (Z3NetF.Proofs.digSum_digit (NeZero.pos q) K (fun n : Fin K => (D.enc (x n) : ℕ))
    (fun _ => (D.enc _).isLt) ⟨n, hn⟩).symm

/-- **Classification of one coordinate** (proof of `lem:cert`, for any digit sequences `x`, `z`): the cells are
either at toroidal distance `≥ 2`, or neighbours `n' ≡ n + e`, and then the digits change by `e` times a carry
pattern (`carry_digits`). -/
theorem coord_class_dig (D : DigitCode R q) (hq : 2 ≤ q) (K : ℕ) (hK : 1 ≤ K) (x z : ℕ → R) :
    (2 ≤ |(cellOf D z K : ℝ) - cellOf D x K| ∧
      |(cellOf D z K : ℝ) - cellOf D x K| ≤ (q : ℝ) ^ K - 2) ∨
    ∃ e : ℤ, ∃ l : ℕ, ∃ y : R, (-1 ≤ e ∧ e ≤ 1) ∧ (1 ≤ l ∧ l ≤ K) ∧
      ((cellOf D z K : ℝ) - cellOf D x K - e = 0 ∨
        (cellOf D z K : ℝ) - cellOf D x K - e = (q : ℝ) ^ K ∨
        (cellOf D z K : ℝ) - cellOf D x K - e = -(q : ℝ) ^ K) ∧
      (e = 0 → cellOf D z K = cellOf D x K) ∧
      ∀ n < K, z n - x n = (e : R) *
        (digInc D (topDigit D) * (if K - (l - 1) ≤ n then 1 else 0) +
          digInc D y * (if n = K - l then 1 else 0)) := by
  set a := cellOf D x K with ha
  set b := cellOf D z K with hb
  have hav : a < q ^ K := cellOf_lt D x K
  have hbw : b < q ^ K := cellOf_lt D z K
  have hQ : ((q ^ K : ℕ) : ℝ) = (q : ℝ) ^ K := by push_cast; ring
  have hcases : b = a ∨ (b = a + 1 ∨ (a + 1 = q ^ K ∧ b = 0)) ∨ (a = b + 1 ∨ (b + 1 = q ^ K ∧ a = 0)) ∨
      (a + 2 ≤ b ∧ b + 2 ≤ a + q ^ K) ∨ (b + 2 ≤ a ∧ a + 2 ≤ b + q ^ K) := by omega
  rcases hcases with h | h | h | h | h
  · -- same cell
    right
    refine ⟨0, 1, 0, by omega, ⟨le_rfl, hK⟩, Or.inl (by rw [h]; simp), fun _ => h, ?_⟩
    intro n hn
    have : z n = x n := by
      apply D.enc.injective; apply Fin.ext
      rw [cellOf_digit D z K n hn, cellOf_digit D x K n hn, ← hb, ← ha, h]
    rw [this]; simp
  all_goals try
    (left
     have hb' : (a : ℝ) + 2 ≤ b ∨ (b : ℝ) + 2 ≤ a := by
       rcases h with ⟨h1, _⟩; first | (left; exact_mod_cast h1) | (right; exact_mod_cast h1)
     have hb'' : (b : ℝ) + 2 ≤ a + (q : ℝ) ^ K ∧ (a : ℝ) + 2 ≤ b + (q : ℝ) ^ K := by
       rw [← hQ]; rcases h with ⟨h1, h2⟩
       constructor
       · have : b + 2 ≤ a + q ^ K := by omega
         exact_mod_cast this
       · have : a + 2 ≤ b + q ^ K := by omega
         exact_mod_cast this
     rcases abs_cases ((b : ℝ) - a) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> constructor <;>
       rcases hb' with hb' | hb' <;> linarith [hb''.1, hb''.2])
  · -- `b = a + 1`, or the wrap `a = q^K - 1`, `b = 0`: a step `+1` from the cell of `v`
    right
    have hmod : b = (a + 1) % q ^ K := by
      rcases h with h | ⟨h1, h2⟩
      · rw [Nat.mod_eq_of_lt (by omega)]; exact h
      · rw [h1, Nat.mod_self, h2]
    obtain ⟨l, hl1, hl2, hdig⟩ := carry_digits D hq K hK x
      z hmod
    refine ⟨1, l, x (K - l), by omega, ⟨hl1, hl2⟩, ?_, fun h => absurd h (by omega), ?_⟩
    · rcases h with h | ⟨h1, h2⟩
      · left; rw [h]; push_cast; ring
      · right; right
        have : (a : ℝ) + 1 = (q : ℝ) ^ K := by rw [← hQ, ← h1]; push_cast; ring
        rw [h2]; push_cast; linarith
    · intro n hn; rw [hdig n hn]; push_cast; ring
  · -- `a = b + 1` or the wrap: a step `+1` from the cell of `w`
    right
    have hmod : a = (b + 1) % q ^ K := by
      rcases h with h | ⟨h1, h2⟩
      · rw [Nat.mod_eq_of_lt (by omega)]; exact h
      · rw [h1, Nat.mod_self, h2]
    obtain ⟨l, hl1, hl2, hdig⟩ := carry_digits D hq K hK z
      x hmod
    refine ⟨-1, l, z (K - l), by omega, ⟨hl1, hl2⟩, ?_, fun h => absurd h (by omega), ?_⟩
    · rcases h with h | ⟨h1, h2⟩
      · left; rw [h]; push_cast; ring
      · right; left
        have : (b : ℝ) + 1 = (q : ℝ) ^ K := by rw [← hQ, ← h1]; push_cast; ring
        rw [h2]; push_cast; linarith
    · intro n hn
      have := hdig n hn
      rw [← neg_sub, this]; push_cast; ring

end Cells

section Main

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **`lem:shift`, `t = 0`**: the shifted sequence (digits `y_{c,n}(v) + ς_{c,n}`, any array `ς`) is a
`(0,s)`-sequence if and only if the unshifted one is. -/
theorem shift_seq0 (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) :
    IsSeq0Sh D C ς ↔ IsSeq0 D C := by
  have key : ∀ (u u' : Fin s → ℕ → R) (d : Fin s → ℕ) (a : Fin s → ℕ), (∀ c, a c < q ^ d c) →
      ∃ a' : Fin s → ℕ, (∀ c, a' c < q ^ d c) ∧ ∀ v : ℕ,
        (∀ c, cellOf D (fun n => seqDigit D C v c n + u c n) (d c) = a c) ↔
        (∀ c, cellOf D (fun n => seqDigit D C v c n + u' c n) (d c) = a' c) := by
    intro u u' d a ha
    obtain ⟨a', ha', hiff⟩ := cond_shift D d u u' a ha
    exact ⟨a', ha', fun v => hiff (fun c n => seqDigit D C v c n)⟩
  have e0 : ∀ v c d, cellOf D (fun n => seqDigit D C v c n + (fun _ _ => (0 : R)) c n) d =
      cellIdx D C v c d := fun v c d => by simp [cellOf, cellIdx]
  have e1 : ∀ v c d, cellOf D (fun n => seqDigit D C v c n + ς c n) d = shCell D C ς v c d :=
    fun v c d => rfl
  constructor
  · intro h m k d hd a ha
    obtain ⟨a', ha', hiff⟩ := key (fun _ _ => 0) ς d a ha
    obtain ⟨v, hv, hu⟩ := h m k d hd a' ha'
    refine ⟨v, ⟨hv.1, fun c => ?_⟩, fun v' hv' => hu v' ⟨hv'.1, ?_⟩⟩
    · have := (hiff v).2 (fun c => by rw [e1]; exact hv.2 c) c; rwa [e0] at this
    · intro c; rw [← e1]; exact (hiff v').1 (fun c => by rw [e0]; exact hv'.2 c) c
  · intro h m k d hd a ha
    obtain ⟨a', ha', hiff⟩ := key ς (fun _ _ => 0) d a ha
    obtain ⟨v, hv, hu⟩ := h m k d hd a' ha'
    refine ⟨v, ⟨hv.1, fun c => ?_⟩, fun v' hv' => hu v' ⟨hv'.1, ?_⟩⟩
    · have := (hiff v).2 (fun c => by rw [e0]; exact hv.2 c) c; rwa [e1] at this
    · intro c; rw [← e0]; exact (hiff v').1 (fun c => by rw [e1]; exact hv'.2 c) c

/-- **`lem:shift`, the certificate** (any digit code `D`, any array `ς` of digits): under the hypotheses of
`lem:cert` (`cert`: `P_{sK}` a `(0,sK,s)`-net, `q^K ≥ 4`, carry responses `D_i(l)`, `LB` at most every certificate
term), the SHIFTED prefix `P_{sK}` has `c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_shift [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R)
    (K j : ℕ)
    (hK : 4 ≤ q ^ K) (hnet : BlockNet0 D C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → R)
    (hD0 : ∀ i c c', Dr i 0 c c' = 0)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ)
    (hLB : ∀ e l, IsStep K e l → ∀ y : Fin s → R, LB ≤ certTerm D j e (certSigma D Dr j e l y)) :
    SepAtLevel q s K (shPoint D C ς) (min 1 LB) := by
  classical
  have hq2 : 2 ≤ q := by
    by_contra h
    have h1 : q ^ K ≤ 1 ^ K := Nat.pow_le_pow_left (by omega) K
    rw [one_pow] at h1; omega
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hK
    · exact h
  intro v w hv hw hvw
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ4 : (4 : ℝ) ≤ (q : ℝ) ^ K := by exact_mod_cast hK
  have hQpos : (0 : ℝ) < (q : ℝ) ^ K := by positivity
  have hQj : (0 : ℝ) < (q : ℝ) ^ j := by positivity
  -- `eq:cellunits` for every point and coordinate
  have hsplit : ∀ x c, ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / (q : ℝ) ^ j ∧
      (q : ℝ) ^ K * shPoint D C ς x c = (shCell D C ς x c K : ℝ) +
        (encVec D (fun i : Fin j => shDigit D C ς x c (K + i)) : ℝ) / (q : ℝ) ^ j + ε :=
    fun x c => coord_split hq2 (fun n => (D.enc (shDigit D C ς x c n) : ℕ)) (fun _ => (D.enc _).isLt) K j
  choose ε hε0 hε1 hεeq0 using hsplit
  have hεeq : ∀ x c, (q : ℝ) ^ K * shPoint D C ς x c = (shCell D C ς x c K : ℝ) +
      ((encVec D (fun i : Fin j => shDigit D C ς x c (K + i)) : ℝ) / (q : ℝ) ^ j + ε x c) :=
    fun x c => by rw [hεeq0]; ring
  set E : ℕ → Fin s → ℕ := fun x c => encVec D (fun i : Fin j => shDigit D C ς x c (K + i)) with hEdef
  have hE : ∀ x c, (E x c : ℝ) + 1 ≤ (q : ℝ) ^ j := by
    intro x c
    have : E x c < q ^ j := Z3Net.Proofs.digSum_lt q j _ (fun _ => (D.enc _).isLt)
    have : E x c + 1 ≤ q ^ j := this
    exact_mod_cast this
  have hu0 : ∀ x c, 0 ≤ (E x c : ℝ) / (q : ℝ) ^ j + ε x c := fun x c => by
    have := hε0 x c; positivity
  have hu1 : ∀ x c, (E x c : ℝ) / (q : ℝ) ^ j + ε x c ≤ 1 := by
    intro x c
    have h1 := hε1 x c
    have h2 : (E x c : ℝ) / (q : ℝ) ^ j + 1 / (q : ℝ) ^ j ≤ 1 := by
      rw [← add_div, div_le_one hQj]; exact hE x c
    linarith
  have hcellQ : ∀ x c, (shCell D C ς x c K : ℝ) + 1 ≤ (q : ℝ) ^ K := by
    intro x c
    have : shCell D C ς x c K + 1 ≤ q ^ K := cellOf_lt D _ K
    exact_mod_cast this
  have hy : ∀ x c, 0 ≤ shPoint D C ς x c ∧ shPoint D C ς x c ≤ 1 := by
    intro x c
    have h := hεeq x c
    have h0 := hu0 x c; have h1 := hu1 x c; have h2 := hcellQ x c
    have h3 : (0 : ℝ) ≤ shCell D C ς x c K := Nat.cast_nonneg _
    constructor
    · by_contra hn; push_neg at hn
      have : (q : ℝ) ^ K * shPoint D C ς x c < 0 := mul_neg_of_pos_of_neg hQpos hn
      linarith
    · by_contra hn; push_neg at hn
      have : (q : ℝ) ^ K < (q : ℝ) ^ K * shPoint D C ς x c := by nlinarith
      linarith
  -- the goal in cell units
  show min 1 LB ≤ (q : ℝ) ^ K * Z3NetDGS.torDist2 (shPoint D C ς v) (shPoint D C ς w)
  rw [show Z3NetDGS.torDist2 (shPoint D C ς v) (shPoint D C ς w) =
    Real.sqrt (∑ c, Z3NetDGS.torCoord (shPoint D C ς v c) (shPoint D C ς w c) ^ 2) from rfl,
    mul_sqrt_sum hQpos.le]
  by_cases hfar : ∃ c, 2 ≤ |(shCell D C ς w c K : ℝ) - shCell D C ς v c K| ∧
      |(shCell D C ς w c K : ℝ) - shCell D C ς v c K| ≤ (q : ℝ) ^ K - 2
  · -- cells at least two apart in some coordinate: distance `≥ 1` cell
    obtain ⟨c0, h1, h2⟩ := hfar
    have hc0 := tor_far hQpos (hεeq v c0) (hεeq w c0) (hu0 v c0) (hu1 v c0) (hu0 w c0) (hu1 w c0) h1 h2
    apply min_le_of_left_le
    calc (1 : ℝ) ≤ (q : ℝ) ^ K * Z3NetDGS.torCoord (shPoint D C ς v c0) (shPoint D C ς w c0) := hc0
      _ = Real.sqrt (((q : ℝ) ^ K *
            Z3NetDGS.torCoord (shPoint D C ς v c0) (shPoint D C ς w c0)) ^ 2) :=
          (Real.sqrt_sq (by linarith)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun c => ((q : ℝ) ^ K *
            Z3NetDGS.torCoord (shPoint D C ς v c) (shPoint D C ς w c)) ^ 2)
            (fun c _ => sq_nonneg _) (Finset.mem_univ c0))
  · -- neighbouring cells: a step `e` with carry lengths `l` and stop digits `y`
    push_neg at hfar
    have hnear := fun c => (coord_class_dig D hq2 K hK1 (shDigit D C ς v c) (shDigit D C ς w c)).resolve_left
      (fun h => absurd h.2 (not_le.mpr (hfar c h.1)))
    choose e l y he hl hk h0 hdig using hnear
    have hne : ∃ c, e c ≠ 0 := by
      by_contra hall; push_neg at hall
      apply hvw
      have hcell : ∀ c, cellIdx D C w c K = cellIdx D C v c K := by
        intro c
        have hsh : shCell D C ς w c K = shCell D C ς v c K := h0 c (hall c)
        unfold cellIdx
        refine Finset.sum_congr rfl fun n _ => ?_
        have hd : shDigit D C ς w c n = shDigit D C ς v c n := by
          apply D.enc.injective; apply Fin.ext
          rw [cellOf_digit D _ K n n.isLt, cellOf_digit D _ K n n.isLt]
          exact congrArg (fun t => t / q ^ (K - 1 - (n : ℕ)) % q) hsh
        unfold shDigit at hd
        rw [add_right_cancel hd]
      obtain ⟨x, _, hxu⟩ := hnet (fun _ => K) (by simp)
        (fun c => cellIdx D C v c K) (fun c => cell_lt D C v c K)
      have hvx := hxu v ⟨⟨by simp, by simpa using hv⟩, fun c => rfl⟩
      have hwx := hxu w ⟨⟨by simp, by simpa using hw⟩, fun c => hcell c⟩
      rw [hvx, hwx]
    have hstep : IsStep K e l := ⟨he, hne, hl⟩
    -- the geometric digits: `R'_c = R_c ⊕ σ_c` (linearity of the law)
    have hgeo : ∀ c (i : Fin j), shDigit D C ς w c (K + i) =
        shDigit D C ς v c (K + i) + certSigma D Dr j e l y c i := by
      intro c i
      have hv' : v < q ^ (s * K) := hv
      have hw' : w < q ^ (s * K) := hw
      set Vd : Fin (s * K) → R :=
        (fun k : Fin (s * K) => idxDigit D w k) - fun k : Fin (s * K) => idxDigit D v k with hVd
      have hdigV : ∀ c₁ n, vecDigit C Vd c₁ n = shDigit D C ς w c₁ n - shDigit D C ς v c₁ n := by
        intro c₁ n
        rw [hVd, vecDigit_sub, ← seqDigit_vec D C hw', ← seqDigit_vec D C hv']
        unfold shDigit
        abel
      have key := law_step C K j hK1 Dr hD0 hD i i.isLt c Vd
        (fun c' => (e c' : R) * digInc D (topDigit D)) (fun c' => (e c' : R) * digInc D (y c')) l hl
        (by
          intro c₁ n hn
          rw [hdigV, hdig c₁ n hn, Finset.sum_eq_single c₁]
          · rw [carryPat_diff (hl c₁).1 (hl c₁).2 c₁ hn, carryPat_self K _ c₁ hn]; ring
          · intro c' _ hc'
            rw [carryPat_ne K _ (Ne.symm hc'), carryPat_ne K _ (Ne.symm hc')]; ring
          · intro h; exact absurd (Finset.mem_univ c₁) h)
      rw [hdigV] at key
      rw [← sub_eq_iff_eq_add', key]
      unfold certSigma carryChange
      exact Finset.sum_congr rfl fun c' _ => by ring
    -- the coordinate gaps
    have hgap : ∀ c, (gapNum D j (e c) (certSigma D Dr j e l y c) : ℝ) / (q : ℝ) ^ j ≤
        (q : ℝ) ^ K * Z3NetDGS.torCoord (shPoint D C ς v c) (shPoint D C ς w c) := by
      intro c
      set r : Fin j → R := fun i => shDigit D C ς v c (K + i) with hr
      have hrw : (fun i : Fin j => shDigit D C ς w c (K + i)) = r + certSigma D Dr j e l y c := by
        funext i; rw [hgeo c i]; rfl
      set S := (Finset.univ.image fun r : Fin j → R =>
        ((e c * (q : ℤ) ^ j + (encVec D (r + certSigma D Dr j e l y c) : ℤ) -
          (encVec D r : ℤ)).natAbs)) with hS
      have hmin : S.min' (by simp [hS]) ≤ ((e c * (q : ℤ) ^ j +
          (encVec D (r + certSigma D Dr j e l y c) : ℤ) - (encVec D r : ℤ)).natAbs) :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))
      have hN : ((S.min' (by simp [hS]) : ℕ) : ℝ) ≤
          |(e c : ℝ) * (q : ℝ) ^ j + (E w c : ℝ) - (E v c : ℝ)| := by
        have h1 : ((S.min' (by simp [hS]) : ℕ) : ℝ) ≤ ((e c * (q : ℤ) ^ j +
            (encVec D (r + certSigma D Dr j e l y c) : ℤ) - (encVec D r : ℤ)).natAbs : ℝ) := by
          exact_mod_cast hmin
        rw [Nat.cast_natAbs, Int.cast_abs] at h1
        have h2 : E w c = encVec D (r + certSigma D Dr j e l y c) := by
          rw [hEdef]; simp only; rw [hrw]
        rw [h2]; push_cast at h1 ⊢; exact h1
      have hg := gap_bound hQj (e c) (E v c) (E w c) (ε v c) (ε w c) (hε0 v c) (hε1 v c) (hε0 w c)
        (hε1 w c) _ hN
      have hgeq : gapNum D j (e c) (certSigma D Dr j e l y c) = S.min' (by simp [hS]) - 1 := rfl
      rw [hgeq]
      refine hg.trans ?_
      have he1 : |(e c : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> exact_mod_cast (by have := he c; omega)
      have hk' : (shCell D C ς w c K : ℝ) - shCell D C ς v c K - (e c : ℝ) = 0 ∨
          (shCell D C ς w c K : ℝ) - shCell D C ς v c K - (e c : ℝ) = (q : ℝ) ^ K ∨
          (shCell D C ς w c K : ℝ) - shCell D C ς v c K - (e c : ℝ) = -(q : ℝ) ^ K := hk c
      exact tor_near hQ4 (hy v c).1 (hy v c).2 (hy w c).1 (hy w c).2 (hεeq v c) (hεeq w c)
        (hu0 v c) (hu1 v c) (hu0 w c) (hu1 w c) he1 hk'
    apply min_le_of_right_le
    refine (hLB e l hstep y).trans ?_
    unfold certTerm
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun c _ => ?_
    exact pow_le_pow_left₀ (by positivity) (hgap c) 2


/-- The coordinates of a shifted point lie in the closed cell of its first `K` (shifted) digits. -/
lemma shift_coord_cell (hq : 2 ≤ q) (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) (v : ℕ)
    (c : Fin s) (K : ℕ) :
    (shCell D C ς v c K : ℝ) ≤ (q : ℝ) ^ K * shPoint D C ς v c ∧
      (q : ℝ) ^ K * shPoint D C ς v c ≤ (shCell D C ς v c K : ℝ) + 1 := by
  obtain ⟨ε, hε0, hε1, he⟩ := coord_split hq (fun n => (D.enc (shDigit D C ς v c n) : ℕ))
    (fun n => (D.enc _).isLt) K 0
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, zero_div, add_zero,
    pow_zero, div_one] at he hε1
  have hcell : ((∑ n : Fin K, (D.enc (shDigit D C ς v c n) : ℕ) * q ^ (K - 1 - (n : ℕ)) : ℕ) : ℝ) =
      (shCell D C ς v c K : ℝ) := rfl
  have hpt : shPoint D C ς v c =
      ∑' n, (((D.enc (shDigit D C ς v c n) : ℕ) : ℝ)) / (q : ℝ) ^ (n + 1) := rfl
  rw [hpt, he, hcell]
  constructor <;> linarith

/-- **`lem:prefix`, covering half, for the shifted sequence (one level)**: if the shifted sequence is a
`(0,s)`-sequence and `N ≥ q^{sK}`, every `x ∈ [0,1]^s` has a shifted point of `P_{[N]}` within `√s · q^{-K}`. -/
theorem shift_cov_level (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R) (hq : 2 ≤ q) (K : ℕ)
    (hsh : IsSeq0Sh D C ς) (N : ℕ) (hN : q ^ (s * K) ≤ N) :
    Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤ Real.sqrt s / (q : ℝ) ^ K := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ K := by positivity
  have hQn : 1 ≤ q ^ K := Nat.one_le_pow _ _ (by omega)
  haveI : Nonempty {x : Fin s → ℝ // ∀ j, 0 ≤ x j ∧ x j ≤ 1} :=
    ⟨⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩⟩
  apply ciSup_le
  rintro ⟨x, hx⟩
  let a : Fin s → ℕ := fun c => min (⌊(q : ℝ) ^ K * x c⌋₊) (q ^ K - 1)
  have ha : ∀ c, a c < q ^ K := fun c => lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hsum : ∑ _c : Fin s, K = s * K := by simp
  obtain ⟨v, ⟨⟨_, hv⟩, hcell⟩, _⟩ := hsh (s * K) 0 (fun _ => K) hsum a ha
  have hvN : v < N := lt_of_lt_of_le (by simpa using hv) hN
  have hmem : shPoint D C ς v ∈ prefixSet N (shPoint D C ς) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hvN, rfl⟩
  have hbdd : BddBelow (Set.range fun y : prefixSet N (shPoint D C ς) => euclDist x y.1) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd ⟨_, hmem⟩).trans ?_
  have hcoord : ∀ c, (x c - shPoint D C ς v c) ^ 2 ≤ (1 / (q : ℝ) ^ K) ^ 2 := by
    intro c
    obtain ⟨h1, h2⟩ := shift_coord_cell hq D C ς v c K
    rw [hcell c] at h1 h2
    have hxa : (a c : ℝ) ≤ (q : ℝ) ^ K * x c ∧ (q : ℝ) ^ K * x c ≤ (a c : ℝ) + 1 := by
      have hx0 : 0 ≤ (q : ℝ) ^ K * x c := mul_nonneg hQ.le (hx c).1
      by_cases hfl : ⌊(q : ℝ) ^ K * x c⌋₊ ≤ q ^ K - 1
      · have hac : a c = ⌊(q : ℝ) ^ K * x c⌋₊ := min_eq_left hfl
        rw [hac]
        exact ⟨Nat.floor_le hx0, (Nat.lt_floor_add_one _).le⟩
      · have hac : a c = q ^ K - 1 := min_eq_right (by omega)
        have hfl' : q ^ K ≤ ⌊(q : ℝ) ^ K * x c⌋₊ := by omega
        have hge : ((q ^ K : ℕ) : ℝ) ≤ (q : ℝ) ^ K * x c :=
          le_trans (by exact_mod_cast hfl') (Nat.floor_le hx0)
        have hx1 : (q : ℝ) ^ K * x c ≤ (q : ℝ) ^ K := by
          have := mul_le_mul_of_nonneg_left (hx c).2 hQ.le
          linarith
        have hcast : ((q ^ K - 1 : ℕ) : ℝ) = (q : ℝ) ^ K - 1 := by
          rw [Nat.cast_sub hQn]; push_cast; ring
        rw [hac, hcast]
        push_cast at hge
        constructor <;> linarith
    have hd : |x c - shPoint D C ς v c| ≤ 1 / (q : ℝ) ^ K := by
      have hm : |(q : ℝ) ^ K * (x c - shPoint D C ς v c)| ≤ 1 := by
        rw [mul_sub]; exact abs_le.mpr ⟨by linarith [hxa.1, h2], by linarith [hxa.2, h1]⟩
      rw [abs_mul, abs_of_pos hQ] at hm
      rw [le_div_iff₀ hQ, mul_comm]; exact hm
    have := sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2
    simpa using this
  unfold euclDist
  calc Real.sqrt (∑ c, (x c - shPoint D C ς v c) ^ 2)
      ≤ Real.sqrt (∑ _c : Fin s, (1 / (q : ℝ) ^ K) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun c _ => hcoord c)
    _ = Real.sqrt s / (q : ℝ) ^ K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul
          (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
        ring

end Main

section Prefix

variable {s q : ℕ}

/-- `2 · sepRad ≥ LB · q^{-(K+1)}` for the first `N ≥ 2` points of any point sequence whose full level
`P_{s(K+1)}` is `LB`-separated (`N < q^{s(K+1)}`). -/
lemma sepRad_ge_pt (pt : ℕ → Fin s → ℝ) (hq : 2 ≤ q) (K N : ℕ) (hN : 2 ≤ N)
    (hNlt : N < q ^ (s * (K + 1))) (LB : ℝ) (hLB : 0 < LB) (hsep : SepAtLevel q s (K + 1) pt LB) :
    LB / (q : ℝ) ^ (K + 1) ≤ 2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N pt) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ (K + 1) := by positivity
  have hpair : ∀ v w, v < N → w < N → v ≠ w →
      LB / (q : ℝ) ^ (K + 1) ≤ Z3NetDGS.torDist2 (pt v) (pt w) := by
    intro v w hv hw hvw
    have := hsep v w (hv.trans hNlt) (hw.trans hNlt) hvw
    rw [div_le_iff₀ hQ]; linarith
  have h01 : pt 0 ≠ pt 1 := by
    intro h
    have := hpair 0 1 (by omega) (by omega) (by omega)
    rw [h] at this
    have h0 : Z3NetDGS.torDist2 (pt 1) (pt 1) = 0 := by
      simp [Z3NetDGS.torDist2, Z3NetDGS.torCoord]
    rw [h0] at this
    have : 0 < LB / (q : ℝ) ^ (K + 1) := div_pos hLB hQ
    linarith
  have hmem : ∀ v, v < N → pt v ∈ prefixSet N pt := fun v hv =>
    Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, rfl⟩
  haveI : Nonempty {xy : (Fin s → ℝ) × (Fin s → ℝ) // xy.1 ∈ prefixSet N pt ∧
      xy.2 ∈ prefixSet N pt ∧ xy.1 ≠ xy.2} :=
    ⟨⟨(pt 0, pt 1), hmem 0 (by omega), hmem 1 (by omega), h01⟩⟩
  have : LB / (q : ℝ) ^ (K + 1) / 2 ≤ Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N pt) := by
    apply le_ciInf
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
    have hvw : v ≠ w := fun h => hab (by rw [h])
    have := hpair v w (Finset.mem_range.mp hv) (Finset.mem_range.mp hw) hvw
    show LB / (q : ℝ) ^ (K + 1) / 2 ≤ Z3NetDGS.torDist2 (pt v) (pt w) / 2
    linarith
  linarith

/-- `q^{-K} ≤ q · N^{-1/s}` and `N^{-1/s} ≤ q^{-K}` for `q^{sK} ≤ N < q^{s(K+1)}`. -/
lemma level_pow (hq : 2 ≤ q) (hs : 1 ≤ s) (K N : ℕ) (hlo : q ^ (s * K) ≤ N)
    (hhi : N < q ^ (s * (K + 1))) :
    ((q : ℝ) ^ (K + 1))⁻¹ ≤ (N : ℝ) ^ (-(1 / (s : ℝ))) ∧ (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ ((q : ℝ) ^ K)⁻¹ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ (by omega)) hlo
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  constructor
  · have hroot : (N : ℝ) ^ (1 / (s : ℝ)) ≤ (q : ℝ) ^ (K + 1) := by
      have e1 : ((q : ℝ) ^ (K + 1)) = (((q : ℝ) ^ (K + 1)) ^ s) ^ ((s : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by positivity) (by omega)).symm
      rw [e1, one_div]
      apply Real.rpow_le_rpow hNpos.le _ (by positivity)
      rw [← pow_mul, mul_comm]
      exact_mod_cast hhi.le
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ (by positivity) hroot
  · have hroot : (q : ℝ) ^ K ≤ (N : ℝ) ^ (1 / (s : ℝ)) := by
      have e1 : ((q : ℝ) ^ K) = (((q : ℝ) ^ K) ^ s) ^ ((s : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (by positivity) (by omega)).symm
      rw [e1, one_div]
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      rw [← pow_mul, mul_comm]
      exact_mod_cast hlo
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ (by positivity) hroot

variable {R : Type*} [CommRing R] [NeZero q]

/-- **`lem:shift`, "in particular"**: let `(y(v))` be a digital `(0,s)`-sequence over the digit code `D`, `ς` any
array of digits, and suppose `lem:cert` gives `c(P_{sK}) ≥ LB` (`0 < LB ≤ 1`) for every `K` with `q^K ≥ 4`
(`CertAt`). Let `q^{K_0} ≥ 4`. Then the shifted sequence is a `(0,s)`-sequence, `c(P_{sK}) ≥ LB` for its full levels
with `q^K ≥ 4`, and for every `N > q^{s(K_0-1)}` the bounds of `lem:prefix` hold for it:
`δ(P_{[N]}) ≥ (LB/q) N^{-1/s}` (any two distinct points among the first `N`), `h(P_{[N]}) ≤ √s q N^{-1/s}` and
`h(P_{[N]}) ≤ (√s q/LB) · δ(P_{[N]})` (`h` Euclidean covering radius, `δ = 2 · sepRad` toroidal). -/
theorem shift_prefix [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (ς : Fin s → ℕ → R)
    (hq : 2 ≤ q) (hs : 1 ≤ s) (hseq : IsSeq0 D C) (LB : ℝ) (hLB0 : 0 < LB) (hLB1 : LB ≤ 1)
    (hcert : ∀ K : ℕ, 4 ≤ q ^ K → CertAt D C K LB) (K0 : ℕ) (hK0 : 4 ≤ q ^ K0) :
    IsSeq0Sh D C ς ∧ (∀ K : ℕ, 4 ≤ q ^ K → SepAtLevel q s K (shPoint D C ς) LB) ∧
    ∀ N : ℕ, q ^ (s * (K0 - 1)) < N →
      (∀ v w : ℕ, v < N → w < N → v ≠ w →
        LB / q * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ Z3NetDGS.torDist2 (shPoint D C ς v) (shPoint D C ς w)) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q / LB * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (shPoint D C ς))) := by
  have hsh : IsSeq0Sh D C ς := (shift_seq0 D C ς).2 hseq
  have hsep : ∀ K : ℕ, 4 ≤ q ^ K → SepAtLevel q s K (shPoint D C ς) LB := by
    intro K hK
    obtain ⟨j, Dr, hD0, hD, hLB⟩ := hcert K hK
    have := cert_shift D C ς K j hK (hseq (s * K) 0) Dr hD0 hD LB hLB
    rwa [min_eq_right hLB1] at this
  refine ⟨hsh, hsep, fun N hN => ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN1 : 1 ≤ N := (lt_of_le_of_lt (Nat.one_le_pow _ _ (by omega)) hN).le
  obtain ⟨hlo, hhi⟩ := level_of hq hs N hN1
  set K := Nat.log q N / s
  have hKK0 : K0 ≤ K + 1 := by
    by_contra h
    have : q ^ (s * (K + 1)) ≤ q ^ (s * (K0 - 1)) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left s (by omega))
    omega
  have hK4 : 4 ≤ q ^ (K + 1) := hK0.trans (Nat.pow_le_pow_right (by omega) hKK0)
  have hsepK := hsep (K + 1) hK4
  have hN2 : 2 ≤ N := by
    have : 1 ≤ q ^ (s * (K0 - 1)) := Nat.one_le_pow _ _ (by omega)
    omega
  obtain ⟨hpw1, hpw2⟩ := level_pow hq hs K N hlo hhi
  have hcov := shift_cov_level D C ς hq K hsh N hlo
  refine ⟨fun v w hv hw hvw => ?_, ?_, ?_⟩
  · have h1 := hsepK v w (hv.trans hhi) (hw.trans hhi) hvw
    calc LB / q * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ LB / q * ((q : ℝ) ^ K)⁻¹ :=
          mul_le_mul_of_nonneg_left hpw2 (div_nonneg hLB0.le hqpos.le)
      _ = LB / (q : ℝ) ^ (K + 1) := by rw [pow_succ]; field_simp
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; linarith
  · calc Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤ Real.sqrt s / (q : ℝ) ^ K := hcov
      _ = Real.sqrt s * q * ((q : ℝ) ^ (K + 1))⁻¹ := by rw [pow_succ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpw1 (by positivity)
  · have hsr := sepRad_ge_pt (shPoint D C ς) hq K N hN2 hhi LB hLB0 hsepK
    calc Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤ Real.sqrt s / (q : ℝ) ^ K := hcov
      _ = Real.sqrt s * q / LB * (LB / (q : ℝ) ^ (K + 1)) := by rw [pow_succ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsr (by positivity)

/-- **`lem:shift`, "for `q ≥ 4` this is every `N ≥ 2`"**: the bounds of `lem:prefix` hold for the shifted sequence
for every `N ≥ 2` (`K_0 = 1`). -/
theorem shift_prefix_q4 [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R)
    (ς : Fin s → ℕ → R) (hq : 4 ≤ q) (hs : 1 ≤ s) (hseq : IsSeq0 D C) (LB : ℝ) (hLB0 : 0 < LB)
    (hLB1 : LB ≤ 1) (hcert : ∀ K : ℕ, 1 ≤ K → CertAt D C K LB) (N : ℕ) (hN : 2 ≤ N) :
    (∀ v w : ℕ, v < N → w < N → v ≠ w →
        LB / q * (N : ℝ) ^ (-(1 / (s : ℝ))) ≤ Z3NetDGS.torDist2 (shPoint D C ς v) (shPoint D C ς w)) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q * (N : ℝ) ^ (-(1 / (s : ℝ))) ∧
      Z3NetDGS.covRad euclDist (prefixSet N (shPoint D C ς)) ≤
        Real.sqrt s * q / LB * (2 * Z3NetDGS.sepRad Z3NetDGS.torDist2 (prefixSet N (shPoint D C ς))) := by
  have hc : ∀ K : ℕ, 4 ≤ q ^ K → CertAt D C K LB := fun K hK => hcert K (by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hK
    · exact h)
  exact (shift_prefix D C ς (by omega) hs hseq LB hLB0 hLB1 hc 1 (by simpa using hq)).2.2 N
    (by simp; omega)

end Prefix

end GeoSeq
