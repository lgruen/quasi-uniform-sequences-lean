/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.SeqNet
public import GeoSeq.OneDigit

@[expose] public section

/-!
# GeoSeq stage S2: the certificate `lem:cert` in its point-set form

The proof of the paper, step by step:

* `nat_carry`: the base-`q` digits of `A` and of `(A+1) mod q^K` (a carry of length `L+1`; the torus
  wrap `A = q^K - 1` is the case `L = K-1`).
* `carry_digits`: hence the cell digits of a point in the next cell differ by
  `Δ(ȳ)` on the `l-1` finest digits and by `Δ(y)` at digit `K-l` (`rem:F4carry`), i.e. by the
  pattern `Δ(ȳ) carryPat(l-1) + Δ(y) (carryPat(l) - carryPat(l-1))`.
* `coord_split`: `q^K y_c = n_c + enc(R_c)/q^j + ε_c`, `0 ≤ ε_c ≤ q^{-j}` (`eq:cellunits`; the jitter
  is the digit tail, a `tsum` bound).
* `tor_far`, `tor_near`: toroidal distance in cell units.
* linearity of the level law (carry responses `IsCarryEntry`) gives `R'_c = R_c ⊕ σ_c`.
* `cert` (general digit code, `δ_i(l, y)` of `eq:carrychange`), `cert_prime` (`ℤ/qℤ`, `δ_i = D_i`).

The structure follows geo `lem:Ss` (`Z3NetF.Ss_coord`, `Ss_sep`): far cells give `1`; neighbouring
cells give the coordinatewise relaxation `f_j`.
-/

namespace GeoSeq

open Finset

/-! ## Digits of `A` and of `(A + 1) mod q^K` -/

lemma div_pow_succ' (A q t : ℕ) : A / q ^ (t + 1) = A / q / q ^ t := by
  rw [Nat.div_div_eq_div_mul, pow_succ', mul_comm]

/-- A carry in base `q`: the digits (position `t`, least significant first) of `A < q^K` and of
`B = (A+1) mod q^K` agree above a position `L < K`, `B_L = (A_L + 1) mod q`, and below `L` the digits
of `A` are `q-1` and those of `B` are `0`. -/
theorem nat_carry {q : ℕ} (hq : 2 ≤ q) (K : ℕ) (hK : 1 ≤ K) :
    ∀ A, A < q ^ K → ∃ L < K,
      (∀ t < L, A / q ^ t % q = q - 1 ∧ (A + 1) % q ^ K / q ^ t % q = 0) ∧
      (A + 1) % q ^ K / q ^ L % q = (A / q ^ L % q + 1) % q ∧
      ∀ t, L < t → t < K → (A + 1) % q ^ K / q ^ t % q = A / q ^ t % q := by
  induction K, hK using Nat.le_induction with
  | base =>
    intro A hA
    refine ⟨0, by omega, fun t ht => absurd ht (by omega), ?_, fun t h1 h2 => absurd h2 (by omega)⟩
    simp only [pow_one, pow_zero, Nat.div_one]
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (show A < q by simpa using hA)]
  | succ K hK ih =>
    intro A hA
    have hq0 : 0 < q := by omega
    by_cases hlast : A % q + 1 < q
    · -- no carry beyond the last digit
      have hAq : A + 1 < q ^ (K + 1) := by
        rcases Nat.lt_or_ge (A + 1) (q ^ (K + 1)) with h | h
        · exact h
        · exfalso
          have hA' : A = q ^ (K + 1) - 1 := by omega
          have : q ^ (K + 1) % q = 0 := by
            rw [pow_succ]; exact Nat.mul_mod_left _ _
          have h1 : (A + 1) % q = 0 := by rw [show A + 1 = q ^ (K + 1) by omega]; exact this
          have h2 : (A + 1) % q = A % q + 1 := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < q by omega), Nat.mod_eq_of_lt hlast]
          omega
      rw [Nat.mod_eq_of_lt hAq]
      have hdiv : (A + 1) / q = A / q := by
        rw [Nat.succ_div]
        have : ¬ q ∣ A + 1 := by
          intro hd
          have h1 := Nat.eq_zero_of_dvd_of_lt (a := q) (b := (A + 1) % q) ?_ ?_
          · rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < q by omega), Nat.mod_eq_of_lt hlast] at h1
            omega
          · exact (Nat.dvd_mod_iff (dvd_refl q)).mpr hd
          · exact Nat.mod_lt _ hq0
        simp [this]
      refine ⟨0, by omega, fun t ht => absurd ht (by omega), ?_, ?_⟩
      · simp only [pow_zero, Nat.div_one]
        rw [Nat.add_mod (A % q), Nat.mod_mod, ← Nat.add_mod]
      · intro t h1 _
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [div_pow_succ', div_pow_succ', hdiv]
    · -- the last digit is `q - 1`: recurse on `A / q`
      have hlast' : A % q = q - 1 := by have := Nat.mod_lt A hq0; omega
      have hA' : A / q < q ^ K := by
        rw [Nat.div_lt_iff_lt_mul hq0, ← pow_succ]; exact hA
      obtain ⟨L, hL, hlo, hmid, hhi⟩ := ih (A / q) hA'
      have hsplit : A + 1 = q * (A / q + 1) := by
        have := Nat.div_add_mod A q; rw [hlast'] at this
        rw [mul_add, mul_one]; omega
      have hB : (A + 1) % q ^ (K + 1) = q * ((A / q + 1) % q ^ K) := by
        rw [hsplit, pow_succ', Nat.mul_mod_mul_left]
      have hBdiv : (A + 1) % q ^ (K + 1) / q = (A / q + 1) % q ^ K := by
        rw [hB, Nat.mul_div_cancel_left _ hq0]
      refine ⟨L + 1, by omega, ?_, ?_, ?_⟩
      · intro t ht
        rcases t with _ | t'
        · refine ⟨by simpa using hlast', ?_⟩
          simp only [pow_zero, Nat.div_one]
          rw [hB]; exact Nat.mul_mod_right _ _
        · rw [div_pow_succ', div_pow_succ', hBdiv]
          exact hlo t' (by omega)
      · rw [div_pow_succ', div_pow_succ', hBdiv]
        exact hmid
      · intro t h1 h2
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [div_pow_succ', div_pow_succ', hBdiv]
        exact hhi t' (by omega) (by omega)

/-! ## Cell digits of a point in the next cell (`rem:F4carry`) -/

section Digits

variable {R : Type*} [CommRing R] {q : ℕ} [NeZero q]

omit [NeZero q] in
lemma eq_symm_of_enc (D : DigitCode R q) (y : R) (k : ℕ) (hk : k < q) (h : (D.enc y : ℕ) = k) :
    y = D.enc.symm ⟨k, hk⟩ := by
  rw [Equiv.eq_symm_apply]; exact Fin.ext h

lemma enc_symm_zero (D : DigitCode R q) : D.enc.symm ⟨0, NeZero.pos q⟩ = 0 := by
  rw [Equiv.symm_apply_eq]; exact Fin.ext D.enc_zero.symm

/-- `Δ(ȳ) = -ȳ`: the top digit goes to `0`. -/
lemma digInc_top (D : DigitCode R q) : digInc D (topDigit D) = -topDigit D := by
  unfold digInc
  have h1 : ((D.enc (topDigit D) : ℕ) + 1) % q = 0 := by
    unfold topDigit; rw [Equiv.apply_symm_apply]
    show (q - 1 + 1) % q = 0
    rw [Nat.sub_add_cancel (NeZero.pos q), Nat.mod_self]
  have : (⟨((D.enc (topDigit D) : ℕ) + 1) % q, Nat.mod_lt _ (NeZero.pos q)⟩ : Fin q) =
      ⟨0, NeZero.pos q⟩ := Fin.ext h1
  rw [this, enc_symm_zero, zero_sub]

/-- **The carry of a cell index** (`rem:F4carry`): if the cell index with digits `z` (most
significant first) is the successor modulo `q^K` of the one with digits `x`, there is a carry length
`l ∈ [1, K]` such that the digits change by `Δ(ȳ)` on the `l - 1` finest digits, by `Δ(x_{K-l})` at
digit `K - l`, and not at all above (the torus wrap is `l = K`). -/
theorem carry_digits (D : DigitCode R q) (hq : 2 ≤ q) (K : ℕ) (hK : 1 ≤ K) (x z : ℕ → R)
    (hcell : ∑ n : Fin K, (D.enc (z n) : ℕ) * q ^ (K - 1 - (n : ℕ)) =
      (∑ n : Fin K, (D.enc (x n) : ℕ) * q ^ (K - 1 - (n : ℕ)) + 1) % q ^ K) :
    ∃ l, 1 ≤ l ∧ l ≤ K ∧ ∀ n < K, z n - x n =
      digInc D (topDigit D) * (if K - (l - 1) ≤ n then 1 else 0) +
        digInc D (x (K - l)) * (if n = K - l then 1 else 0) := by
  change Z3Net.Proofs.digSum q K (fun n : Fin K => (D.enc (z n) : ℕ)) =
    (Z3Net.Proofs.digSum q K (fun n : Fin K => (D.enc (x n) : ℕ)) + 1) % q ^ K at hcell
  set A := Z3Net.Proofs.digSum q K (fun n : Fin K => (D.enc (x n) : ℕ)) with hA
  have hAlt : A < q ^ K := Z3Net.Proofs.digSum_lt q K _ (fun _ => (D.enc _).isLt)
  obtain ⟨L, hL, hlo, hmid, hhi⟩ := nat_carry hq K hK A hAlt
  refine ⟨L + 1, by omega, by omega, ?_⟩
  intro n hn
  have hx : (D.enc (x n) : ℕ) = A / q ^ (K - 1 - n) % q :=
    (Z3NetF.Proofs.digSum_digit (NeZero.pos q) K (fun n : Fin K => (D.enc (x n) : ℕ))
      (fun _ => (D.enc _).isLt) ⟨n, hn⟩).symm
  have hz : (D.enc (z n) : ℕ) = (A + 1) % q ^ K / q ^ (K - 1 - n) % q := by
    rw [← hcell]
    exact (Z3NetF.Proofs.digSum_digit (NeZero.pos q) K (fun n : Fin K => (D.enc (z n) : ℕ))
      (fun _ => (D.enc _).isLt) ⟨n, hn⟩).symm
  rcases lt_trichotomy (K - 1 - n) L with ht | ht | ht
  · obtain ⟨h1, h2⟩ := hlo _ ht
    have ex : x n = topDigit D := eq_symm_of_enc D _ _ _ (by rw [hx, h1])
    have ez : z n = 0 := by rw [eq_symm_of_enc D (z n) 0 (NeZero.pos q) (by rw [hz, h2]), enc_symm_zero]
    rw [if_pos (by omega), if_neg (by omega), ex, ez, digInc_top]; ring
  · have hnl : n = K - (L + 1) := by omega
    have ez : z n = D.enc.symm ⟨((D.enc (x n) : ℕ) + 1) % q, Nat.mod_lt _ (NeZero.pos q)⟩ :=
      eq_symm_of_enc D _ _ _ (by rw [hz, ht, hmid, hx, ht])
    rw [if_neg (by omega), if_pos hnl, ← hnl, ez]
    unfold digInc; ring
  · have ez : z n = x n := by
      apply D.enc.injective; apply Fin.ext
      rw [hz, hx, hhi _ ht (by omega)]
    rw [if_neg (by omega), if_neg (by omega), ez]; ring

end Digits

/-! ## The jitter: digit tail of the real point (`eq:cellunits`) -/

lemma pow_mul_div_lo {q : ℝ} (hq : q ≠ 0) (x : ℝ) {K n : ℕ} (hn : n < K) :
    q ^ K * (x / q ^ (n + 1)) = x * q ^ (K - 1 - n) := by
  have : q ^ K = q ^ (K - 1 - n) * q ^ (n + 1) := by rw [← pow_add]; congr 1; omega
  rw [this]; field_simp

lemma pow_mul_div_hi {q : ℝ} (hq : q ≠ 0) (x : ℝ) {K j i : ℕ} (hi : i < j) :
    q ^ K * (x / q ^ (K + i + 1)) = x * q ^ (j - 1 - i) / q ^ j := by
  have h1 : q ^ (K + i + 1) = q ^ K * q ^ (i + 1) := by rw [← pow_add]; congr 1
  have h2 : q ^ j = q ^ (j - 1 - i) * q ^ (i + 1) := by rw [← pow_add]; congr 1; omega
  rw [h1, h2]; field_simp

/-- **`eq:cellunits`**: for digits `a_n < q`, `q^K ∑_n a_n q^{-n-1} = n + enc(R)/q^j + ε` with
`n = ∑_{n<K} a_n q^{K-1-n}` (the cell), `enc(R) = ∑_{i<j} a_{K+i} q^{j-1-i}` (the `j` geometric
digits) and the jitter `0 ≤ ε ≤ q^{-j}` (the tail `∑_{n ≥ K+j} a_n q^{K-n-1}`). -/
theorem coord_split {q : ℕ} (hq : 2 ≤ q) (a : ℕ → ℕ) (ha : ∀ n, a n < q) (K j : ℕ) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / (q : ℝ) ^ j ∧
      (q : ℝ) ^ K * ∑' n, (a n : ℝ) / (q : ℝ) ^ (n + 1) =
        ((∑ n : Fin K, a n * q ^ (K - 1 - (n : ℕ)) : ℕ) : ℝ) +
          ((∑ i : Fin j, a (K + i) * q ^ (j - 1 - (i : ℕ)) : ℕ) : ℝ) / (q : ℝ) ^ j + ε := by
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hqpos : (0 : ℝ) < q := by positivity
  set f : ℕ → ℝ := fun n => (a n : ℝ) / (q : ℝ) ^ (n + 1) with hf
  set g : ℕ → ℝ := fun n => ((q : ℝ) - 1) / (q : ℝ) ^ (n + 1) with hg
  have hr0 : (0 : ℝ) ≤ 1 / q := by positivity
  have hr1 : (1 : ℝ) / q < 1 := by rw [div_lt_one hqpos]; linarith
  have hg_eq : ∀ M n, g (n + M) = ((q : ℝ) - 1) / (q : ℝ) ^ (M + 1) * (1 / q) ^ n := by
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
    have : a n + 1 ≤ q := ha n
    have : (a n : ℝ) + 1 ≤ q := by exact_mod_cast this
    linarith
  have hfs : Summable f :=
    Summable.of_nonneg_of_le hf0 hfg (by simpa using hgs 0)
  set M := K + j with hM
  have hsplit := hfs.sum_add_tsum_nat_add M
  set T := ∑' i, f (i + M) with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun i => hf0 _
  have hTle : T ≤ 1 / (q : ℝ) ^ M := by
    have h1 : T ≤ ∑' i, g (i + M) :=
      Summable.tsum_le_tsum (fun i => hfg _) ((summable_nat_add_iff M).mpr hfs) (hgs M)
    have h2 : ∑' i, g (i + M) = 1 / (q : ℝ) ^ M := by
      simp_rw [hg_eq M]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      have : (q : ℝ) - 1 ≠ 0 := by linarith
      rw [pow_succ]
      field_simp
    linarith
  refine ⟨(q : ℝ) ^ K * T, by positivity, ?_, ?_⟩
  · calc (q : ℝ) ^ K * T ≤ (q : ℝ) ^ K * (1 / (q : ℝ) ^ M) :=
          mul_le_mul_of_nonneg_left hTle (by positivity)
      _ = 1 / (q : ℝ) ^ j := by rw [hM, pow_add]; field_simp
  · rw [← hsplit, Finset.sum_range_add, mul_add, mul_add]
    congr 1
    congr 1
    · push_cast
      rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun n => (q : ℝ) ^ K * f n) K]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact pow_mul_div_lo hq0 _ n.isLt
    · push_cast
      rw [Finset.mul_sum, Finset.sum_div, ← Fin.sum_univ_eq_sum_range (fun i => (q : ℝ) ^ K * f (K + i)) j]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hf]
      rw [show K + (i : ℕ) + 1 = K + (i : ℕ) + 1 from rfl]
      exact pow_mul_div_hi hq0 _ i.isLt

/-! ## Toroidal distance in cell units -/

/-- Cells at least two apart on the torus (`2 ≤ |b - a| ≤ Q - 2`) give a coordinate gap `≥ 1` cell. -/
theorem tor_far {Q y y' a b u u' : ℝ} (hQ : 0 < Q) (hya : Q * y = a + u) (hyb : Q * y' = b + u')
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hu0' : 0 ≤ u') (hu1' : u' ≤ 1)
    (h2 : 2 ≤ |b - a|) (hQ2 : |b - a| ≤ Q - 2) :
    1 ≤ Q * Z3NetDGS.torCoord y y' := by
  unfold Z3NetDGS.torCoord
  rw [mul_min_of_nonneg _ _ hQ.le]
  have h0 : Q * (y - y') = (a - b) + (u - u') := by rw [mul_sub]; linarith
  have h1 : Q * |y - y'| = |(a - b) + (u - u')| := by
    rw [← h0, abs_mul, abs_of_pos hQ]
  rw [mul_sub, mul_one, h1]
  apply le_min <;> rcases abs_cases (b - a) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    rcases abs_cases ((a - b) + (u - u')) with ⟨hc, _⟩ | ⟨hc, _⟩ <;> linarith

/-- Neighbouring cells (`b - a ≡ e (mod Q)`, `e ∈ {-1,0,1}`), `Q ≥ 4`: the coordinate gap in cell
units is at least `|e + u' - u|` (the difference is at most `2 ≤ Q/2`, so it is the toroidal one). -/
theorem tor_near {Q y y' a b u u' e : ℝ} (hQ : 4 ≤ Q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hy0' : 0 ≤ y')
    (hy1' : y' ≤ 1) (hya : Q * y = a + u) (hyb : Q * y' = b + u')
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hu0' : 0 ≤ u') (hu1' : u' ≤ 1) (he : |e| ≤ 1)
    (hk : b - a - e = 0 ∨ b - a - e = Q ∨ b - a - e = -Q) :
    |e + u' - u| ≤ Q * Z3NetDGS.torCoord y y' := by
  unfold Z3NetDGS.torCoord
  have hQ0 : 0 < Q := by linarith
  rw [mul_min_of_nonneg _ _ hQ0.le]
  have h1 : Q * |y - y'| = |Q * y - Q * y'| := by
    rw [← mul_sub, abs_mul, abs_of_pos hQ0]
  rw [mul_sub, mul_one, h1, hya, hyb]
  have he' := abs_le.mp he
  have hQy : Q * y ≤ Q := by nlinarith
  have hQy' : Q * y' ≤ Q := by nlinarith
  have hQy0 : 0 ≤ Q * y := by positivity
  have hQy0' : 0 ≤ Q * y' := by positivity
  rw [hya] at hQy hQy0; rw [hyb] at hQy' hQy0'
  apply le_min <;> rcases hk with hk | hk | hk <;>
    rcases abs_cases (e + u' - u) with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
    rcases abs_cases (a + u - (b + u')) with ⟨hd, _⟩ | ⟨hd, _⟩ <;> linarith

/-- The coordinatewise relaxation: with `u = E/Q_j + ε`, `u' = E'/Q_j + ε'`, jitters in `[0, 1/Q_j]`
and `N ≤ |e Q_j + E' - E|`, the gap is at least `(N - 1)/Q_j` (`f_j` of `lem:cert`). -/
theorem gap_bound {Qj : ℝ} (hQj : 0 < Qj) (e E E' ε ε' : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / Qj)
    (hε0' : 0 ≤ ε') (hε1' : ε' ≤ 1 / Qj) (N : ℕ) (hN : (N : ℝ) ≤ |e * Qj + E' - E|) :
    ((N - 1 : ℕ) : ℝ) / Qj ≤ |e + (E' / Qj + ε') - (E / Qj + ε)| := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp only [Nat.zero_sub, Nat.cast_zero, zero_div]; exact abs_nonneg _
  rw [Nat.cast_sub hpos, Nat.cast_one, div_le_iff₀ hQj]
  have key : (e + (E' / Qj + ε') - (E / Qj + ε)) * Qj = (e * Qj + E' - E) + (ε' - ε) * Qj := by
    field_simp; ring
  have hd1 : (ε' - ε) * Qj ≤ 1 := by
    have : ε' * Qj ≤ 1 := by rw [le_div_iff₀ hQj] at hε1'; linarith
    nlinarith
  have hd2 : -1 ≤ (ε' - ε) * Qj := by
    have : ε * Qj ≤ 1 := by rw [le_div_iff₀ hQj] at hε1; linarith
    nlinarith
  have h3 : |e + (E' / Qj + ε') - (E / Qj + ε)| * Qj =
      |(e * Qj + E' - E) + (ε' - ε) * Qj| := by
    rw [← key, abs_mul, abs_of_pos hQj]
  rw [h3]
  rcases abs_cases (e * Qj + E' - E) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
    rcases abs_cases ((e * Qj + E' - E) + (ε' - ε) * Qj) with ⟨h5, _⟩ | ⟨h5, _⟩ <;> linarith

/-- `Q · √(∑ t_c²) = √(∑ (Q t_c)²)` for `Q ≥ 0`. -/
lemma mul_sqrt_sum {s : ℕ} {Q : ℝ} (hQ : 0 ≤ Q) (t : Fin s → ℝ) :
    Q * Real.sqrt (∑ c, t c ^ 2) = Real.sqrt (∑ c, (Q * t c) ^ 2) := by
  have : ∑ c, (Q * t c) ^ 2 = Q ^ 2 * ∑ c, t c ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hQ]

/-! ## Linearity of the level law -/

section Linear

variable {R : Type*} [CommRing R] {s : ℕ}

lemma vecDigit_add {m : ℕ} (C : Gen s R) (V W : Fin m → R) (c : Fin s) (n : ℕ) :
    vecDigit C (V + W) c n = vecDigit C V c n + vecDigit C W c n := by
  unfold vecDigit; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp [mul_add]

lemma vecDigit_sub {m : ℕ} (C : Gen s R) (V W : Fin m → R) (c : Fin s) (n : ℕ) :
    vecDigit C (V - W) c n = vecDigit C V c n - vecDigit C W c n := by
  unfold vecDigit; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp [mul_sub]

lemma vecDigit_zero {m : ℕ} (C : Gen s R) (c : Fin s) (n : ℕ) :
    vecDigit C (0 : Fin m → R) c n = 0 := by
  simp [vecDigit]

lemma vecDigit_comb {m : ℕ} (C : Gen s R) (α β : Fin s → R) (X Y : Fin s → Fin m → R)
    (c : Fin s) (n : ℕ) :
    vecDigit C (fun k => ∑ c', (α c' * X c' k + β c' * (Y c' k - X c' k))) c n =
      ∑ c', (α c' * vecDigit C (X c') c n +
        β c' * (vecDigit C (Y c') c n - vecDigit C (X c') c n)) := by
  unfold vecDigit
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end Linear

/-! ## The carry responses and the step of the law -/

section Law

variable {R : Type*} [CommRing R] {s : ℕ}

lemma carryPat_ne (K l : ℕ) {c' c : Fin s} (h : c ≠ c') (n : ℕ) : (carryPat K l c' c n : R) = 0 := by
  unfold carryPat; rw [if_neg (fun h' => h h'.1)]

lemma carryPat_self (K l : ℕ) (c : Fin s) {n : ℕ} (hn : n < K) :
    (carryPat K l c c n : R) = if K - l ≤ n then 1 else 0 := by
  unfold carryPat; simp [hn]

lemma carryPat_diff {K l : ℕ} (hl : 1 ≤ l) (hlK : l ≤ K) (c : Fin s) {n : ℕ} (hn : n < K) :
    (carryPat K l c c n : R) - carryPat K (l - 1) c c n = if n = K - l then 1 else 0 := by
  rw [carryPat_self K l c hn, carryPat_self K (l - 1) c hn]
  split_ifs <;> first | (exfalso; omega) | simp

/-- **The step of the level law** (linearity, `sec:law`): if the cell digits of an index vector `Vd`
are the combination `∑_{c'} (a_{c'} carryPat(l_{c'}-1) + b_{c'} (carryPat(l_{c'}) - carryPat(l_{c'}-1)))`
of carry patterns, its geometric digit `K+i` of coordinate `c` is the same combination of the carry
responses `D_i(l)` (`IsCarryEntry`; `D_i(0) = 0`). -/
theorem law_step (C : Gen s R) (K j : ℕ) (hK1 : 1 ≤ K) (Dr : ℕ → ℕ → Fin s → Fin s → R)
    (hD0 : ∀ i c c', Dr i 0 c c' = 0)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (i : ℕ) (hi : i < j) (c : Fin s) (Vd : Fin (s * K) → R) (a b : Fin s → R) (l : Fin s → ℕ)
    (hl : ∀ c, 1 ≤ l c ∧ l c ≤ K)
    (hcellD : ∀ c₁, ∀ n < K, vecDigit C Vd c₁ n = ∑ c', (a c' * carryPat K (l c' - 1) c' c₁ n +
      b c' * (carryPat K (l c') c' c₁ n - carryPat K (l c' - 1) c' c₁ n))) :
    vecDigit C Vd c (K + i) =
      ∑ c', (a c' * Dr i (l c' - 1) c c' + b c' * (Dr i (l c') c c' - Dr i (l c' - 1) c c')) := by
  classical
  let wit : ℕ → Fin s → Fin (s * K) → R := fun l' c' =>
    if h : 1 ≤ l' ∧ l' ≤ K then Classical.choose (hD i hi l' h.1 h.2 c c').1 else 0
  have wit_cell : ∀ l' ≤ K, ∀ c' c₁, ∀ n < K, vecDigit C (wit l' c') c₁ n = carryPat K l' c' c₁ n := by
    intro l' hl' c' c₁ n hn
    by_cases h : 1 ≤ l' ∧ l' ≤ K
    · simp only [wit, dif_pos h]
      exact Classical.choose_spec (hD i hi l' h.1 h.2 c c').1 c₁ n hn
    · simp only [wit, dif_neg h, vecDigit_zero]
      unfold carryPat
      rw [if_neg (by rintro ⟨_, h1, h2⟩; omega)]
  have wit_geo : ∀ l' ≤ K, ∀ c', vecDigit C (wit l' c') c (K + i) = Dr i l' c c' := by
    intro l' hl' c'
    by_cases h : 1 ≤ l' ∧ l' ≤ K
    · simp only [wit, dif_pos h]
      exact (hD i hi l' h.1 h.2 c c').2 _ (Classical.choose_spec (hD i hi l' h.1 h.2 c c').1)
    · simp only [wit, dif_neg h, vecDigit_zero]
      rw [show l' = 0 by omega, hD0]
  set W' : Fin (s * K) → R := fun k => ∑ c', (a c' * wit (l c' - 1) c' k +
    b c' * (wit (l c') c' k - wit (l c' - 1) c' k)) with hW'
  have hW'cell : ∀ c₁, ∀ n < K, vecDigit C W' c₁ n = vecDigit C Vd c₁ n := by
    intro c₁ n hn
    rw [hW', vecDigit_comb, hcellD c₁ n hn]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [wit_cell _ (by have := hl c'; omega) c' c₁ n hn, wit_cell _ (hl c').2 c' c₁ n hn]
  have hU : ∀ c₁, ∀ n < K, vecDigit C (Vd - W') c₁ n = 0 := by
    intro c₁ n hn; rw [vecDigit_sub, hW'cell c₁ n hn, sub_self]
  have h1 : vecDigit C (wit 1 c + (Vd - W')) c (K + i) = Dr i 1 c c :=
    (hD i hi 1 le_rfl hK1 c c).2 _ (fun c₁ n hn => by
      rw [vecDigit_add, hU c₁ n hn, add_zero, wit_cell 1 hK1 c c₁ n hn])
  rw [vecDigit_add, wit_geo 1 hK1 c, add_eq_left, vecDigit_sub, sub_eq_zero] at h1
  rw [h1, hW', vecDigit_comb]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [wit_geo _ (by have := hl c'; omega) c', wit_geo _ (hl c').2 c']

end Law

/-! ## Neighbouring cells of two points -/

section Cells

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

lemma seqDigit_vec (D : DigitCode R q) (C : Gen s R) {M x : ℕ} (hx : x < q ^ M) (c : Fin s) (n : ℕ) :
    seqDigit D C x c n = vecDigit C (fun k : Fin M => idxDigit D x k) c n := by
  rw [seqDigit_eq_range D C x c n M (fun k hk => idxDigit_eq_zero D x k
    (digit_high x k (hx.trans_le (Nat.pow_le_pow_right (NeZero.pos q) hk))))]
  unfold vecDigit
  exact (Fin.sum_univ_eq_sum_range (fun k => C c n k * idxDigit D x k) M).symm

lemma cell_lt (D : DigitCode R q) (C : Gen s R) (x : ℕ) (c : Fin s) (K : ℕ) :
    cellIdx D C x c K < q ^ K :=
  Z3Net.Proofs.digSum_lt q K _ (fun _ => (D.enc _).isLt)

lemma cell_digit (D : DigitCode R q) (C : Gen s R) (x : ℕ) (c : Fin s) (K n : ℕ) (hn : n < K) :
    (D.enc (seqDigit D C x c n) : ℕ) = cellIdx D C x c K / q ^ (K - 1 - n) % q :=
  (Z3NetF.Proofs.digSum_digit (NeZero.pos q) K (fun n : Fin K => (D.enc (seqDigit D C x c n) : ℕ))
    (fun _ => (D.enc _).isLt) ⟨n, hn⟩).symm

/-- **Classification of one coordinate** (proof of `lem:cert`): the cells of two points are either at
toroidal distance `≥ 2`, or neighbours `n' ≡ n + e (mod q^K)` with `e ∈ {-1,0,1}`; in the second case
the cell digits change by `e` times the carry pattern of a carry length `l ∈ [1, K]` stopping at a
digit `y` (`carry_digits`, applied from the lower cell). -/
theorem coord_class (D : DigitCode R q) (hq : 2 ≤ q) (C : Gen s R) (K : ℕ) (hK : 1 ≤ K) (v w : ℕ)
    (c : Fin s) :
    (2 ≤ |(cellIdx D C w c K : ℝ) - cellIdx D C v c K| ∧
      |(cellIdx D C w c K : ℝ) - cellIdx D C v c K| ≤ (q : ℝ) ^ K - 2) ∨
    ∃ e : ℤ, ∃ l : ℕ, ∃ y : R, (-1 ≤ e ∧ e ≤ 1) ∧ (1 ≤ l ∧ l ≤ K) ∧
      ((cellIdx D C w c K : ℝ) - cellIdx D C v c K - e = 0 ∨
        (cellIdx D C w c K : ℝ) - cellIdx D C v c K - e = (q : ℝ) ^ K ∨
        (cellIdx D C w c K : ℝ) - cellIdx D C v c K - e = -(q : ℝ) ^ K) ∧
      (e = 0 → cellIdx D C w c K = cellIdx D C v c K) ∧
      ∀ n < K, seqDigit D C w c n - seqDigit D C v c n = (e : R) *
        (digInc D (topDigit D) * (if K - (l - 1) ≤ n then 1 else 0) +
          digInc D y * (if n = K - l then 1 else 0)) := by
  set a := cellIdx D C v c K with ha
  set b := cellIdx D C w c K with hb
  have hav : a < q ^ K := cell_lt D C v c K
  have hbw : b < q ^ K := cell_lt D C w c K
  have hQ : ((q ^ K : ℕ) : ℝ) = (q : ℝ) ^ K := by push_cast; ring
  have hcases : b = a ∨ (b = a + 1 ∨ (a + 1 = q ^ K ∧ b = 0)) ∨ (a = b + 1 ∨ (b + 1 = q ^ K ∧ a = 0)) ∨
      (a + 2 ≤ b ∧ b + 2 ≤ a + q ^ K) ∨ (b + 2 ≤ a ∧ a + 2 ≤ b + q ^ K) := by omega
  rcases hcases with h | h | h | h | h
  · -- same cell
    right
    refine ⟨0, 1, 0, by omega, ⟨le_rfl, hK⟩, Or.inl (by rw [h]; simp), fun _ => h, ?_⟩
    intro n hn
    have : seqDigit D C w c n = seqDigit D C v c n := by
      apply D.enc.injective; apply Fin.ext
      rw [cell_digit D C w c K n hn, cell_digit D C v c K n hn, ← hb, ← ha, h]
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
    obtain ⟨l, hl1, hl2, hdig⟩ := carry_digits D hq K hK (fun n => seqDigit D C v c n)
      (fun n => seqDigit D C w c n) hmod
    refine ⟨1, l, seqDigit D C v c (K - l), by omega, ⟨hl1, hl2⟩, ?_, fun h => absurd h (by omega), ?_⟩
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
    obtain ⟨l, hl1, hl2, hdig⟩ := carry_digits D hq K hK (fun n => seqDigit D C w c n)
      (fun n => seqDigit D C v c n) hmod
    refine ⟨-1, l, seqDigit D C w c (K - l), by omega, ⟨hl1, hl2⟩, ?_, fun h => absurd h (by omega), ?_⟩
    · rcases h with h | ⟨h1, h2⟩
      · left; rw [h]; push_cast; ring
      · right; left
        have : (b : ℝ) + 1 = (q : ℝ) ^ K := by rw [← hQ, ← h1]; push_cast; ring
        rw [h2]; push_cast; linarith
    · intro n hn
      have := hdig n hn
      rw [← neg_sub, this]; push_cast; ring

end Cells

/-! ## `lem:cert` -/

section Main

variable {R : Type*} [CommRing R] {q s : ℕ} [NeZero q]

/-- **`lem:cert`** (certificate, general digit code; `δ_i(l, y)` of `eq:carrychange`). Let the prefix
`P_{sK}` be a `(0, sK, s)`-net in base `q` with `q^K ≥ 4`, let `Dr i l = D_i(l)` be its carry responses
for `i < j`, `1 ≤ l ≤ K` (`IsCarryEntry`, with `D_i(0) = 0`), and let `LB` be at most every certificate
term `(∑_c f_j(e_c, σ_c)²)^{1/2}` over all steps `e ∈ {-1,0,1}^s \ {0}`, carry lengths `l_c ∈ [1, K]` and
stop digits `y_c` (`σ_c = certSigma`). Then `c(P_{sK}) ≥ min(1, LB)`: any two distinct points of
`P_{sK}` have toroidal distance at least `min(1, LB) · q^{-K}`. -/
theorem cert [Fintype R] [DecidableEq R] (D : DigitCode R q) (C : Gen s R) (K j : ℕ)
    (hK : 4 ≤ q ^ K) (hnet : BlockNet0 D C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → R)
    (hD0 : ∀ i c c', Dr i 0 c c' = 0)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ)
    (hLB : ∀ e l, IsStep K e l → ∀ y : Fin s → R, LB ≤ certTerm D j e (certSigma D Dr j e l y)) :
    SepAtLevel q s K (seqPoint D C) (min 1 LB) := by
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
      (q : ℝ) ^ K * seqCoord D C x c = (cellIdx D C x c K : ℝ) +
        (encVec D (fun i : Fin j => seqDigit D C x c (K + i)) : ℝ) / (q : ℝ) ^ j + ε :=
    fun x c => coord_split hq2 (fun n => (D.enc (seqDigit D C x c n) : ℕ)) (fun _ => (D.enc _).isLt) K j
  choose ε hε0 hε1 hεeq0 using hsplit
  have hεeq : ∀ x c, (q : ℝ) ^ K * seqCoord D C x c = (cellIdx D C x c K : ℝ) +
      ((encVec D (fun i : Fin j => seqDigit D C x c (K + i)) : ℝ) / (q : ℝ) ^ j + ε x c) :=
    fun x c => by rw [hεeq0]; ring
  set E : ℕ → Fin s → ℕ := fun x c => encVec D (fun i : Fin j => seqDigit D C x c (K + i)) with hEdef
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
  have hcellQ : ∀ x c, (cellIdx D C x c K : ℝ) + 1 ≤ (q : ℝ) ^ K := by
    intro x c
    have : cellIdx D C x c K + 1 ≤ q ^ K := cell_lt D C x c K
    exact_mod_cast this
  have hy : ∀ x c, 0 ≤ seqCoord D C x c ∧ seqCoord D C x c ≤ 1 := by
    intro x c
    have h := hεeq x c
    have h0 := hu0 x c; have h1 := hu1 x c; have h2 := hcellQ x c
    have h3 : (0 : ℝ) ≤ cellIdx D C x c K := Nat.cast_nonneg _
    constructor
    · by_contra hn; push_neg at hn
      have : (q : ℝ) ^ K * seqCoord D C x c < 0 := mul_neg_of_pos_of_neg hQpos hn
      linarith
    · by_contra hn; push_neg at hn
      have : (q : ℝ) ^ K < (q : ℝ) ^ K * seqCoord D C x c := by nlinarith
      linarith
  -- the goal in cell units
  show min 1 LB ≤ (q : ℝ) ^ K * Z3NetDGS.torDist2 (seqPoint D C v) (seqPoint D C w)
  rw [show Z3NetDGS.torDist2 (seqPoint D C v) (seqPoint D C w) =
    Real.sqrt (∑ c, Z3NetDGS.torCoord (seqCoord D C v c) (seqCoord D C w c) ^ 2) from rfl,
    mul_sqrt_sum hQpos.le]
  by_cases hfar : ∃ c, 2 ≤ |(cellIdx D C w c K : ℝ) - cellIdx D C v c K| ∧
      |(cellIdx D C w c K : ℝ) - cellIdx D C v c K| ≤ (q : ℝ) ^ K - 2
  · -- cells at least two apart in some coordinate: distance `≥ 1` cell
    obtain ⟨c0, h1, h2⟩ := hfar
    have hc0 := tor_far hQpos (hεeq v c0) (hεeq w c0) (hu0 v c0) (hu1 v c0) (hu0 w c0) (hu1 w c0) h1 h2
    apply min_le_of_left_le
    calc (1 : ℝ) ≤ (q : ℝ) ^ K * Z3NetDGS.torCoord (seqCoord D C v c0) (seqCoord D C w c0) := hc0
      _ = Real.sqrt (((q : ℝ) ^ K *
            Z3NetDGS.torCoord (seqCoord D C v c0) (seqCoord D C w c0)) ^ 2) :=
          (Real.sqrt_sq (by linarith)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun c => ((q : ℝ) ^ K *
            Z3NetDGS.torCoord (seqCoord D C v c) (seqCoord D C w c)) ^ 2)
            (fun c _ => sq_nonneg _) (Finset.mem_univ c0))
  · -- neighbouring cells: a step `e` with carry lengths `l` and stop digits `y`
    push_neg at hfar
    have hnear := fun c => (coord_class D hq2 C K hK1 v w c).resolve_left
      (fun h => absurd h.2 (not_le.mpr (hfar c h.1)))
    choose e l y he hl hk h0 hdig using hnear
    have hne : ∃ c, e c ≠ 0 := by
      by_contra hall; push_neg at hall
      apply hvw
      obtain ⟨x, _, hxu⟩ := hnet (fun _ => K) (by simp)
        (fun c => cellIdx D C v c K) (fun c => cell_lt D C v c K)
      have hvx := hxu v ⟨⟨by simp, by simpa using hv⟩, fun c => rfl⟩
      have hwx := hxu w ⟨⟨by simp, by simpa using hw⟩, fun c => h0 c (hall c)⟩
      rw [hvx, hwx]
    have hstep : IsStep K e l := ⟨he, hne, hl⟩
    -- the geometric digits: `R'_c = R_c ⊕ σ_c` (linearity of the law)
    have hgeo : ∀ c (i : Fin j), seqDigit D C w c (K + i) =
        seqDigit D C v c (K + i) + certSigma D Dr j e l y c i := by
      intro c i
      have hv' : v < q ^ (s * K) := hv
      have hw' : w < q ^ (s * K) := hw
      set Vd : Fin (s * K) → R :=
        (fun k : Fin (s * K) => idxDigit D w k) - fun k : Fin (s * K) => idxDigit D v k with hVd
      have hdigV : ∀ c₁ n, vecDigit C Vd c₁ n = seqDigit D C w c₁ n - seqDigit D C v c₁ n := by
        intro c₁ n
        rw [hVd, vecDigit_sub, ← seqDigit_vec D C hw', ← seqDigit_vec D C hv']
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
        (q : ℝ) ^ K * Z3NetDGS.torCoord (seqCoord D C v c) (seqCoord D C w c) := by
      intro c
      set r : Fin j → R := fun i => seqDigit D C v c (K + i) with hr
      have hrw : (fun i : Fin j => seqDigit D C w c (K + i)) = r + certSigma D Dr j e l y c := by
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
      have hk' : (cellIdx D C w c K : ℝ) - cellIdx D C v c K - (e c : ℝ) = 0 ∨
          (cellIdx D C w c K : ℝ) - cellIdx D C v c K - (e c : ℝ) = (q : ℝ) ^ K ∨
          (cellIdx D C w c K : ℝ) - cellIdx D C v c K - (e c : ℝ) = -(q : ℝ) ^ K := hk c
      exact tor_near hQ4 (hy v c).1 (hy v c).2 (hy w c).1 (hy w c).2 (hεeq v c) (hεeq w c)
        (hu0 v c) (hu1 v c) (hu0 w c) (hu1 w c) he1 hk'
    apply min_le_of_right_le
    refine (hLB e l hstep y).trans ?_
    unfold certTerm
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun c _ => ?_
    exact pow_le_pow_left₀ (by positivity) (hgap c) 2

/-- For `ℤ/qℤ` with `enc = val`, every step adds `1` to the digits it changes: `Δ ≡ 1`. -/
lemma digInc_zcode (q : ℕ) [NeZero q] (y : ZMod q) : digInc (zcode q) y = 1 := by
  show (((y.val + 1) % q : ℕ) : ZMod q) - y = 1
  rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_zmod_val]; ring

/-- **`lem:cert`, prime `q`** (`ℤ/qℤ`, `enc = val`; the statement holds for every `q`, the paper uses
it for prime `q = p`, where `ℤ/pℤ = 𝔽_p`): with the carry responses `Dr i l = D_i(l)`
(`i < j`, `1 ≤ l ≤ K`) of a `(0, sK, s)`-net `P_{sK}`, `q^K ≥ 4`, and `LB` at most every term
`(∑_c f_j(e_c, σ_c)²)^{1/2}`, `σ_{c,i} = ∑_{c'} e_{c'} D_i(l_{c'})[c][c']`, over all steps `e` and carry
lengths `l_c ∈ [1, K]`: `c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_prime {q s : ℕ} [NeZero q] (C : Gen s (ZMod q)) (K j : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ i < j, ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K i l c c' (Dr i l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l → LB ≤ certTerm (zcode q) j e (certSigmaP Dr j e l)) :
    SepAtLevel q s K (seqPoint (zcode q) C) (min 1 LB) := by
  classical
  set Dr' : ℕ → ℕ → Fin s → Fin s → ZMod q := fun i l c c' => if l = 0 then 0 else Dr i l c c'
    with hDr'
  refine cert (zcode q) C K j hK hnet Dr' (fun i c c' => by simp [hDr']) ?_ LB ?_
  · intro i hi l hl hlK c c'
    have : Dr' i l c c' = Dr i l c c' := by simp [hDr', show l ≠ 0 by omega]
    rw [this]; exact hD i hi l hl hlK c c'
  · intro e l hst y
    have hσ : certSigma (zcode q) Dr' j e l y = certSigmaP Dr j e l := by
      funext c i
      unfold certSigma certSigmaP carryChange
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [digInc_zcode, digInc_zcode]
      have : Dr' i (l c') c c' = Dr i (l c') c c' := by
        simp [hDr', show l c' ≠ 0 by have := hst.2.2 c'; omega]
      rw [this]; ring
    rw [hσ]; exact hLB e l hst

/-- **`lem:cert` with one geometric digit** (`j = 1`, `ℤ/qℤ`; the form used by `thm:WF`, `thm:GA`,
`lem:dom` together with `rem:onedigit`): with the one-digit responses `Dr l = D(l)` (`1 ≤ l ≤ K`) and
`LB` at most every `(∑_c f_1(e_c, σ_c)²)^{1/2}`, `σ_c = ∑_{c'} e_{c'} D(l_{c'})[c][c']`,
`c(P_{sK}) ≥ min(1, LB)`. -/
theorem cert_one {q s : ℕ} [NeZero q] (C : Gen s (ZMod q)) (K : ℕ) (hK : 4 ≤ q ^ K)
    (hnet : BlockNet0 (zcode q) C (s * K) 0) (Dr : ℕ → Fin s → Fin s → ZMod q)
    (hD : ∀ l, 1 ≤ l → l ≤ K → ∀ c c', IsCarryEntry C K 0 l c c' (Dr l c c'))
    (LB : ℝ) (hLB : ∀ e l, IsStep K e l →
      LB ≤ Real.sqrt (∑ c, ((gapNum1 q (e c) (∑ c', (e c' : ZMod q) * Dr (l c') c c') : ℝ) / q) ^ 2)) :
    SepAtLevel q s K (seqPoint (zcode q) C) (min 1 LB) := by
  refine cert_prime C K 1 hK hnet (fun _ l c c' => Dr l c c') ?_ LB ?_
  · intro i hi l hl hlK c c'
    obtain rfl : i = 0 := by omega
    exact hD l hl hlK c c'
  · intro e l hst
    refine (hLB e l hst).trans_eq ?_
    unfold certTerm
    simp only [gapNum_one, pow_one]
    rfl

end Main

end GeoSeq
