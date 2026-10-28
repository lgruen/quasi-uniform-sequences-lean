/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V2Defs

@[expose] public section

/-!
# GeoSeq stage V2: mixed-radix coverings (`lem:ws`, general `k`)

* `cdiv_*`: the ceiling `⌈a/b⌉`.
* `ws_step`: one row (an arc of `D` residues is reached from any residue in at most `⌈(p-D)/ν⌉` steps
  of size `ν ≤ D`).
* `ws_pos` (all steps positive) and **`ws_cover`** = `lem:ws`: for every `σ ∈ (ℤ/p)^k`, every run of `N_k`
  consecutive integers contains an `o` with `σ + o v ∈ I_1 × ⋯ × I_k` (rows indexed from `0` in Lean).
-/

namespace GeoSeq

lemma cdiv_mul_ge (a b : ℕ) (hb : 0 < b) : a ≤ cdiv a b * b := by
  unfold cdiv
  have := Nat.lt_div_mul_add (a := a + b - 1) hb
  omega

lemma cdiv_mul_le (a b : ℕ) : cdiv a b * b ≤ a + b - 1 := Nat.div_mul_le_self _ _

lemma cdiv_mono {a a' : ℕ} (b : ℕ) (h : a ≤ a') : cdiv a b ≤ cdiv a' b :=
  Nat.div_le_div_right (by omega)

lemma cdiv_pos (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ cdiv a b := by
  unfold cdiv
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

lemma cdiv_sub_self (p ν : ℕ) (h1 : 1 ≤ ν) (h2 : ν ≤ p) : cdiv (p - ν) ν + 1 = cdiv p ν := by
  unfold cdiv
  have e1 : p - ν + ν - 1 = p - 1 := by omega
  have e2 : p + ν - 1 = (p - 1) + ν := by omega
  rw [e1, e2, Nat.add_div_right _ (by omega)]

/-- One row of `lem:ws`: from any residue `y ∈ [0, p)`, steps of size `ν ≤ D ≤ p` reach the arc
`{0, …, D-1}` (mod `p`) after `i ≤ ⌈(p - D)/ν⌉` steps. -/
lemma ws_step (p ν D y : ℕ) (hν : 1 ≤ ν) (hνD : ν ≤ D) (hD : D ≤ p) (hy : y < p) :
    ∃ i : ℕ, i ≤ cdiv (p - D) ν ∧ ∃ r : ℕ, r < D ∧ ∃ m : ℕ, y + i * ν = r + m * p := by
  by_cases h : y < D
  · exact ⟨0, Nat.zero_le _, y, h, 0, by simp⟩
  · refine ⟨cdiv (p - y) ν, cdiv_mono ν (by omega), y + cdiv (p - y) ν * ν - p, ?_, 1, ?_⟩
    · have := cdiv_mul_le (p - y) ν; omega
    · have := cdiv_mul_ge (p - y) ν (by omega); omega

lemma arc_of (p : ℕ) (L : ℤ) (len r : ℕ) (hr : r < len) (x : ZMod p) (hx : x = ((L + r : ℤ) : ZMod p)) :
    x ∈ arc p L len := ⟨r, hr, hx⟩

lemma wsN_pos (p : ℕ) (hp : 1 ≤ p) (len ν : ℕ → ℕ) (t : ℕ) (hν : ∀ t', 1 ≤ t' → t' ≤ t → 1 ≤ ν t') :
    1 ≤ wsN p len ν t := by
  induction t with
  | zero => simp [wsN]
  | succ t ih =>
    simp only [wsN]
    have := ih (fun t' h1 h2 => hν t' h1 (by omega))
    have := cdiv_pos p (ν (t + 1)) hp (hν (t + 1) (by omega) le_rfl)
    omega

/-- **`lem:ws` with positive steps** `ν_t ≥ 1` (rows indexed from `0`). -/
theorem ws_pos (p : ℕ) [NeZero p] (k : ℕ) (hk : 1 ≤ k) (ν : ℕ → ℕ) (L : ℕ → ℤ) (len : ℕ → ℕ)
    (hlen : ∀ t < k, len t ≤ p) (hν : ∀ t < k, 1 ≤ ν t) (h1 : ν 0 ≤ len 0)
    (hN : ∀ t, t + 1 < k → wsN p len ν t * ν (t + 1) ≤ len (t + 1)) (σ : ℕ → ZMod p) (a : ℤ) :
    ∃ o : ℤ, a ≤ o ∧ o < a + wsN p len ν (k - 1) ∧
      ∀ t < k, σ t + (o : ZMod p) * (ν t : ZMod p) ∈ arc p (L t) (len t) := by
  have hp : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hNpos : ∀ t, t < k → 1 ≤ wsN p len ν t :=
    fun t ht => wsN_pos p hp len ν t (fun t' _ h2 => hν t' (by omega))
  have key : ∀ t, t < k → ∀ a : ℤ, ∃ o : ℤ, a ≤ o ∧ o < a + wsN p len ν t ∧
      ∀ r ≤ t, σ r + (o : ZMod p) * (ν r : ZMod p) ∈ arc p (L r) (len r) := by
    intro t
    induction t with
    | zero =>
      intro hk0 a
      set x : ZMod p := σ 0 + (a : ZMod p) * ν 0 - (L 0 : ZMod p)
      obtain ⟨i, hi, r, hr, m, hm⟩ := ws_step p (ν 0) (len 0) x.val (hν 0 hk0) h1 (hlen 0 hk0)
        (ZMod.val_lt x)
      refine ⟨a + i, by omega, ?_, fun r' hr' => ?_⟩
      · simp only [wsN]; push_cast; omega
      · obtain rfl : r' = 0 := by omega
        refine arc_of p (L 0) (len 0) r hr _ ?_
        have hc := congrArg (fun n : ℕ => (n : ZMod p)) hm
        simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id,
          ZMod.natCast_self, mul_zero, add_zero] at hc
        push_cast
        simp only [x] at hc
        linear_combination hc
    | succ t ih =>
      intro ht a
      have hNt := hNpos t (by omega)
      have hlt := hN t ht
      have hν1 := hν (t + 1) ht
      have hνp : ν (t + 1) ≤ p := by
        have := hlen (t + 1) ht
        have : ν (t + 1) ≤ wsN p len ν t * ν (t + 1) := Nat.le_mul_of_pos_left _ hNt
        omega
      set x : ZMod p := σ (t + 1) + (a : ZMod p) * ν (t + 1) - (L (t + 1) : ZMod p)
      obtain ⟨i, hi, r, hr, m, hm⟩ := ws_step p (ν (t + 1)) (ν (t + 1)) x.val hν1 le_rfl hνp
        (ZMod.val_lt x)
      have hcs := cdiv_sub_self p (ν (t + 1)) hν1 hνp
      obtain ⟨o, ho1, ho2, hgood⟩ := ih (by omega) (a + i)
      refine ⟨o, by omega, ?_, fun r' hr' => ?_⟩
      · simp only [wsN]; push_cast
        have : (i : ℤ) + 1 ≤ (cdiv p (ν (t + 1)) : ℤ) := by exact_mod_cast (show i + 1 ≤ _ by omega)
        have : (1 : ℤ) ≤ (wsN p len ν t : ℤ) := by exact_mod_cast hNt
        have e : ((wsN p len ν t - 1 : ℕ) : ℤ) = (wsN p len ν t : ℤ) - 1 := by omega
        rw [e]; omega
      · rcases Nat.lt_or_ge r' (t + 1) with h | h
        · exact hgood r' (by omega)
        · obtain rfl : r' = t + 1 := by omega
          set j := (o - (a + i)).toNat
          have hj : o = a + i + j := by omega
          have hjN : j < wsN p len ν t := by omega
          refine arc_of p (L (t + 1)) (len (t + 1)) (r + j * ν (t + 1)) ?_ _ ?_
          · have : (j + 1) * ν (t + 1) ≤ wsN p len ν t * ν (t + 1) :=
              Nat.mul_le_mul_right _ (by omega)
            nlinarith
          · have hc := congrArg (fun n : ℕ => (n : ZMod p)) hm
            simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id,
              ZMod.natCast_self, mul_zero, add_zero] at hc
            rw [hj]; push_cast
            simp only [x] at hc
            linear_combination hc
  obtain ⟨o, h1, h2, h3⟩ := key (k - 1) (by omega) a
  exact ⟨o, h1, h2, fun t ht => h3 t (by omega)⟩

lemma arc_neg (p : ℕ) (L : ℤ) (len : ℕ) (x : ZMod p) :
    x ∈ arc p L len ↔ -x ∈ arc p (-(L + len - 1)) len := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨len - 1 - i, by omega, ?_⟩
    have : ((len - 1 - i : ℕ) : ℤ) = (len : ℤ) - 1 - i := by omega
    push_cast [this]; ring
  · rintro ⟨i, hi, hx⟩
    refine ⟨len - 1 - i, by omega, ?_⟩
    have : ((len - 1 - i : ℕ) : ℤ) = (len : ℤ) - 1 - i := by omega
    have hx' : x = -((-(L + len - 1) + i : ℤ) : ZMod p) := by rw [← hx]; ring
    rw [hx']; push_cast [this]; ring

/-- **`lem:ws`** (mixed-radix covering), general `k ≥ 1`; rows indexed `0, …, k-1` (row `0` = the paper's
row `1`, the fast row). Let `v_t ∈ ℤ` with `ν_t = |v_t| ≥ 1` and arcs `I_t = arc p (L t) (len t)` of
`|I_t| = len t ≤ p` residues. If `ν_0 ≤ |I_0|` and `N_{t-1} ν_t ≤ |I_t|` for `t ≥ 1`, with
`N_0 = 1 + ⌈(p - |I_0|)/ν_0⌉`, `N_t = N_{t-1} - 1 + ⌈p/ν_t⌉` (`wsN`), then for every `σ ∈ (ℤ/p)^k` every
set of `N_{k-1}` consecutive integers `a, …, a + N_{k-1} - 1` contains an `o` with `σ + o v ∈ I_0 × ⋯ × I_{k-1}`. -/
theorem ws_cover (p : ℕ) [NeZero p] (k : ℕ) (hk : 1 ≤ k) (v : ℕ → ℤ) (L : ℕ → ℤ) (len : ℕ → ℕ)
    (hlen : ∀ t < k, len t ≤ p) (hv : ∀ t < k, 1 ≤ (v t).natAbs) (h1 : (v 0).natAbs ≤ len 0)
    (hN : ∀ t, t + 1 < k →
      wsN p len (fun t => (v t).natAbs) t * (v (t + 1)).natAbs ≤ len (t + 1))
    (σ : ℕ → ZMod p) (a : ℤ) :
    ∃ o : ℤ, a ≤ o ∧ o < a + wsN p len (fun t => (v t).natAbs) (k - 1) ∧
      ∀ t < k, σ t + (o : ZMod p) * (v t : ZMod p) ∈ arc p (L t) (len t) := by
  obtain ⟨o, ho1, ho2, hgood⟩ := ws_pos p k hk (fun t => (v t).natAbs)
    (fun t => if 0 ≤ v t then L t else -(L t + len t - 1)) len hlen hv h1 hN
    (fun t => if 0 ≤ v t then σ t else -σ t) a
  refine ⟨o, ho1, ho2, fun t ht => ?_⟩
  have hg := hgood t ht
  by_cases h0 : 0 ≤ v t
  · simp only [if_pos h0] at hg
    have : (((v t).natAbs : ℕ) : ZMod p) = (v t : ZMod p) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg h0]
    rwa [this] at hg
  · simp only [if_neg h0] at hg
    rw [arc_neg]
    have : (((v t).natAbs : ℕ) : ZMod p) = -(v t : ZMod p) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (by omega)]; push_cast; ring
    rw [this] at hg
    convert hg using 1; ring

end GeoSeq
