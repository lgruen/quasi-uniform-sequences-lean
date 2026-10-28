/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, version 1; LaTeX source `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V93Defs

@[expose] public section

/-!
# GeoSeq stage V9-3 (part 1): `b`-adic digits and index polynomials

* Uniqueness of polynomial division (`div_mod_unique`), additivity of `div` (`div_add'`), hence of the
  `b`-adic digits (`badicDigit_add`).
* The digit calculus used by `lem:carrypair`: `a_0(a + bW) = a`, `a_{Q+1}(a + bW) = a_Q(W)` for `deg a < deg b`
  (`badicDigit_base`, `badicDigit_succ`); the digits of `b^η W` (`badicDigit_pow_mul`), of the run `g S_n`
  (`badicDigit_run`), vanishing high digits (`badicDigit_high`), and congruences mod `b^λ` (`badicDigit_congr`).
* `runS`: `S_{n+1} = 1 + b S_n`, `(b - 1) S_n = b^n - 1`, `deg S_n ≤ e (n - 1)`, `S_n ≠ 0`.
* Index polynomials: `idxPolyP p (polyIdx p V) = V`, `polyIdx p V < p^m` for `deg V < m`, `deg idxPolyP p n ≤ n`.
-/

namespace GeoSeq

open Finset Polynomial

section Div
variable {F : Type*} [Field F]

lemma div_mod_unique {B X0 r : F[X]} (hB : B ≠ 0) (hr : r.degree < B.degree) :
    (B * X0 + r) / B = X0 ∧ (B * X0 + r) % B = r := by
  have hmod : (B * X0 + r) % B = r := by
    rw [Polynomial.add_mod, EuclideanDomain.mod_eq_zero.2 (dvd_mul_right B X0), zero_add,
      (mod_eq_self_iff hB).mpr hr]
  refine ⟨?_, hmod⟩
  have h := EuclideanDomain.div_add_mod (B * X0 + r) B
  rw [hmod] at h
  exact mul_left_cancel₀ hB (add_right_cancel h)

lemma div_add' (V W B : F[X]) : (V + W) / B = V / B + W / B := by
  by_cases hB : B = 0
  · subst hB; simp [EuclideanDomain.div_zero]
  have h1 := EuclideanDomain.div_add_mod V B
  have h2 := EuclideanDomain.div_add_mod W B
  have hdeg : (V % B + W % B).degree < B.degree :=
    lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_mod_lt _ hB) (degree_mod_lt _ hB))
  have h := (div_mod_unique hB hdeg (X0 := V / B + W / B)).1
  rwa [show B * (V / B + W / B) + (V % B + W % B) = V + W by linear_combination h1 + h2] at h

lemma badicDigit_add (b V W : F[X]) (Q : ℕ) :
    badicDigit b (V + W) Q = badicDigit b V Q + badicDigit b W Q := by
  unfold badicDigit; rw [div_add', Polynomial.add_mod]

lemma badicDigit_zero (b : F[X]) (Q : ℕ) : badicDigit b 0 Q = 0 := by
  unfold badicDigit; rw [EuclideanDomain.zero_div, EuclideanDomain.zero_mod]

lemma ne_zero_of_natDegree {b : F[X]} (hb : 1 ≤ b.natDegree) : b ≠ 0 := by
  rintro rfl; simp at hb

/-- `a_0(a + b W) = a` for `deg a < deg b`. -/
lemma badicDigit_base {b a : F[X]} (ha : a.natDegree < b.natDegree) (W : F[X]) :
    badicDigit b (a + b * W) 0 = a := by
  have hb : b ≠ 0 := ne_zero_of_natDegree (by omega)
  unfold badicDigit
  rw [pow_zero, EuclideanDomain.div_one, add_comm]
  exact (div_mod_unique hb (degree_lt_degree ha)).2

/-- `a_{Q+1}(a + b W) = a_Q(W)` for `deg a < deg b`. -/
lemma badicDigit_succ {b a : F[X]} (ha : a.natDegree < b.natDegree) (W : F[X]) (Q : ℕ) :
    badicDigit b (a + b * W) (Q + 1) = badicDigit b W Q := by
  have hb : b ≠ 0 := ne_zero_of_natDegree (by omega)
  have hbQ : b ^ Q ≠ 0 := pow_ne_zero _ hb
  have hW : b ^ Q * (W / b ^ Q) + W % b ^ Q = W := EuclideanDomain.div_add_mod W (b ^ Q)
  have hr : (W % b ^ Q).degree < (b ^ Q).degree := degree_mod_lt _ hbQ
  have key : a + b * W = b ^ (Q + 1) * (W / b ^ Q) + (b * (W % b ^ Q) + a) := by
    linear_combination (-b) * hW
  have hbne : b.degree ≠ ⊥ := by simpa using hb
  have h1 : (b * (W % b ^ Q)).degree < (b ^ (Q + 1)).degree := by
    rw [degree_mul, pow_succ', degree_mul]
    exact WithBot.add_lt_add_left hbne hr
  have h2 : a.degree < (b ^ (Q + 1)).degree := by
    refine lt_of_lt_of_le (degree_lt_degree ha) ?_
    rw [pow_succ', degree_mul]
    exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hbQ)
  have hdeg : (b * (W % b ^ Q) + a).degree < (b ^ (Q + 1)).degree :=
    lt_of_le_of_lt (degree_add_le _ _) (max_lt h1 h2)
  unfold badicDigit
  rw [key, (div_mod_unique (pow_ne_zero _ hb) hdeg).1]

/-- High digits vanish: `a_Q(V) = 0` if `deg V < e Q`. -/
lemma badicDigit_high {b V : F[X]} (hb : 1 ≤ b.natDegree) {Q : ℕ}
    (hV : V.natDegree < b.natDegree * Q) : badicDigit b V Q = 0 := by
  have hb0 : b ≠ 0 := ne_zero_of_natDegree hb
  have hbQ : b ^ Q ≠ 0 := pow_ne_zero _ hb0
  have hd : V.degree < (b ^ Q).degree := by
    apply degree_lt_degree; rw [natDegree_pow]; linarith
  unfold badicDigit
  rw [(Polynomial.div_eq_zero_iff hbQ).mpr hd, EuclideanDomain.zero_mod]

lemma badicDigit_pow_mul_aux {b : F[X]} (hb : 1 ≤ b.natDegree) (W : F[X]) :
    ∀ η Q : ℕ, badicDigit b (b ^ η * W) Q = if Q < η then 0 else badicDigit b W (Q - η)
  | 0, Q => by simp
  | η + 1, 0 => by
    have h0 : (0 : F[X]).natDegree < b.natDegree := by rw [natDegree_zero]; omega
    rw [show b ^ (η + 1) * W = 0 + b * (b ^ η * W) by ring, badicDigit_base h0]
    simp
  | η + 1, Q + 1 => by
    have h0 : (0 : F[X]).natDegree < b.natDegree := by rw [natDegree_zero]; omega
    rw [show b ^ (η + 1) * W = 0 + b * (b ^ η * W) by ring, badicDigit_succ h0,
      badicDigit_pow_mul_aux hb W η Q]
    by_cases h : Q < η
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega), show Q + 1 - (η + 1) = Q - η by omega]

/-- The digits of `b^η W`: `0` below `η`, then those of `W`. -/
theorem badicDigit_pow_mul {b : F[X]} (hb : 1 ≤ b.natDegree) (W : F[X]) (η Q : ℕ) :
    badicDigit b (b ^ η * W) Q = if Q < η then 0 else badicDigit b W (Q - η) := by
  exact badicDigit_pow_mul_aux hb W η Q

lemma runS_zero (b : F[X]) : runS b 0 = 0 := by simp [runS]

lemma runS_succ (b : F[X]) (n : ℕ) : runS b (n + 1) = 1 + b * runS b n := by
  unfold runS
  rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => pow_succ' b i

lemma runS_mul (b : F[X]) (n : ℕ) : (b - 1) * runS b n = b ^ n - 1 := by
  rw [mul_comm]; exact geom_sum_mul b n

lemma natDegree_runS (b : F[X]) (n : ℕ) : (runS b n).natDegree ≤ b.natDegree * (n - 1) := by
  unfold runS
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have := Finset.mem_range.mp hj
  refine (natDegree_pow_le).trans ?_
  rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)

lemma runS_ne_zero {b : F[X]} (hb : 1 ≤ b.natDegree) {n : ℕ} (hn : 1 ≤ n) : runS b n ≠ 0 := by
  intro h
  have h1 := runS_mul b n
  rw [h, mul_zero] at h1
  have h2 : (b ^ n).natDegree = (1 : F[X]).natDegree := by rw [sub_eq_zero.mp h1.symm]
  rw [natDegree_pow, natDegree_one] at h2
  have : 1 ≤ n * b.natDegree := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

lemma badicDigit_run_aux {b g : F[X]} (hg : g.natDegree < b.natDegree) :
    ∀ n Q : ℕ, badicDigit b (g * runS b n) Q = if Q < n then g else 0
  | 0, Q => by simp [runS_zero, badicDigit_zero]
  | n + 1, 0 => by
    rw [runS_succ, show g * (1 + b * runS b n) = g + b * (g * runS b n) by ring, badicDigit_base hg]
    simp
  | n + 1, Q + 1 => by
    rw [runS_succ, show g * (1 + b * runS b n) = g + b * (g * runS b n) by ring, badicDigit_succ hg,
      badicDigit_run_aux hg n Q]
    by_cases h : Q < n
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- The digits of the run `g S_n` (`deg g < deg b`): `g` at the positions `< n`, `0` beyond. -/
theorem badicDigit_run {b g : F[X]} (hg : g.natDegree < b.natDegree) (n Q : ℕ) :
    badicDigit b (g * runS b n) Q = if Q < n then g else 0 := by
  exact badicDigit_run_aux hg n Q

/-- Digits below `λ` depend only on `V mod b^λ`. -/
lemma badicDigit_congr {b : F[X]} (hb : 1 ≤ b.natDegree) {V V' : F[X]} {l Q : ℕ}
    (h : b ^ l ∣ V - V') (hQ : Q < l) : badicDigit b V Q = badicDigit b V' Q := by
  obtain ⟨H, hH⟩ := h
  have hV : V = V' + b ^ Q * (b ^ (l - Q) * H) := by
    rw [← mul_assoc, ← pow_add, show Q + (l - Q) = l by omega, ← hH]; ring
  rw [hV, badicDigit_add, badicDigit_pow_mul hb, ite_eq_right (lt_irrefl Q), Nat.sub_self]
  have h0 : (0 : F[X]).natDegree < b.natDegree := by rw [natDegree_zero]; omega
  rw [show b ^ (l - Q) * H = 0 + b * (b ^ (l - Q - 1) * H) by
    rw [zero_add, ← mul_assoc, ← pow_succ', show l - Q - 1 + 1 = l - Q by omega], badicDigit_base h0,
    add_zero]

end Div

/-! ## Index polynomials -/

lemma natDigits_sum {p : ℕ} (hp : 1 ≤ p) :
    ∀ (N : ℕ) (a : ℕ → ℕ), (∀ j, a j < p) → ∀ k : ℕ,
      (∑ j ∈ range N, a j * p ^ j) / p ^ k % p = if k < N then a k else 0
  | 0, a, _, k => by simp
  | N + 1, a, ha, k => by
    rw [Finset.sum_range_succ', pow_zero, mul_one]
    have hs : ∑ j ∈ range N, a (j + 1) * p ^ (j + 1) = p * ∑ j ∈ range N, a (j + 1) * p ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    have IH := natDigits_sum hp N (fun j => a (j + 1)) (fun j => ha _)
    rcases k with _ | k
    · rw [pow_zero, Nat.div_one, ite_eq_left (by omega)]
      rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (ha 0)]
    · rw [pow_succ', ← Nat.div_div_eq_div_mul,
        show (p * ∑ j ∈ range N, a (j + 1) * p ^ j + a 0) / p = ∑ j ∈ range N, a (j + 1) * p ^ j by
          rw [add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (ha 0), zero_add], IH k]
      by_cases h : k < N
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]

lemma natSum_lt {p : ℕ} (hp : 1 ≤ p) :
    ∀ (N : ℕ) (a : ℕ → ℕ), (∀ j, a j < p) → ∑ j ∈ range N, a j * p ^ j < p ^ N
  | 0, a, _ => by simp
  | N + 1, a, ha => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := natSum_lt hp N a ha
    have h2 : a N * p ^ N ≤ (p - 1) * p ^ N := Nat.mul_le_mul_right _ (by have := ha N; omega)
    have h3 : (p - 1) * p ^ N + p ^ N = p ^ N * p := by
      rw [mul_comm (p ^ N) p, ← Nat.succ_mul]; congr 1; omega
    omega

variable {p : ℕ} [Fact p.Prime]

lemma coeff_idxPolyP (n k : ℕ) :
    (idxPolyP p n).coeff k = if k < n + 1 then (((n / p ^ k % p : ℕ) : ZMod p)) else 0 := by
  unfold idxPolyP
  rw [finsetSum_coeff]
  simp_rw [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

omit [Fact p.Prime] in
lemma natDegree_idxPolyP (n : ℕ) : (idxPolyP p n).natDegree ≤ n := by
  unfold idxPolyP
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => (natDegree_monomial_le _).trans ?_
  have := Finset.mem_range.mp hk; omega

lemma polyIdx_digit (V : Polynomial (ZMod p)) (k : ℕ) :
    polyIdx p V / p ^ k % p = if k < V.natDegree + 1 then (V.coeff k).val else 0 :=
  natDigits_sum (Fact.out : p.Prime).one_lt.le _ (fun j => (V.coeff j).val) (fun _ => ZMod.val_lt _) k

/-- `idxPolyP p (ι(V)) = V`. -/
theorem idxPolyP_polyIdx (V : Polynomial (ZMod p)) : idxPolyP p (polyIdx p V) = V := by
  have hp : p.Prime := Fact.out
  ext k
  rw [coeff_idxPolyP, polyIdx_digit]
  by_cases hk : k < polyIdx p V + 1
  · rw [ite_eq_left hk]
    by_cases hd : k < V.natDegree + 1
    · rw [ite_eq_left hd, ZMod.natCast_zmod_val]
    · rw [ite_eq_right hd, Nat.cast_zero, coeff_eq_zero_of_natDegree_lt (by omega)]
  · rw [ite_eq_right hk]
    have hlt : polyIdx p V < p ^ k := lt_of_lt_of_le (by omega) (Nat.lt_pow_self hp.one_lt).le
    have h0 := polyIdx_digit V k
    rw [Nat.div_eq_of_lt hlt, Nat.zero_mod] at h0
    by_cases hd : k < V.natDegree + 1
    · rw [ite_eq_left hd] at h0
      exact ((ZMod.val_eq_zero _).mp h0.symm).symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem polyIdx_lt (V : Polynomial (ZMod p)) {m : ℕ} (hV : V.natDegree < m) : polyIdx p V < p ^ m :=
  lt_of_lt_of_le (natSum_lt (Fact.out : p.Prime).one_lt.le _ _ (fun j => ZMod.val_lt _))
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega))

theorem polyIdx_injective : Function.Injective (polyIdx p) := fun V W h => by
  rw [← idxPolyP_polyIdx V, ← idxPolyP_polyIdx W, h]

end GeoSeq
