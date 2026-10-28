/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.S10Defs

@[expose] public section

/-!
# GeoSeq stage S10: `prop:composite`(b) (integer relations in composite dimension)

For composite `s` and every twist `ϱ = ζ^k` there is a nonzero `ξ ∈ ℤ^{s-1}`, depending only on `s` and `k`,
with `∑_d ξ_d u_d = 0` in `𝔽_p` for every prime `p ≡ 1 (mod s)` and every primitive `s`-th root `ζ ∈ 𝔽_p`.

Formal route (the paper's argument without prime ideals): put `Q_d = X^{kd} ∏_{e ≠ d} (1 - X^e) ∈ ℤ[X]`
(`d, e = 1, …, s-1`), so that `u_d = θ ζ^{kd} ∏_{e≠d}(1-ζ^e) / (s ∏_e (1-ζ^e))`. The `s - 1` classes of the
`Q_d` in `ℚ[X]/(Φ_s)` (dimension `φ(s) < s - 1`, `AdjoinRoot.powerBasis'`) are linearly dependent; clearing
denominators gives `ξ ∈ ℤ^{s-1} \ 0` with `Φ_s ∣ ∑ ξ_d Q_d` in `ℚ[X]`, hence in `ℤ[X]` (`Φ_s` monic,
`Polynomial.map_dvd_map`); reducing mod `p` and evaluating at the root `ζ` of `Φ_s` gives the relation.
-/

namespace GeoSeq

open Finset
open scoped Polynomial

/-- `Q_d = X^{k(d+1)} ∏_{e ≠ d} (1 - X^{e+1})` (index `d : Fin (s-1)` stands for `d + 1`). -/
noncomputable def compQ (s k : ℕ) (d : Fin (s - 1)) : ℤ[X] :=
  Polynomial.X ^ (k * ((d : ℕ) + 1)) * ∏ e ∈ univ.erase d, (1 - Polynomial.X ^ ((e : ℕ) + 1))

lemma totient_lt_of_composite (s : ℕ) (hs : 1 < s) (hcomp : ¬ s.Prime) : s.totient < s - 1 := by
  have h1 := Nat.totient_lt s hs
  have h2 : s.totient ≠ s - 1 := fun h => hcomp ((Nat.totient_eq_iff_prime (by omega)).1 h)
  omega

/-- The integer relation modulo `Φ_s`. -/
lemma compRel_exists (s : ℕ) (hs : 1 < s) (hcomp : ¬ s.Prime) (k : ℕ) :
    ∃ ξ : Fin (s - 1) → ℤ, ξ ≠ 0 ∧
      Polynomial.cyclotomic s ℤ ∣ ∑ d, Polynomial.C (ξ d) * compQ s k d := by
  set Φ := Polynomial.cyclotomic s ℚ
  let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic s ℚ)
  haveI := pb.finite
  have hfr : Module.finrank ℚ (AdjoinRoot Φ) = s.totient := by
    rw [pb.finrank]
    show Φ.natDegree = _
    exact Polynomial.natDegree_cyclotomic s ℚ
  set v : Fin (s - 1) → AdjoinRoot Φ :=
    fun d => AdjoinRoot.mk Φ ((compQ s k d).map (Int.castRingHom ℚ)) with hv
  have hnl : ¬ LinearIndependent ℚ v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, hfr] at this
    have := totient_lt_of_composite s hs hcomp
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnl
  set N : ℕ := ∏ d, (g d).den with hN
  have hden : ∀ d, (g d).den ∣ N := fun d => Finset.dvd_prod_of_mem _ (Finset.mem_univ d)
  set ξ : Fin (s - 1) → ℤ := fun d => (g d).num * ((N / (g d).den : ℕ) : ℤ) with hξ
  have hξq : ∀ d, ((ξ d : ℤ) : ℚ) = g d * N := by
    intro d
    obtain ⟨m, hm⟩ := hden d
    have hdiv : N / (g d).den = m := by rw [hm, Nat.mul_div_cancel_left _ (g d).den_pos]
    simp only [hξ, hdiv]
    rw [hm]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  refine ⟨ξ, ?_, ?_⟩
  · intro h0
    have := congrFun h0 i
    simp only [hξ, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero, Rat.num_eq_zero] at this
    rcases this with h | h
    · exact hi h
    · have hpos : 0 < N := Finset.prod_pos fun d _ => (g d).den_pos
      have := Nat.div_pos (Nat.le_of_dvd hpos (hden i)) (g i).den_pos
      omega
  · set R := ∑ d, Polynomial.C (ξ d) * compQ s k d
    have hmk : AdjoinRoot.mk Φ (R.map (Int.castRingHom ℚ)) = 0 := by
      have e : AdjoinRoot.mk Φ (R.map (Int.castRingHom ℚ)) = (N : ℚ) • ∑ d, g d • v d := by
        rw [Finset.smul_sum]
        simp only [R, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_sum, map_mul, hv]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [smul_smul, Algebra.smul_def, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
        congr 2
        rw [Polynomial.C_inj]
        simp [hξq d, mul_comm]
      rw [e, hg, smul_zero]
    rw [AdjoinRoot.mk_eq_zero,
      show Φ = (Polynomial.cyclotomic s ℤ).map (Int.castRingHom ℚ) from
        (Polynomial.map_cyclotomic_int s ℚ).symm] at hmk
    exact (Polynomial.map_dvd_map (Int.castRingHom ℚ) (RingHom.injective_int _)
      (Polynomial.cyclotomic.monic s ℤ)).1 hmk

/-- **`prop:composite`(b)**: for composite `s > 1` and every twist exponent `k` there is a nonzero
`ξ ∈ ℤ^{s-1}` (depending only on `s` and `k`) such that for every prime `p ≡ 1 (mod s)`, every primitive
`s`-th root of unity `ζ ∈ 𝔽_p` and every `θ`, the directions `u_d = θ ζ^{kd} / (s (1 - ζ^d))` of the twisted
symmetric Kummer family satisfy `∑_d ξ_d u_d = 0`; and `ξ ≢ 0 (mod p)` as soon as `p > max_d |ξ_d|`. -/
theorem composite_b (s : ℕ) (hs : 1 < s) (hcomp : ¬ s.Prime) (k : ℕ) :
    ∃ ξ : Fin (s - 1) → ℤ, ξ ≠ 0 ∧
      (∀ (p : ℕ) [Fact p.Prime], p % s = 1 → ∀ ζ : ZMod p, IsPrimitiveRoot ζ s → ∀ θ : ZMod p,
        ∑ d : Fin (s - 1), (ξ d : ZMod p) * twU s θ (ζ ^ k) ζ ((d : ℕ) + 1) = 0) ∧
      (∀ p : ℕ, (∀ d, (ξ d).natAbs < p) → ∃ d, (ξ d : ZMod p) ≠ 0) := by
  obtain ⟨ξ, hξ0, hdvd⟩ := compRel_exists s hs hcomp k
  refine ⟨ξ, hξ0, ?_, ?_⟩
  · intro p _ hp ζ hζ θ
    -- `s ≠ 0` in `𝔽_p`
    have hsp : (s : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have hps : p ≤ s := Nat.le_of_dvd (by omega) h
      have h2 := (Fact.out : p.Prime).two_le
      rcases Nat.lt_or_ge p s with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at hp; omega
      · have : p = s := le_antisymm hps h'
        subst this; rw [Nat.mod_self] at hp; omega
    have hne : ∀ e : Fin (s - 1), (1 : ZMod p) - ζ ^ ((e : ℕ) + 1) ≠ 0 := by
      intro e h
      have := hζ.pow_eq_one_iff_dvd ((e : ℕ) + 1)
      rw [← sub_eq_zero.1 h |>.symm] at this
      have hd := this.1 rfl
      have := Nat.le_of_dvd (by omega) hd
      have := e.isLt
      omega
    -- the evaluation of the relation
    obtain ⟨T, hT⟩ := hdvd
    have hev : ∑ d : Fin (s - 1), (ξ d : ZMod p) * (ζ ^ (k * ((d : ℕ) + 1)) *
        ∏ e ∈ univ.erase d, (1 - ζ ^ ((e : ℕ) + 1))) = 0 := by
      have h := congrArg (fun P : ℤ[X] => (P.map (Int.castRingHom (ZMod p))).eval ζ) hT
      simp only [Polynomial.map_mul, Polynomial.map_cyclotomic, Polynomial.eval_mul,
        (hζ.isRoot_cyclotomic (by omega)).eq_zero, zero_mul] at h
      rw [← h]
      simp [compQ, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub,
        Polynomial.map_pow, Polynomial.eval_finset_sum, Polynomial.eval_prod, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_pow]
    set PiA := ∏ e : Fin (s - 1), ((1 : ZMod p) - ζ ^ ((e : ℕ) + 1))
    have hPiA : PiA ≠ 0 := Finset.prod_ne_zero_iff.2 fun e _ => hne e
    have hu : ∀ d : Fin (s - 1), twU s θ (ζ ^ k) ζ ((d : ℕ) + 1) =
        θ / (s * PiA) * (ζ ^ (k * ((d : ℕ) + 1)) * ∏ e ∈ univ.erase d, (1 - ζ ^ ((e : ℕ) + 1))) := by
      intro d
      have hsplit : PiA = (1 - ζ ^ ((d : ℕ) + 1)) * ∏ e ∈ univ.erase d, (1 - ζ ^ ((e : ℕ) + 1)) :=
        (Finset.mul_prod_erase univ _ (Finset.mem_univ d)).symm
      unfold twU
      rw [hsplit, ← pow_mul, mul_comm k]
      have h1 := hne d
      have h2 : ∏ e ∈ univ.erase d, ((1 : ZMod p) - ζ ^ ((e : ℕ) + 1)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun e _ => hne e
      field_simp
    simp_rw [hu]
    rw [show ∑ d : Fin (s - 1), (ξ d : ZMod p) * (θ / (s * PiA) * (ζ ^ (k * ((d : ℕ) + 1)) *
        ∏ e ∈ univ.erase d, (1 - ζ ^ ((e : ℕ) + 1)))) = θ / (s * PiA) * ∑ d : Fin (s - 1),
        (ξ d : ZMod p) * (ζ ^ (k * ((d : ℕ) + 1)) * ∏ e ∈ univ.erase d, (1 - ζ ^ ((e : ℕ) + 1))) by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_; ring, hev, mul_zero]
  · intro p hp
    by_contra h
    push_neg at h
    apply hξ0
    funext d
    have := h d
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] at this
    have := Nat.eq_zero_of_dvd_of_lt this (hp d)
    simpa using this

end GeoSeq
