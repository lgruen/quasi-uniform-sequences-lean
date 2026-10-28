/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.N1

@[expose] public section

/-!
# GeoSeq stage S10: `thm:dual` (dual-number Faure sequences), part 1: the kernel criterion

* `blockNet0_of_kernel`: over a finite field, if for a composition-wise kernel test every index vector
  `V ∈ F^m` whose first `d_c` digits vanish in every coordinate is `0`, then `P_m` is a net (block `0`);
  `isSeq0_of_kernel`: if this holds for every `m`, the sequence is a `(0,s)`-sequence (every block).
* `kernel_of_blockNet0`: the converse (from `box_existsUnique`).
-/

namespace GeoSeq

open Finset

section Kernel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {s q : ℕ} [NeZero q]

/-- Kernel test ⟹ `P_m` is a `(0,m,s)`-net: the digit map `F^m → F^{∑ d_c}` is linear and injective
between sets of the same size, hence bijective. -/
lemma blockNet0_of_kernel (D : DigitCode F q) (C : Gen s F) (m : ℕ)
    (hker : ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ V : Fin m → F,
      (∀ c, ∀ n < d c, vecDigit C V c n = 0) → V = 0) :
    BlockNet0 D C m 0 := by
  intro d hd a ha
  rw [existsUnique_block D m 0]
  -- the digit map and its bijectivity
  let L : (Fin m → F) → ((Σ c : Fin s, Fin (d c)) → F) := fun V x => vecDigit C V x.1 x.2
  have hinj : Function.Injective L := by
    intro V W h
    have h0 := hker d hd (V - W) fun c n hn => by
      have := congrFun h ⟨c, ⟨n, hn⟩⟩
      simp only [L] at this
      have hs : V - W = V + (-1 : F) • W := by simp [sub_eq_add_neg]
      rw [hs, vecDigit_add, vecDigit_smul, this]; ring
    exact sub_eq_zero.1 h0
  have hcard : Fintype.card (Fin m → F) = Fintype.card ((Σ c : Fin s, Fin (d c)) → F) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_sigma, hd]
  have hbij : Function.Bijective L := (Fintype.bijective_iff_injective_and_card L).2 ⟨hinj, hcard⟩
  -- the target pattern
  let t : (Σ c : Fin s, Fin (d c)) → F := fun x => digOf D (d x.1) (a x.1) x.2
  obtain ⟨V, hV⟩ := hbij.2 t
  refine ⟨V, ?_, ?_⟩
  · intro c
    show Z3Net.Proofs.digSum q (d c) _ = a c
    have hfun : (fun n : Fin (d c) => (D.enc (seqDigit D C (blockIdx D m 0 V) c n) : ℕ)) =
        fun n : Fin (d c) => (D.enc (vecDigit C V c n) : ℕ) := by
      funext n; rw [seqDigit_block, seqDigit_zero, add_zero]; rfl
    rw [hfun, digSum_enc_eq_iff D (d c) (a c) (ha c)]
    intro n
    exact congrFun hV ⟨c, n⟩
  · intro W hW
    apply hinj
    rw [hV]
    funext x
    have := hW x.1
    change Z3Net.Proofs.digSum q (d x.1) _ = a x.1 at this
    have hfun : (fun n : Fin (d x.1) => (D.enc (seqDigit D C (blockIdx D m 0 W) x.1 n) : ℕ)) =
        fun n : Fin (d x.1) => (D.enc (vecDigit C W x.1 n) : ℕ) := by
      funext n; rw [seqDigit_block, seqDigit_zero, add_zero]; rfl
    rw [hfun, digSum_enc_eq_iff D (d x.1) (a x.1) (ha x.1)] at this
    exact this x.2

/-- Kernel test for every `m` ⟹ `(0,s)`-sequence. -/
lemma isSeq0_of_kernel (D : DigitCode F q) (C : Gen s F)
    (hker : ∀ m : ℕ, ∀ d : Fin s → ℕ, ∑ c, d c = m → ∀ V : Fin m → F,
      (∀ c, ∀ n < d c, vecDigit C V c n = 0) → V = 0) : IsSeq0 D C := by
  rw [isSeq0_iff_trunc]
  intro m
  exact (blockNet0_iff D C m 0).1 (blockNet0_of_kernel D C m (hker m))

/-- Converse: a net prefix passes the kernel test. -/
lemma kernel_of_blockNet0 (D : DigitCode F q) (C : Gen s F) (m : ℕ) (hnet : BlockNet0 D C m 0)
    (d : Fin s → ℕ) (hd : ∑ c, d c = m) (V : Fin m → F)
    (hV : ∀ c, ∀ n < d c, vecDigit C V c n = 0) : V = 0 := by
  obtain ⟨U, _, hU⟩ := box_existsUnique D C m hnet d hd (fun _ _ => (0 : F))
  exact (hU V hV).trans (hU 0 fun c n _ => vecDigit_zero C c n).symm

end Kernel

end GeoSeq
