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
# GeoSeq stage V3: definitions for the mixed-radix rule in every dimension (`lem:MRbound`, `thm:MRall`)

All quantities of `sec:order` after `ex:MR101`, with `n = s - 1`:
* `mrMuBar` = `μ̄_{tj} = μ_{tj}/gcd` (a natural number);
* `mrUmin` = `u_min = max_t 1/(2γ_t)` (rational);
* over any field with a linear order (`ℚ` for exact evaluation, `ℝ` for the theorems):
  `mrNuP` / `mrNuM` = `ν^±_{tj}(u) = μ̄_{tj} ∏_{i=t+1}^{j} (γ_i u ± 1/2)`, `mrEta` = `η_t(j) = ∑_{r=0}^{t} 1/ν^-_{rj}(u)`,
  `mrPu` = `p(u) = Q_s^s u^s`, `mrFrow` = the row bounds `F_0`, `F_c` (`1 ≤ c ≤ n`), `mrF` = `F = max_c F_c`;
* real numbers: `mrQ` = `Q_s = (Q_s^s)^{1/s}`, `mrU` = `u(p) = p^{1/s}/Q_s`, the step factors of the
  **mixed-radix rule** `mrRuleH` = `h_t = max(1, round(γ_t u))` (`round` = Mathlib's `round`, ties upwards; ties
  cannot occur at the primes of `mr_no_ties`), `mrU1` = `u_1(s) = inf {u > u_min : F(u) < 1}`, `mrP1` =
  `p_1(s) = Q_s^s u_1(s)^s`, `mrCp` = `C'_s = Q_s u^* F(u^*)`.
* exact rounding (for the range checker): `mrHq` = the least `k ≤ fuel` with `(2k+1)^s Q_s^s > 2^s γ_t^s p`
  (it equals `round(γ_t u)` whenever it is below the fuel bound, `mrRuleH_eq_of_bracket`).
-/

namespace GeoSeq

open Finset

/-- `μ̄_{tj} = μ_{tj}/gcd` (`def:MR`). -/
def mrMuBar (s t j : ℕ) : ℕ := mrMu s t j / mrG s

/-- `u_min = max_{1 ≤ t ≤ n} 1/(2γ_t)` (`sec:order`, before `lem:MRbound`; `0` for `s ≤ 1`). -/
def mrUmin (s : ℕ) : ℚ :=
  if h : (Ioc 0 (s - 1)).Nonempty then (Ioc 0 (s - 1)).sup' h (fun t => 1 / (2 * mrGamma s t)) else 0

section Field

variable {α : Type*} [Field α] [LinearOrder α]

/-- `ν^+_{tj}(u) = μ̄_{tj} ∏_{i=t+1}^{j} (γ_i u + 1/2)`. -/
def mrNuP (s t j : ℕ) (u : α) : α := (mrMuBar s t j : α) * ∏ i ∈ Ioc t j, ((mrGamma s i : α) * u + 1 / 2)

/-- `ν^-_{tj}(u) = μ̄_{tj} ∏_{i=t+1}^{j} (γ_i u - 1/2)`. -/
def mrNuM (s t j : ℕ) (u : α) : α := (mrMuBar s t j : α) * ∏ i ∈ Ioc t j, ((mrGamma s i : α) * u - 1 / 2)

/-- `η_t(j) = ∑_{r=0}^{t} 1/ν^-_{rj}(u)`. -/
def mrEta (s t j : ℕ) (u : α) : α := ∑ r ∈ range (t + 1), 1 / mrNuM s r j u

/-- `p(u) = Q_s^s u^s`. -/
def mrPu (s : ℕ) (u : α) : α := (mrQss s : α) * u ^ s

/-- The row bounds of `lem:MRbound`: `F_0(u) = (2 ∑_{j=1}^{n} ν^+_{0j} + 1)/p(u)` and, for `1 ≤ c ≤ n`,
`F_c(u) = 2 ∑_{j>c} max(ν^+_{cj}/p(u), η_{c-1}(j) ν^+_{cj}/2) + η_{c-1}(c)`. -/
def mrFrow (s c : ℕ) (u : α) : α :=
  if c = 0 then (2 * ∑ j ∈ Ioo 0 s, mrNuP s 0 j u + 1) / mrPu s u
  else 2 * ∑ j ∈ Ioo c s, max (mrNuP s c j u / mrPu s u) (mrEta s (c - 1) j u * mrNuP s c j u / 2) +
    mrEta s (c - 1) c u

/-- `F = max_{0 ≤ c ≤ n} F_c` (`lem:MRbound`; `0` for `s = 0`). -/
def mrF (s : ℕ) (u : α) : α :=
  if h : (range s).Nonempty then (range s).sup' h (fun c => mrFrow s c u) else 0

end Field

/-- `Q_s = (Q_s^s)^{1/s}` (`def:MR`). -/
noncomputable def mrQ (s : ℕ) : ℝ := ((mrQss s : ℚ) : ℝ) ^ ((1 : ℝ) / s)

/-- `u = p^{1/s}/Q_s` (`def:MR`, the mixed-radix rule). -/
noncomputable def mrU (s p : ℕ) : ℝ := (p : ℝ) ^ ((1 : ℝ) / s) / mrQ s

/-- **The step factors of the mixed-radix rule** `h_t = max(1, round(γ_t u))`, `u = p^{1/s}/Q_s` (`def:MR`;
`round` rounds ties upwards — at the primes of `mr_no_ties` there are no ties). -/
noncomputable def mrRuleH (s p : ℕ) (t : ℕ) : ℕ := max 1 (round ((mrGamma s t : ℝ) * mrU s p)).toNat

/-- `u_1(s) = inf {u > u_min : F(u) < 1}` (`thm:MRall`). -/
noncomputable def mrU1 (s : ℕ) : ℝ := sInf {u : ℝ | (mrUmin s : ℝ) < u ∧ mrF s u < 1}

/-- `p_1(s) = Q_s^s u_1(s)^s` (`thm:MRall`). -/
noncomputable def mrP1 (s : ℕ) : ℝ := (mrQss s : ℝ) * mrU1 s ^ s

/-- `C'_s = Q_s u^* F(u^*)` (`thm:MRall`(c)). -/
noncomputable def mrCp (s : ℕ) (us : ℝ) : ℝ := mrQ s * us * mrF s us

/-! ## Exact rounding (the range checker of `tab:P1`) -/

/-- The least `k < fuel` with `(2k+1)^s Q_s^s > 2^s γ_t^s p`, i.e. `round(γ_t u)` (`fuel` if there is none). -/
def mrHqAux (s p t : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if (2 ^ s * mrGamma s t ^ s * p : ℚ) < (2 * k + 1 : ℚ) ^ s * mrQss s then k else mrHqAux s p t fuel (k + 1)

/-- The exact step factor `max(1, k)`, `k` = the rounding of `γ_t u` by rational `s`-th powers (fuel `64`). -/
def mrHq (s p : ℕ) (t : ℕ) : ℕ := max 1 (mrHqAux s p t 64 0)

/-- `67` is prime (for the non-vacuity example `MRall_example`). -/
instance fact_prime_67 : Fact (Nat.Prime 67) := ⟨by norm_num⟩

end GeoSeq
