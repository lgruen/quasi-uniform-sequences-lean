# p1_certificates/ — threshold certificates of the closed-form ordered rule (earlier version; not used in this paper)

Status: part of the ordered window systems of an earlier version of this work (Appendix `app:archive`: "not used
here"). Kept so that the data of that version remain checkable; no statement of this paper depends on it.

Statement checked (earlier version, Proposition "P1" for the closed-form rule MR-A): for every prime
p ≥ P_1(s) = K_s^s u*^s, Γ < p and 1 − LB ≤ C'_s p^{−1/s}, C'_s = K_s u* G(u*). Finite check: G(u*) < 1 at ONE rational
u* per s, G the explicit rational function of that version's Lemma B, plus u* > max_t 1/(2γ_t) (that lemma's
hypothesis); the monotonicity is a written proof.
Certificates u*: s = 3: 2934559/10⁶; s = 4: 3495097/10⁶; s = 5: 197527/62500; s = 6: 2270329/500000;
s = 7: 1280189/250000.

Files: `p1.py`, `mrA.py` — the audit's independent implementations (G(u) and rule MR-A, written from the
definitions); `p1_eval.py` evaluates G EXACTLY (Fractions) at the five u*.

## Re-run (from the archive root)

    uv run --with sympy python p1_certificates/p1_eval.py

Expected: `G(u*)<1: True` for s = 3..7 (1 − G ≈ 5·10⁻⁷ ... 10⁻⁶); P_1 = 63.18, 889.81, 8057.8, 860654, 5.3213·10⁷;
C'_s = 3.983, 5.462, 6.043, 9.753, 12.697. (`uv run --with sympy python p1_certificates/p1.py` alone re-does the
bisection for s = 3..5 and sanity scans; not part of the check.) The authors' original evaluator is a research program
(not archived).

Requirements: Python 3, SymPy.

Last run 2026-10-29: PASS, 0.2 s (one core; the first `uv run` may take longer to set up SymPy).
