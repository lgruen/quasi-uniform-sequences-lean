# practice/ — the sequences of Table `tab:practice` (Section `sec:practice`)

Supports: Table `tab:practice` (certified bounds of the four residue sequences at p = 13, 17, 23, 31: generator
matrices rebuilt from `def:residue`, exact ljit(Λ_v)²; listed in Table `tab:ca`), and the ordered window systems of the
comparison in `sec:practice` ("those systems are in the data archive").

Data:
* `residue_sequences.txt` — the four residue sequences (s = 3) by places, scale θ and check vector v.
* `residue_U_p13.txt`, `residue_U_p17.txt`, `residue_U_p23.txt`, `residue_U_p31.txt` — their generator matrices
  (format: first line `p R C`, then 3·R rows of C integers, rows i < R and columns j < C of C_0, C_1, C_2; these are the
  matrices whose 𝒥 was measured for the table).
* `pp_designs_s3.txt` — the ordered window systems of the comparison (p = 13, 17, 23, 31; records as in
  `verify/README.md`), with exact window bounds 2/13, 2/17, 4/23, 11/31 at every full level.
* `dump_pp_s3_p13.txt` ... `dump_pp_s3_p31.txt` — generator matrices of the sequences generated from these systems with
  the rule of `rem:steerrule` (same format).
* `gen_points.py` — stand-alone point generator (pure Python): `python3 practice/gen_points.py FILE N [start]` prints
  points start .. start+N−1 of the sequence given by a matrix file.

Programs:
* `rebuild_check.py practice` — rebuilds the generator matrices of `def:residue` from (places, θ, v) and compares them
  entry by entry with the archived files; exact ljit² by enumeration; certified constants truncated to 3 digits.
* `audit_ljit.py` — the audit's exact ljit² of the four check vectors (box enumeration).
* the four check vectors are also in `residue_tables/check_vectors.tsv` and are checked there by three programs.

## Re-run (from the archive root)

    uv run --with numpy python practice/rebuild_check.py practice
    python3 practice/audit_ljit.py
    python3 verify/verify_designs.py practice/pp_designs_s3.txt
    python3 practice/gen_points.py practice/residue_U_p31.txt 3

Expected: `matrices == archived: True` for all four primes, ljit² = 1, 1, 2, 4, certified sep(P_{3K−1}) ≥ .425, .388,
.497, .636 (truncated), inclusion ljit/p = .076, .058, .061, .064, all-N LB/p = .032, .022, .021, .020; the audit prints
the same ljit²; the verifier prints `## TOTAL 4/4 PASS` with LB = 0.153846, 0.117647, 0.173913, 0.354839; the
generator prints the first points (the first is the origin).

Not archived: the values of 𝒥 in `tab:practice` and in the text of `sec:practice` come from exact minimum-distance
programs on the generated points (illustration, not part of a proof); those programs and the candidate scans are
research programs and are not part of this archive.

Requirements: Python 3; NumPy for `rebuild_check.py`.

Last run 2026-10-29: PASS, 0.1 s + < 0.1 s + 0.7 s + < 0.1 s (one core).
