# verify/ — the common verifier of the window systems

Supports: the window systems used with `prop:steer` and `lem:cert` (j = 1) — the archived systems of
`practice/` (comparison in `sec:practice`, `tab:practice`), `selection_rule/cfg/` (sequences of the figures,
`rem:steerrule`), and the ordered window systems of an earlier version of this work in `lf_designs/` and `mrA_designs/`
(not used in this paper). Described in Appendix `app:verification` ("Window systems").

Files: `verify_designs.py` (Python 3, standard library) and `cover_helper.cpp` (exact coverings; compiled
automatically with `g++ -O3` into `verify/cover_helper` on first use — delete it afterwards). The verifier reads
ONLY data files, never the search programs.

## Record format

A record file holds one or more records separated by blank lines; each record is a block of lines `key values...`:

| line | meaning |
|---|---|
| `s S p P theta T brick B mode M` | dimension s, prime p, scale θ in F_p (the `brick`/`mode` fields are ignored) |
| `places a_0 ... a_{s-1}` | the places in F_p (pairwise distinct) |
| `rho l_0 ... l_{s-1}` (or `lambda ...`) | the constants λ_c (nonzero mod p) |
| `kappa_row k_0 ... k_{s-1}` | s lines: the stored crosses κ_{c←j}, row c, centred representatives (diagonal 0) |
| `win j lo_0 hi_0 ... lo_{s-1} hi_{s-1}` | the windows W_{c←j} of column j for c = 0..s−1 (intervals of centred residues; the own window is the entry c = j) |
| `M ...`, `W ...` | own/cross sizes per column (informational) |
| `minS n LB x worst e...` | the stored exact window bound: n = min Σ_c (p f_1)² (integer), LB = √n / p, and a minimising step |
| `superdiag d_1 ... d_{s-1}` (optional) | integer superdiagonal of a rational (ordered) system |
| `order j r...` (optional) | the row order of column j used for the `lem:ws` covering certificate |
| `frame a_0/.. theta n/d` (optional) | rational frame and θ of a rational system |
| `heights h_1 ...` (optional) | heights of the closed-form rule MR-A (earlier version) |
| `member NAME Gamma G` (optional) | provenance label and the value Γ of an ordered system |

## Checks per record

(0) p prime, places distinct, θ and λ_c nonzero mod p; (1) the crosses κ_{c←j} computed from the λ_c by `prop:LI`(c), in
two equivalent normalisations, equal the stored ones; (2) for a rational system (frame + θ + superdiag, or heights):
the rational gauge is rebuilt, the upper crosses are integers equal to the stored centred values, numerators and
denominators prime to p; (3) condition (i) of `prop:steer` (the forced crosses −κ lie in their windows); (4) condition (ii)
for every column: exactly (exact scan for at most two restricted crosses; enumeration of F_p^j when p^{j−1} ≤ 2·10⁶,
raise with `--brute N`) or else by `lem:ws` in the stored row order; (5) the exact window bound LB(W) of `lem:cert`
(j = 1) from its definition (f_1 of `rem:onedigit`, cross-checked against its definition for p ≤ 300), compared with the
stored `minS`; (6) for ordered systems of the earlier version: the ordered pattern, Γ and the closed-form value, which
must equal the exact LB. Output per record: `PASS|FAIL name s p member cover=<E|W per column> LB=... Gamma=...`, then a
summary line `## TOTAL k/n PASS`.

## Re-run (from the archive root)

    python3 verify/verify_designs.py [--brute N] [--range a b] FILE...

e.g. `python3 verify/verify_designs.py practice/pp_designs_s3.txt` (expected: `## TOTAL 4/4 PASS`). The full list of
commands is in the READMEs of `practice/`, `selection_rule/`, `lf_designs/`, `mrA_designs/`; the s = 5 file of
`lf_designs/` is checked in chunks with `--range a b` (records a..b−1).

`results/`: the outputs of the run of 2026-10-29 — 2846 / 2846 records PASS: `lf_designs` 25 + 279 + 2290 + 4,
`mrA_designs` 6 + 53 + 178, `practice` 4, `selection_rule/cfg` 7.

Negative controls (re-run 2026-10-29 on corrupted copies of the four `practice/` records, written to `bin/`): a stored
cross changed by one is rejected (`WHY=kappa_row,...`); of the 24 single shortenings of an own window by one, 20 are
rejected and 4 are accepted (column 2 at p = 13 and p = 23: the shortened system still satisfies every check, i.e.
those stored own windows are longer than needed). The research repository's own negative-control program is not
archived.

Requirements: Python 3, a C++ compiler.

Last run 2026-10-29: PASS (2846/2846 records), 0.1–16.6 s per command (one core; largest: `lf_designs_s3.txt` +
`lf_designs_s4.txt` together, 16.6 s including the compilation of `cover_helper`).
