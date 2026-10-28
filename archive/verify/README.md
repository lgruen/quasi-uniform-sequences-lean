# verify/ — the common verifier of the window systems

Supports: the five archived window systems used with `prop:steer` and `lem:cert` (j = 1): the four ordered window systems
of the comparison in `sec:practice` (`practice/pp_designs_s3.txt`; "those systems are in the data archive") and the
staggered window system at p = 101 of Figure `fig:bsgeom` (`selection_rule/cfg/bs_s3_p101.cfg`, certified
sep(P_{3K}) ≥ 52/101 = 0.5148 for every K). Described in Appendix `app:verification` ("Window systems").

Files: `verify_designs.py` (Python 3, standard library) and `cover_helper.cpp` (exact coverings; compiled
automatically with `g++ -O3` into `verify/cover_helper` on first use — delete it afterwards); `negative_controls.py`
(corrupted copies of the records, see below). The verifier reads ONLY data files, never the search programs.

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
| `heights h_1 ...` (optional) | heights of a closed-form ordered rule of an earlier version (no archived record uses it) |
| `member NAME Gamma G` (optional) | provenance label and the value Γ of an ordered system |

## Checks per record

(0) p prime, places distinct, θ and λ_c nonzero mod p; (1) the crosses κ_{c←j} computed from the λ_c by `prop:LI`(c), in
two equivalent normalisations, equal the stored ones; (2) for a rational system (frame + θ + superdiag, or heights):
the rational gauge is rebuilt, the upper crosses are integers equal to the stored centred values, numerators and
denominators prime to p; (3) condition (i) of `prop:steer` (the forced crosses −κ lie in their windows); (4) condition (ii)
for every column: exactly (exact scan for at most two restricted crosses; enumeration of F_p^j when p^{j−1} ≤ 2·10⁶,
raise with `--brute N`) or else by `lem:ws` in the stored row order; (5) the exact window bound LB(W) of `lem:cert`
(j = 1) from its definition (f_1 of `rem:onedigit`, cross-checked against its definition for p ≤ 300), compared with the
stored `minS`; (6) for ordered systems (the four records of `practice/`): the ordered pattern, Γ and the closed-form value of the
earlier version, which must equal the exact LB. Output per record: `PASS|FAIL name s p member cover=<E|W per column> LB=... Gamma=...`, then a
summary line `## TOTAL k/n PASS`.

## Re-run (from the archive root)

    python3 verify/verify_designs.py practice/pp_designs_s3.txt selection_rule/cfg/bs_s3_p101.cfg
    python3 verify/negative_controls.py practice/pp_designs_s3.txt selection_rule/cfg/bs_s3_p101.cfg

Expected: `## TOTAL 5/5 PASS`, with LB = 0.153846, 0.117647, 0.173913, 0.354839 (= 2/13, 2/17, 4/23, 11/31, the ordered
systems at p = 13, 17, 23, 31; covering exact in every column, `cover=EEE`) and LB = 0.514851 (= 52/101, the staggered
system). `results/` holds the per-record output of this command (`practice.txt`, `selection_rule_cfg.txt`) and of the
negative controls (`negative_controls.txt`).

Negative controls (`negative_controls.py`, run 2026-10-29): every record passes uncorrupted; each of the 30 changes of
one stored cross κ_{c←j} (c ≠ j) by one is rejected (30/30); of the 22 shortenings of an own window by one at one end
(own windows with at least two elements), 18 are rejected and 4 are accepted: column 2 of the systems at p = 13 and
p = 23, shortened at either end. An accepted shortening passes every check including the stored exact bound `minS`, so
it is itself a valid window system with the same bound; those four stored own windows are longer than needed.

Requirements: Python 3, a C++ compiler.

Last run 2026-10-29: PASS (5/5 records), 0.8 s (including the compilation of `cover_helper`); negative controls 0.1 s
(one core).
