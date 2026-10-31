# Course notes: the residue sequences from the ground up

These notes are written for an LLM tutor (or a reader who wants the plan). Point an LLM at this file and at the
step pages next to it, and ask it to quiz you, to say where you are, or to draw more pictures. The human-facing
pages are `../NN-*.html`; this file is the spine they share.

## Audience and goal

- Readers: computer science students. Assumed: high-school algebra, modular arithmetic, number bases, the idea of
  random vs quasi-Monte Carlo points. NOT assumed: polynomials over finite fields, Taylor expansions, residues,
  lattices. The polynomial step is the steep part; introduce it as "numbers without carries" and "base conversion".
- Goal: understand the construction of the residue sequences (`def:residue`) so well that its quasi-uniformity looks
  forced by design: the picture first, the proof light. Target chain: `cor:faure`/`rem:faurerate` (why the classical
  sequences fail) -> `lem:t0` -> `lem:resform`(c) -> `lem:residue-rel` -> `thm:residue` -> `cor:korobov` ->
  `lem:prefix` / `cor:residueQU`. The four Palomar statements (`cor:halton`, `thm:residue`, `cor:korobov`,
  `cor:residueQU`) are Lean-checked.
- Out of scope for now: brick wall, block-periodic sequences, the count of exact relations, windows, small bases.

## Conventions (bind any tutor or writer)

- Cite the paper by `\label` (e.g. `thm:residue`), never by line or page number.
- Never call something proven, impossible or forced unless the paper proves it; state scope as the paper does.
- Dimension: the mechanism is shown in s = 2 (the theorem covers s = 2). For s >= 3 use digit boards (one row of
  s digit strings per point), offset tables (which small offsets pass the checksum), and slices of the cube.
- Quizzes: give hints, not answers; ask the reader to predict or explain; re-test earlier steps later.

## The arc

| step | page | idea | the picture |
|---|---|---|---|
| 1 | `01-*.html` | holes vs clumps; quasi-uniform; checkpoints suffice | a prefix with its closest pair circled; mesh ratio vs N |
| 2 | `02-*.html` | digit reversal; elementary boxes; one point per box | every box shape holds one point |
| 3 | `03-*.html` | polynomials as numbers without carries | integer vs polynomial addition side by side |
| 4 | `04-*.html` | base-(z-a) digits (Taylor digits by repeated division); the Faure coordinates | one index in "base z" and "base z-1" |
| 5 | `05-*.html` | one point per box from remainders (`lem:t0`) | remainder lookup table |
| 6 | `06-*.html` | the carry the other coordinate cannot see (`rem:faurerate`, p = 5: indices 1 and 3120) | digit board of the close pair |
| 7 | `07-*.html` | the design brief: position inside the cell, one rule for every scale | sub-cell offsets, Faure vs fixed rule |
| 8 | `08-*.html` | the digit at position -1; residues sum to zero (`lem:resform`(c)) | a ledger, one entry per pole |
| 9 | `09-*.html` | the checksum: `lem:residue-rel`, occupied fine cells = Λ_v (`thm:residue`(i)) | lit fine cells, jittered points |
| 10 | `10-*.html` | why the lattice keeps points apart (`thm:residue`(ii), `cor:korobov`, p > 2^s) | offsets that pass the checksum |
| 11 | `11-*.html` | from checkpoints to every N (`lem:prefix`, `cor:residueQU`) | the whole construction on one page |

## Per-step notes

(Filled in as each step is worked through: key idea, worked example, check questions with answers, common
misconceptions, figure scripts.)

### Step 1: holes and clumps

- Key idea: measure distances in units of 1/sqrt(N) (the side of the area 1/N each point owns). Holes = covering
  radius, clumps = separation; quasi-uniform = both of order 1 for every N. Random points fail on clumps (birthday
  paradox: closest distance ~ 0.8/N). The classical sequences fail on clumps along explicit checkpoints
  (`rem:faurerate`: Faure base 5, indices 1 and 3120 at N = 5^5; 1 and 5^25 - 5 at N = 5^25, sep ~ 1e-8). The residue
  sequence (p = 5, v = (2,-1)) has sep >= 1/sqrt(5) at every N = 5^odd (`cor:korobov`).
- Figures: `figs/step01_holes_clumps.png` (`step01_data.cjs`, `step01_figs.py`), `figs/step01_checkpoints.png`
  (`step01_checkpoints.cjs`, `faure_far.py`, `step01_fig_checkpoints.py`). Show checkpoints N = p^m, not every N:
  an every-N log plot made Faure look as if it recovers (it only waits for the next failure at 5^25).
- Check questions and answers:
  1. Rising stretches and drops in the every-N curve? Rising: the closest pair is unchanged, sqrt(N) grows (slope
     1/2 on log-log). Drop: a new point lands closer to an old one than any pair before.
  2. Why not a square grid at every N? A k x k grid is not inside the (k+1) x (k+1) grid; a sequence cannot move
     points. Nested grids exist only at sparse sizes (subdivision); the gap between them grows with s.
  3. Random closest distance vs N? ~ 1/N (N^2/2 pairs, each within r with probability ~ pi r^2), so
     distance x sqrt(N) ~ 1/sqrt(N).
- Misconceptions met:
  - Reading the decay rate off one random run (its lucky dips); use the median.
  - "Prefixes between checkpoints are badly distributed." For separation they are a subset of the next checkpoint
    (lose at most a fixed factor, `lem:prefix`). For boxes: a (0,s)-sequence is a net at EVERY power p^m, not only
    at the full levels p^(sK); an arbitrary N splits by its base-p digits into blocks that are nets, so the
    discrepancy stays O((log N)^s / N) at every N. (Step 2 shows this.)

## Progress of the first run-through

| step | status | notes |
|---|---|---|
| 1 | understood (2026-10-31) | answers 1, 2 right; 3 corrected (1/N, not N^(-3/2)) |
| 2-11 | not started | |
