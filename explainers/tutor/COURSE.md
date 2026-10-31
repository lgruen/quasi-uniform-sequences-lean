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

## Progress of the first run-through

| step | status | notes |
|---|---|---|
| 1-11 | not started | |
