# Low-discrepancy quasi-uniform digital sequences in every dimension

Manuscript, Lean 4 formalization, data and verification archive, and interactive explainers for

> Leonhard Gruenschloss, *Low-discrepancy quasi-uniform digital sequences in every dimension*, version 1 (2026).
> Hexagon: HEXAGON_ID_TBD.

A sequence in the unit cube is quasi-uniform if, for every N, its first N points have minimum distance and covering
radius both of the optimal order N^(-1/s). Dick, Goda and Suzuki asked for such sequences among the digital sequences
of quasi-Monte Carlo integration, and Goda, Hofer and Suzuki asked whether any Halton-type sequence is quasi-uniform.
The manuscript shows that in dimension two and higher no Halton-type sequence, no Sobol' sequence, no classical
Niederreiter sequence and no Faure sequence is quasi-uniform, and constructs, for every dimension s and every prime
base p > 2^s, explicit quasi-uniform digital (0, s)-sequences: one fixed linear scramble of a generalized Faure sequence
in which the digits of all coordinates at one scale are residues of one rational function (`thm:residue`). This
repository is release **v1.0.0**, which accompanies **version 1** of the manuscript. It is the companion of
*Low-discrepancy quasi-uniform digital nets in every dimension* (Hexagon
[hexagon:2610.00217v1](https://hexagonmath.org/abs/2610.00217v1); repository
<https://github.com/lgruen/separated-nets-lean>, Zenodo [10.5281/zenodo.23327748](https://doi.org/10.5281/zenodo.23327748)).

Archived at Zenodo: concept DOI ZENODO_DOI_TBD (all versions); release v1.0.0: version DOI ZENODO_VERSION_DOI_TBD.
Palomar entry (`cor:halton`; `thm:residue` with `cor:korobov`, `cor:residueQU`): PALOMAR_ID_TBD.
Website: <https://lgruen.github.io/quasi-uniform-sequences-lean/>, with the interactive explainers
<https://lgruen.github.io/quasi-uniform-sequences-lean/explainers/>.

## Contents

| path | content | licence |
|---|---|---|
| repository root | the Lean 4 / Mathlib Lake project: library `GeoSeq/` (definitions, statement files `GeoSeq/Statements/*.lean`, proofs), `Z3Net/` (the part of the Lean library of the nets paper that `GeoSeq` imports), the Challenge/Solution roots `GeoSeq*Challenge.lean` / `GeoSeq*Solution.lean` and the 78 Comparator configurations `comparatorGeoSeq*.json`, tools in `scripts/` | MIT |
| [`HeadlineSeqV4/`](HeadlineSeqV4/), `comparatorHeadlineSeqV4.json`, [`palomar/headline-seq-v4/formalization.yaml`](palomar/headline-seq-v4/formalization.yaml) | the Palomar entry: a Mathlib-only statement file of 195 lines (`cor:halton`; `thm:residue` with `cor:korobov` and `cor:residueQU` for one explicit residue sequence) | MIT |
| [`docs/library-formalization.yaml`](docs/library-formalization.yaml) | metadata of the whole library, in the `formalization.yaml` format; not a Palomar entry | MIT |
| [`COVERAGE.md`](COVERAGE.md), [`COMPARATOR_RESULTS.md`](COMPARATOR_RESULTS.md) | the configurations and what they cover; the Comparator runs | MIT |
| [`paper/`](paper/) | `main.tex`, `sections/`, `refs.bib`, `main.bbl`, `main.pdf`, `figs/`, `Makefile` | manuscript CC BY 4.0 ([`paper/LICENSE.md`](paper/LICENSE.md)) |
| [`archive/`](archive/) | the data and verification archive of the computer-assisted parts (`app:archive`): one directory per item, each with a README naming the statement it supports and the command that re-runs its check | MIT |
| [`explainers/`](explainers/) | five interactive pages that compute the sequences in the browser, with a cross-check against the paper's numbers | MIT |
| `.github/workflows/pages.yml`, `site/` | GitHub Pages build of the explainers and the paper PDF (manual trigger only) | MIT |

## Status

The paper (`app:lean`) lists what is formalized. The results new in version 1 are compared in 58 Comparator
configurations with 679 theorems (32 with 311 theorems, `comparatorGeoSeqV9*.json`, and 26 with 368 theorems,
`comparatorGeoSeqV10_*.json`); the results kept from the previous version of the
manuscript are compared in the 20 configurations of that version (`comparatorGeoSeq.json`, `…S3/S4/K4/S10/S11…`,
`…V0…V7…`), and the Palomar entry in `comparatorHeadlineSeqV4.json` (4 theorems). Every compared theorem is proved;
the only axioms are `propext`, `Classical.choice` and `Quot.sound`; there is no `native_decide` (finite computations
are evaluated by the Lean kernel, `decide +kernel`); `sorry` occurs only in the statement files
(`GeoSeq/Statements/*.lean`, `HeadlineSeqV4/Challenge.lean`), by design: the Challenge holds the statements, the
Solution the proofs. [Comparator](https://github.com/leanprover/comparator) checks each configuration with the Lean
kernel and the independent NanoDa kernel; all 79 configurations were accepted by both kernels; see
[`COMPARATOR_RESULTS.md`](COMPARATOR_RESULTS.md) for the runs and
[`COVERAGE.md`](COVERAGE.md) for what each configuration covers and what is not formalized.

Statement review: TODO(author) — the author's review and sign-off of the Palomar entry's statements (and the basis on
which the other library statements are accepted) are recorded here before the release. No independent human peer
review has been performed.

## Building

The Lean project (needs [elan](https://github.com/leanprover/elan); toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib
`v4.35.0-rc3`, both pinned):

```sh
lake exe cache get                 # Mathlib build cache
lake build                         # every library and every Challenge/Solution root
lake build HeadlineSeqV4           # only the Palomar entry (and what it imports)
```

Some modules evaluate long kernel computations (the certificates of `thm:S3`, `thm:K4`, `thm:S4`, `thm:p7`, the data
of the earlier ordered window systems, the per-prime checks of `thm:block`(c), (d), `GeoSeq/V99Ca5*.lean`,
`GeoSeq/V10_1D5ca*.lean`, the eleven evaluations of `GeoSeq/V10_4S6ca*.lean` (about 1.7 min each), and the prime-power
rows `GeoSeq/V10_3RowsX.lean`). Lake builds
modules in parallel, which can exceed the memory of a 32 GB machine; if it starts swapping, build the heavy modules one
at a time first and then run `lake build` again. Measured build times are in `COMPARATOR_RESULTS.md`.

To run Comparator, build it, `lean4export` at the tag of the toolchain and NanoDa (on Linux also `landrun`), then
`scripts/run_comparator.sh <tools dir> comparatorHeadlineSeqV4.json` (one or more configurations, in sequence; logs
`comparator_<config>.log`).

The paper (needs [tectonic](https://tectonic-typesetting.github.io), or a TeX distribution with `latexmk`):

```sh
cd paper && make pdf                     # or: latexmk -pdf main.tex
```

The archive (Python 3, a C++17 compiler, [uv](https://docs.astral.sh/uv/) for SymPy/NumPy): see
[`archive/README.md`](archive/README.md); every check runs in under half a minute on one core.

The explainers' cross-check (needs `node`): `node explainers/check/crosscheck.cjs`. The pages can be opened locally
(`site/build_site.sh _site` assembles the website in `_site/`).

## Versions

Release v1.0.0 = version 1 of the manuscript. A later version of the manuscript gets a new release (v2.0.0, …) of this
repository, a new Zenodo version under the same concept DOI, and a new version of the Palomar entry.

## Use of AI

The constructions, proofs and Lean formalization were produced by AI systems (Anthropic Claude Opus 5.5; some early exploratory results used Claude Fable 5.1) under the author's direction. The author selected the problems, steered the research and reviewed the formal statements, but has not verified every proof by hand. AI systems are not listed as authors; responsibility for the deposit rests with the author.

## Citation

See [`CITATION.cff`](CITATION.cff). The archive is cited by its Zenodo concept DOI ZENODO_DOI_TBD (all versions) or,
for release v1.0.0, by its version DOI ZENODO_VERSION_DOI_TBD.

## Licence and third-party material

Code, Lean sources, scripts, archive programs and data: MIT ([`LICENSE`](LICENSE)). Manuscript (`paper/main.tex`,
`paper/sections/`, `paper/refs.bib`, `paper/main.bbl`, `paper/main.pdf`, `paper/figs/`): CC BY 4.0
([`paper/LICENSE.md`](paper/LICENSE.md)).

`Z3Net/` is taken from the Lean formalization of the nets paper (same author, MIT). Its centred-residue helper `cres`
(in the `*Defs` modules of `Z3Net/`) is adapted from `GKEvenNet.cres` (`GKEvenNet/Distance.lean`) in Lennart Rudolph's
Palomar formalization of the even-order Grünschloß–Keller nets, <https://github.com/lennrt/palomar-formalizations>
(archived at Zenodo, doi:10.5281/zenodo.22264675), released under the MIT License, Copyright (c) 2026 Lennart Rudolph;
its copyright line is reproduced in `LICENSE`. The layout of the Lean project follows the same repository's Palomar
template. Lean 4, Mathlib and the Python packages used by the scripts are dependencies fetched at build time; they are
not redistributed here. The Sobol' direction-number files of Joe and Kuo are not redistributed (the explainers
use only the initial values of the first three dimensions, quoted in `explainers/src/core.js`).
