# Coverage: the Comparator configurations and the paper

The authoritative list of what is formalized, what differs in form and what is not formalized is the paper itself,
Appendix `app:cert`, subsection `app:lean` (paragraphs "Formalized results of this version", "Where the formal
statements differ in form", "Not formalized", "Configurations", "Palomar entry"). This file maps the configurations of
this repository to the paper. Results are cited by their LaTeX labels; the statement files
(`GeoSeq/Statements/*.lean`) give the labels in their docstrings, statement by statement.

All configurations permit exactly the axioms `propext`, `Quot.sound`, `Classical.choice` and enable the NanoDa kernel.
Which configurations were re-run on this tree, and how long they took: [`COMPARATOR_RESULTS.md`](COMPARATOR_RESULTS.md).

## Results new in version 1: 32 configurations, 311 theorems

| configuration | theorems | content (labels of version 1) |
|---|---|---|
| `comparatorGeoSeqV9.json` | 55 | residue identity (`lem:resform`(a), (c)); residue sequences (`def:residue`, `lem:residue-t0`, `lem:residue-rel`, `thm:residue`, `cor:korobov`, `cor:residueQU`); `lem:prefix` for level families (`rem:prefixcases`) |
| `comparatorGeoSeqV93.json` | 36 | `sec:fail` for prime bases: `def:radinv`, `lem:carrypair`, `thm:nonqu`, `cor:halton`, `cor:faure` |
| `comparatorGeoSeqV94.json` | 34 | staggered residue sequences (`def:residuestar`, `lem:residuestar-t0`, `lem:residuestar-rel`, `thm:residuestar`), `cor:dyadic`, the brick wall (`def:WF`, `thm:WF`, `ex:brickwall`) |
| `comparatorGeoSeqV95.json` | 46 | corollaries of `thm:nonqu` over prime fields: `cor:unscrambled`, `cor:sobol`, `cor:nied`, `lem:sobol`, `lem:nied`, `rem:faurerate`, the reorderings of `rem:randomize` |
| `comparatorGeoSeqV96.json` | 34 | block-periodic residue sequences: `thm:block`(i)–(iii), cases (a) and (b), `thm:blocktwo`, `prop:implied`, `cor:gauss` |
| `comparatorGeoSeqV97.json` | 17 | `sec:joint`: `lem:corrS`, `thm:corrected`, `prop:joint` ((ii) for one factor); `lem:shift`(b) |
| `comparatorGeoSeqV98.json` | 41 | `sec:count`: `def:exactrel`, `lem:reltype`, `thm:count`, `cor:layer`, `cor:N1`, `cor:residuerows`, `cor:nodesign`, `cor:density`, `prop:onerel`, `prop:blockrel`, `lem:rigid` |
| `comparatorGeoSeqV99.json` | 22 | `thm:block`(c) for s = 4 (with the kernel checks of the one-digit relaxation at every prime 7 ≤ p ≤ 109) |
| `comparatorGeoSeqV99ca.json` | 2 | `thm:block`(c) for s = 5, assembled from the per-prime checks |
| `comparatorGeoSeqV99ca5_p<q>.json` (22) | 1 each | `thm:block`(c), s = 5: the kernel evaluation of the one-digit relaxation checker at the prime q, 19 ≤ q ≤ 109 (one configuration per prime, for run time) |
| `comparatorGeoSeqV99cov.json` | 2 | `thm:coverage` as an assembly of the cited results, without its prime-power rows |

## Results kept from the previous version: 20 configurations, 440 theorems

The paper: "The results kept from the previous version are compared in the configurations of that version." These
configurations (and their statement files) date from the development version V3 of the manuscript, which was not
deposited. They cite the labels of that version; most are unchanged in version 1. The kept results are listed in
`app:lean` ("Of the results kept from the previous version, the library covers, with statements that agree up to
wording: …").

| configuration | theorems | content |
|---|---|---|
| `comparatorGeoSeq.json` | 140 | frames and the law (`def:selfsim`, `lem:t0`, `lem:frames`, `prop:law`, `prop:automaton`, `lem:cert`, `rem:onedigit`, `ex:running`), `prop:LI`, `prop:depthdir`, `thm:B2`, `lem:octave`, `cor:allprimes`, `thm:HB`, `cor:HB17` (kernel check of the range 3677 < p < 10⁴), and results of earlier versions (see below) |
| `comparatorGeoSeqS3.json`, `comparatorGeoSeqS3core.json` | 24, 16 (subset) | `thm:S3` with its automaton checks |
| `comparatorGeoSeqS4.json`, `comparatorGeoSeqS4core.json` | 27, 15 (subset) | `thm:S4` with its automaton checks |
| `comparatorGeoSeqK4.json` | 34 | `thm:K4` |
| `comparatorGeoSeqS10.json` | 23 | structural results: `prop:N2`, `prop:LI`, `prop:depthdir`, `prop:rank2`, `lem:volume` (and results of earlier versions) |
| `comparatorGeoSeqS11.json` | 1 | residue machinery of the previous version (`app:machinery`) |
| `comparatorGeoSeqV0.json` | 6 | `prop:LI` (λ-form), `lem:volume` (product form), `cor:HB17` (quasi-uniform clause) |
| `comparatorGeoSeqV1.json` | 26 | `prop:steer`(a)–(d) for every s and frame, `prop:depthdir`, `lem:volume`, `lem:antipode` |
| `comparatorGeoSeqV2.json`, `comparatorGeoSeqV3.json` | 30, 33 | `lem:ws`, `prop:steer`; and the ordered window systems of the previous version (not in version 1) |
| `comparatorGeoSeqV4.json`, `…V4s4.json`, `…V4s5.json` | 15, 2, 2 | the ordered window systems of the previous version over integer frames, with the archived data (not in version 1; data in `archive/lf_designs/`) |
| `comparatorGeoSeqV5.json` | 32 | `def:BS`, `thm:BS`, `lem:W`, `lem:D`, `lem:R`, `prop:P0`(a), (b), `thm:A3`, `thm:HB`, `tab:BSdata` |
| `comparatorGeoSeqV6.json` | 16 | `prop:P0`(c), `thm:A` (every s ≥ 3), the thresholds for s = 4, 5 |
| `comparatorGeoSeqV7.json`, `…V7d45.json`, `…V7full.json` | 23, 3, 3 | the graph rule (`def:graphrule`) and `thm:p7` (`tab:p7`), `lem:shift`(a), `thm:B2`, and the coverage theorems of the previous version (`thm:dim3`, `thm:dim45`; in version 1 replaced by `thm:coverage`, configuration `comparatorGeoSeqV99cov.json`) |

Labels of earlier versions that occur in these statement files and are not labels of version 1 (the results were
removed, merged or renamed): `thm:G`, `thm:GA`, `cor:G2`, `app:G2`, `lem:dom`, `lem:HBcov`, `lem:gform`, `lem:WFlaw`,
`cor:WF`, `sec:WF`, `prop:freeze`, `lem:hermite`, `lem:nie`, `tab:B2dir`, `thm:B3` (in version 1: `rem:B3`),
`prop:N1` (in version 1: `cor:N1`), `cor:cover`, `prop:composite`, `thm:dual`, `lem:H`, `def:LI`, `lem:ebasis`,
`lem:residue`, `prop:LIconv`, `rem:convchar2`, `def:lex`, `lem:lex`, `lem:lexcover`, `rem:lexexact`, `lem:cauchy`,
`def:MR`, `thm:MR`, `ex:MR101`, `lem:MRbound`, `thm:MRall`, `tab:P1`, `tab:LFY`, `prop:lexcap`, `prop:lexmin`,
`prop:tournament`, `tab:smallp`, `thm:LF`, `rem:p211`, `sec:dims`, `tab:dim3`, `tab:dim45`, `thm:dim3`, `thm:dim45`,
and, in the docstrings of `GeoSeq/Statements/V98.lean` and `V99.lean`, `prop:N1` and `prop:D`.

## The Palomar entry

`comparatorHeadlineSeqV4.json` (4 theorems): `GeoSeqV4.halton_not_quasiUniform` (`cor:halton`),
`GeoSeqV4.halton_bases_exist`, `GeoSeqV4.residue_quasiUniform` (`thm:residue` with `cor:korobov`, `cor:residueQU`
and `lem:residue-t0`, for the residue sequence with Faure places, θ = 1 and the Korobov check vector) and
`GeoSeqV4.residue_data`. Statement file `HeadlineSeqV4/Challenge.lean` (195 lines, Mathlib only); metadata, with the
list of divergences from the paper, in `palomar/headline-seq-v4/formalization.yaml`.

## Not formalized

As listed in `app:lean`: `lem:resform`(b) and `lem:reschange`; `prop:primepower` beyond t = 0 and the relation, and
hence the prime-power rows of `thm:coverage`; `thm:block`(c) for s ≥ 6; the prime powers in `sec:fail`, and the
digital shifts and index scrambles of `rem:randomize`; the computer-assisted tables (`tab:residue`, `tab:sobolpar`,
`tab:primepower`, `tab:practice`) and `rem:A3range`, `lem:riordan`, `lem:witness`, the binary-sequence clauses of
`thm:K4` and `thm:S4`, `rem:toeplitz`, the remaining remarks and the figures. The computer-assisted items are checked
by the programs of [`archive/`](archive/).
