# Coverage: the Comparator configurations and the paper

The authoritative list of what is formalized, what differs in form and what is not formalized is the paper itself,
Appendix `app:cert`, subsection `app:lean` (paragraphs "Formalized results of this version", "Where the formal
statements differ in form", "Not formalized", "Configurations", "Palomar entry"). This file maps the configurations of
this repository to the paper. Results are cited by their LaTeX labels; the statement files
(`GeoSeq/Statements/*.lean`) give the labels in their docstrings, statement by statement.

All configurations permit exactly the axioms `propext`, `Quot.sound`, `Classical.choice` and enable the NanoDa kernel.
The Comparator runs (all 79 configurations accepted by both kernels) and how long they took:
[`COMPARATOR_RESULTS.md`](COMPARATOR_RESULTS.md).

## Results new in version 1: 58 configurations, 679 theorems

First stages (V9): 32 configurations, 311 theorems.

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

Added for version 1 after the first stages (V10): 26 configurations, 368 theorems.

| configuration | theorems | content (labels of version 1) |
|---|---|---|
| `comparatorGeoSeqV10_1.json` | 55 | upper densities of `cor:layer`(a) and `cor:density`; `prop:joint`(ii) for a general multiplier; the equality of LB(F) in `thm:block`(c) for s = 4, 5 (`blk4_LB_eq`, `blk5_LB_eq_of`; upper bound `axis_term`); `rem:randomize`(a), (b) (digital shifts, index scrambles) and (c) for level families; `rem:residuefull` (`residue_full`); `cor:N1` (offset-map form); `lem:signclass` (`sc_LB`, checker `ca_signclass`); `thm:block`(d) for s = 4 (`blk4d_block`, every prime p ≥ 11) and s = 5 (`blk5d_block_of`, `blk5d_LB_eq_of`, given the per-prime checks; `blk5d_block_proof` for p ≥ 67) |
| `comparatorGeoSeqV10_1ca5_p<q>.json` (10) | 1 each | `thm:block`(d), s = 5: the kernel evaluation of the checker at the prime q, 23 ≤ q ≤ 61 (one configuration per prime, for run time) |
| `comparatorGeoSeqV10_2.json` | 41 | `lem:reschange` over every commutative ring, `lem:resform`(b) over every field, `def:selfsim` as written (`IsSelfSim`) and the bridges of `lem:residue-t0`, `def:residuestar`, `prop:onerel`, `cor:residuerows`, `lem:corrS`, `prop:joint` to it |
| `comparatorGeoSeqV10_3.json` | 63 | `sec:fail` over every finite field and every digit code with a carry pair (`carrypairD`, `nonqu_code`, `faure_code`, `nied_not_quD`, `unscrambledD`; `carryPair_nat`); `prop:primepower` (`primepower_of_check`) with the 13 rows of the first version of `tab:primepower` on explicit models F_p[x]/(f); the prime-power rows of `thm:coverage` (`coverage_pp_of_parts`) |
| `comparatorGeoSeqV10_3x.json` | 41 | the further rows of `tab:primepower` (better f; q = 32, 64, 81, 121, 125, 128 for s = 2; 128, 169 for s = 3; s = 4, 5) and the coverage rows `coverage_pp_new` |
| `comparatorGeoSeqV10_4.json` | 37 | `def:block`(a) for every reachable design (`designNum_exists`, `designNum_order`), `thm:block`(i)–(iii) for every reachable design, the transfer of U*_s (`ustar_reachable`), `thm:block`(c) for every s ≥ 3 at p ≥ 5a*_s + 4 (`blkS_block`), the column of ones (`ustar_col0`), `a*_s ≥ s − 1`, the equality given α_0 = a*_s (`blkS_LB_eq_of`); the free diagonal for every s (`blkSd_block`, `blkSd_block_sc`); `thm:block`(d) for s = 6 given the eleven checks (`blk6d_block_of_chk`, `blk6d_LB_eq_of_chk`, every prime p ≥ 125) |
| `comparatorGeoSeqV10_4ca<k>.json` (11) | 11 each | `thm:block`(d), s = 6: the kernel evaluations of the sign-class checker at P = 6367 (121 evaluations, split for run time) |

Some unconditional forms are checked by `lake build` only, not by a configuration: `blk5_LB_eq` and `blk5d_block`,
`blk5d_LB_eq`, `blk6d_block`, `blk6d_LB_eq` (their import closures contain all per-prime evaluations at once, too long
for one configuration); the compared forms take the per-prime checks as hypotheses, and these
checks are compared separately (`…V99ca5_p<q>`, `…V10_1ca5_p<q>`, `…V10_4ca<k>`).

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

As listed in `app:lean` ("Not formalized"): `thm:block`(d) for s = 7, for s = 6 below p = 125, for s = 4, 5 below
p = 11, 23; a*_s for s ≥ 6 (the formal U*_s is defined by choice and a*_s is not evaluated); the optimality remark
after `thm:block`(d); `rem:randomize`(a), (b) for prime powers; the tables `tab:residue`, `tab:sobolpar`,
`tab:practice`, and the optimality over f, k in `tab:primepower`; `rem:A3range`, `lem:riordan`, `lem:witness`, the
binary-sequence clauses of `thm:K4` and `thm:S4`, `rem:toeplitz`, the other remarks and the figures. In
`thm:coverage`, p = 11, 13, 17 in case (d) and case (e) are not formalized. The computer-assisted items are checked by
the programs of [`archive/`](archive/).
