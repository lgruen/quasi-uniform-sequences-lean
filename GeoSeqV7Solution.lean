/-
Paper: L. Gruenschloss, low-discrepancy quasi-uniform digital sequences in every dimension (geoseq
paper, development version V3, not deposited; COVERAGE.md relates its labels to `paper/main.tex`).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.V7P7
public import GeoSeq.V7Shift
public import GeoSeq.V7B2
public import GeoSeq.V7Dim
public import GeoSeq.V7Dim45

@[expose] public section

/-!
# Solution (geoseq paper V3, stage V7)
-/

#print axioms GeoSeq.graphRule_unique
#print axioms GeoSeq.graph_resp
#print axioms GeoSeq.graphSig_neg
#print axioms GeoSeq.graph_cert
#print axioms GeoSeq.graph_seq
#print axioms GeoSeq.p7chk_sound
#print axioms GeoSeq.p7chk_111
#print axioms GeoSeq.p7chk_116
#print axioms GeoSeq.p7chk_161
#print axioms GeoSeq.p7chk_166
#print axioms GeoSeq.p7chk_small
#print axioms GeoSeq.p7_LB
#print axioms GeoSeq.p7_LB_eq
#print axioms GeoSeq.p7
#print axioms GeoSeq.p7_exists
#print axioms GeoSeq.shift_seq0
#print axioms GeoSeq.cert_shift
#print axioms GeoSeq.shift_prefix
#print axioms GeoSeq.shift_prefix_q4
#print axioms GeoSeq.B2_kappa
#print axioms GeoSeq.dim3_primes
#print axioms GeoSeq.dim3_every_prime
#print axioms GeoSeq.dim3_of_small
#print axioms GeoSeq.dim3
#print axioms GeoSeq.edP211_valid
#print axioms GeoSeq.dim45_primes
#print axioms GeoSeq.dim45_of_small
#print axioms GeoSeq.dim45_q4
#print axioms GeoSeq.dim45
