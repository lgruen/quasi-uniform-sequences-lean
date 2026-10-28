/-
Paper: L. Gruenschloss, quasi-uniform (0,s)-sequences (geoseq paper, revision 2; LaTeX source
an earlier development version of the paper, not deposited).
Results are cited by their `\label` names, never by numbers.
Author: Leonhard Gruenschloss.
Use of AI: see the section "Use of AI" of `README.md`.
-/
module
public import GeoSeq.Statements.Prelim
public import GeoSeq.Statements.Law
public import GeoSeq.Statements.WF
public import GeoSeq.Statements.B2
public import GeoSeq.Statements.Series
public import GeoSeq.Statements.Cert
public import GeoSeq.Statements.PropLaw
public import GeoSeq.Statements.Mesh
public import GeoSeq.Statements.B3
public import GeoSeq.Statements.Steer

@[expose] public section

/-!
# Challenge (geoseq paper, stages S0–S3, S5–S7)

All GeoSeq statements (`GeoSeq/Statements/*.lean`). The compared (proved) theorems are listed in
`comparatorGeoSeq.json`; since stage S5 (S6: `Statements/B3.lean`, S7: `Statements/Steer.lean`) every statement in these files is proved
(the formalization notes of the research repository).
-/
