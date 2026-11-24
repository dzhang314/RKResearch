# Native order-fifteen first marked escape

The reviewed field-theoretic consumer is
`RKResearch.Certified.Graded.order15_first_escape_chart`. It assumes
strict lower triangularity, `RKResearch.HasOrder A b 15`, and at most
22 stages over a characteristic-zero field. No physical rank, output
sign, distinct node or synthetic tableau is assumed.

* The last original stage is proved to have nonzero output weight.
  The mark is the original last coordinate exactly when the first
  reverse seed vanishes; otherwise the first seed retains its reverse
  dimension. The generic `OptionalTerminalMark` module derives their
  exact one-unit balance, reverse cap, marked ordinary defect rank,
  and constant-Cauchy separation. Its field hypotheses do not require
  characteristic zero or an order on the field.
* With `d = terminalDebit A b`, actual marked tree ranks at grades
  6 and 7 are 13+d and 15+d. The first escape has rank 8+d and is
  literally the length-(r+3) head chain on the original tableau.
* If there is a nonzero polynomial alias through degree seven, its
  degree is exactly seven, the terminal is marked, and all such aliases
  are scalar multiples of this one. The actual marked grade-seven
  tree space is the degree-six coefficient band plus the first escape.
  Otherwise the actual marked grade-eight tree space is the degree-seven
  coefficient band plus the first escape, and an actual degree-eight
  mesh polynomial is earned.
* Every paid polynomial G through degree eight has zero constant term.
  `order15_escape_adjacent_packet` returns G=X D, deg D≤7, and
  `RKCert.ReviewedNative.JacobiMoments.MomentDifferences D 5`, giving
  exactly the shared six adjacent Jacobi moment differences. In the
  unmarked case the seven individual moments are zero. The shared
  scalar theorem `JacobiMoments.signedSlope_band` can consume this
  packet downstream, but its implementation (whose import closure still
  includes archived geometry) is not imported by this proof.

This is the first chart only, not the through-grade-twelve staircase
and not a proof of the 23-stage obstruction. Every tree, elementary
weight and order condition used here is the human-reviewed native one.

## Verification

Four additive modules plus one independent, single-import combined
chart-and-moments consumer. Lean 4.36.0
(`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`) and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, with the reviewed human
sources pinned at `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
The previous grade-five seal, SHA-256
`d316335a4022bb38880e2b0b3c6e2d985fb624f88def5af746c74b613df263f8`,
and all overlapping source hashes were preserved.
All 24 audited declarations report only propext, Classical.choice
and Quot.sound. No legacy tree or order conversion, no scalar replay,
no human-source edits, and no remote writes.

The transitive project-source manifest lists the precise external
module hashes, including the shared tree-free JacobiMomentPorts.
Use the supplied scoped checker with OptionalTerminalMark,
ERKOrder15PaidFrame, ERKOrder15Alias, ERKOrder15EscapeMoments,
then AuditReviewedNativeERKOrder15FirstEscape.
