# Clean stage profile in the order-eight four-off branch

This Lean certificate proves the normalized polynomial shape from an
actual order-eight tableau and the stated clean-tap placement, terminal
profile, and polynomial hypotheses. In particular, it derives a shared
clean primitive and the resulting shape from the exact coefficients on
the three clean stages. It does not derive all these hypotheses from the
four-off census or exclude that branch.

The two named modules were checked with Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, against the reviewed RK
definitions. The separate no-output audit specializes the theorem to a
literal ten-stage tableau and reports the axioms for three named lemmas.
Each body and the audit exited successfully. The exact source and output
hashes are recorded in [acceptance.tsv](acceptance.tsv), and the
[typed audit output](typed-audit-output.txt) records the three standard
axiom reports.
