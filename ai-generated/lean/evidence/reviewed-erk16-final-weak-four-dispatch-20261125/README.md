# Order 16, width 24: the remaining ordinary four-site case

For the reviewed order-first `RKResearch.HasOrder 16 A b`, the
ordinary four-site weak head now forces carrier rank three, fifteen
seed rows, and four physical contrast rows with distinct reflected
clocks. The original origin is inactive and no active contrast shares
its reflected clock 1. The proof excludes a repeated active origin by
retaining one representative of each numerical clock and applying the
grouped Lobatto test without assuming a diagonal identity on the
doubled group. This leaves the inactive, unshared case open and does not
change the unconditional stage lower bound.

The independent `FiniteWeightedSignGap` lemma gives a degree-paid
separator test in any ordered field. It uses an existing nodal identity,
not an extra moment at the target cut.

These three modules compiled and replayed separately with
`leanchecker` on the pinned Lean/Mathlib 4.36.0 dependency bank.
Both accompanying statement and axiom audits passed; the three named
queries report only the standard axioms. No full or cross-version
build is claimed.
