# Whole-block moments and clean clocks

The clean-four lemmas derive forward and reflected moment identities
on the original tableau rows, using the reviewed order predicate.
A block indicator includes every fed row with the given clock, not
just one representative. Forward chronology is established at first
occurrences. The transpose identity uses grouped masses and the
unit reverse weight. Over an ordered field the whole-block output
masses are positive; the individual output weights need not be.

The independent paid-endpoint theorem applies over ordered fields to
any tableau of sufficient order with a paid coordinate at clock one.
For the even midpoint index q between 2 and 10, it constructs a
degree-q−1 polynomial that controls the other nonzero clean clocks:
they lie strictly inside the unit interval and there are at most
q−1 distinct such clocks. Its hypotheses do not include a stage cap
or minimal defect rank.

These are reusable ingredients, not unconditional stage lower
bounds. The four modules were individually compiled and kernel
replayed on Lean 4.36.0 with the pinned Mathlib. The two audits found
only standard axioms.
