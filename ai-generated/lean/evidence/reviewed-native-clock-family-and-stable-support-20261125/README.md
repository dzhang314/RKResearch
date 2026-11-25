# Checked family rank and clock-stable fibre support

These two independent generic Lean 4.36.0 modules and their separate
single-import typed audits all exited zero. Neither audit requested object
output. The exact source, log, and artifact digests and the named stock-only
axiom reports are recorded in `result.json`.

- `ClockFamilyRank` computes the sum of the actual restricted ranks of
  the finite family's column span. Adding a member increases the rank by
  the sum of its new dimensions after removing the actual overlap in each
  original fibre. The gain is antitone in the previously selected family.
  The paid-clock staircase bounds the family's rank when each member has
  its own inclusion in the clock-local annihilator; there is no union
  payment hypothesis.
- `ClockStableFiberSupport` identifies the dimension of any clock-stable
  subspace with the sum of its actual fibre ranks. Each nonzero original
  fibre contributes at least one dimension, so a clock-stable subspace of
  dimension at most two has at most two nonzero original fibres. This is
  not a claim about the total number of stage clocks.

The two modules do not import one another. No enumeration algorithm,
families of paid shortening supports, joint profile, or numerical stage
bound are part of these checked results.
