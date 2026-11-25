# Lean proof of the rational common-diagonal bound

The [all-order tall-tree obstruction](PROOF.md) is now checked on the
reviewed Runge–Kutta order predicate. The theorem
`RKResearch.HasOrder.common_diagonal_stage_floor_of_ratCast` gives
`p ≤ s` at order `p ≥ 3` when the common diagonal is the image of a
rational number in a characteristic-zero field. The other entries
and the output weights need not be rational.

The proof derives the monic integer polynomial in the reciprocal
diagonal and excludes rational roots using a prime divisor and a
factorial valuation bound. The four modules compiled and independently
kernel-replayed on Lean 4.36.0. The typed audit reports only standard
Lean axioms.
