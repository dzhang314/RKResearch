# Distinct denominator roots in the tall RK response

Over a characteristic-zero field, the derivative-gcd quotient degree
of a nonzero polynomial is the number of its distinct roots in the
algebraic closure. More generally, the same count holds in any
extension in which the polynomial splits. Applied to the previous
tall-response bound, this gives order at most the numerator degree
plus the number of distinct roots of the denominator. These roots
are the retained poles if the submitted fraction is reduced.

Both source modules and both typed audits passed with Lean 4.36.0 and
the repository's pinned Mathlib. The [G1 audit](G1.audit-output.txt)
checks the splitting-extension version and field-map invariance. The
[G2 audit](G2.audit-output.txt) checks the algebraic-closure identity
and its application to reviewed `HasOrder p A b`. All five named
axiom checks report only `propext`, `Classical.choice`, and
`Quot.sound`. This result uses tall trees only and does not assert
an unconditional new stage-count bound.
