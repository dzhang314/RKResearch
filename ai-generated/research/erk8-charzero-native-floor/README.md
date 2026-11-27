# Native ERK8 stage minimum over characteristic-zero rings

For every characteristic-zero commutative ring \(R\), a strictly
explicit tableau \(A\) with \(s\) stages and order at least eight has
\(s\ge11\). For each width \(s\), an exact order-eight explicit
tableau exists if and only if \(s\ge11\) and \(8!\) is a unit of \(R\).
Thus the minimum is exactly **eleven** whenever order eight is
admissible. There is no order-eight tableau if the unit condition
fails. These statements apply to rings with zero divisors and to
unordered characteristic-zero fields; no ordered-field or real
structure is used.

## Checked endpoints

- **RKResearch.Certified.Graded.FourOffNewton.no_four_off_charZero**
  consumes a literal strict width-ten tableau and reviewed HasOrder 8.
  It rules out exactly four off clocks.
- **RKResearch.Certified.ERK8CharZero.no_order8_fin10** closes both
  branches of the paid width-ten census over every characteristic-zero
  field. Its caller supplies only strictness and literal order.
- **RKResearch.Certified.ERK8CharZero.stages_at_least_eleven_field**
  appends isolated zero-weight stages for the reduction from any
  smaller width to width ten.
- **RKResearch.Certified.ERK8CharZero.stages_at_least_eleven** is the
  specialization to arbitrary characteristic-zero commutative rings.
- **RKResearch.Certified.ERK8CharZero.exact_order_eight_exists_iff**
  characterizes existence at an arbitrary width, with failure at
  order nine included.

## Proof and scope

The paid census applies because the scalar 11 is nonzero in
characteristic zero. It earns the even horizon and the one-/four-off
split. The one-off branch uses the existing checked literal
ERK8OneOffFin10 endpoint.

In four-off, the earned physical geometry and terminal profile
produce the checked normalized quadratic shape and its nonzero
clean evaluations. The new generic terminal and physical Newton
transfer from the [characteristic-11 four-off packet](../erk8-char11-native-four-exclusion/README.md)
applies over characteristic zero without changes. The remaining
adapter identifies the actual four-node barycentric measure with
the earlier characteristic-zero scalar moments. For every positive
power the origin contributes zero, and the factor of the clock in
each numerator cancels the identical factor of its four-node
cofactor, giving the precise three terms consumed by both checked
chronological scalar closures (first clean at physical 4 or 5).

The lower result for rings chooses a prime disjoint from the
multiplicative set of nonzero natural scalars, then maps the
coefficients into the fraction field of that prime quotient. An
arbitrary maximal ideal of the original ring would not suffice:
it might kill a nonzero integer. The unital map preserves the
reviewed tree polynomial equalities, strictness and stage count.
The exact-width result pairs this lower theorem with the existing
eleven-stage factorial-localized upper and the literal tall-tree
factorial-unit check. Padding preserves both order eight and
non-order nine.

The arbitrary-ring result in **positive characteristic** remains a
[mathematical source proof](../erk-eight-char11/README.md), not part
of this native endpoint. The native characteristic-11 census now
forces one off; its paid one-off closure and the remaining native
positive-characteristic four-off specializations are separate.
In particular, this characteristic-zero release does not claim
that characteristic-zero one-off reasoning transfers automatically.

## Verification

From ai-generated/lean with the matching Mathlib revision:

    lake build +RKCert.ReviewedNative.ERK8CharZeroStageFloor
    lake build +RKCert.ReviewedNative.ERK8CharZeroExactWidth

The first target does not require rebuilding the separate numeric
eleven-stage tableau certificate. The adjacent log records the three
new modules on Lean 4.36.0, and every endpoint uses only propext,
Classical.choice and Quot.sound. The source list is hashed. No
claim is made here of a whole dependency build on another release.
