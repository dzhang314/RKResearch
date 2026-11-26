# Checked factorial-unit ring interpolation on integer nodes

Over a commutative ring where n! is a unit, the Vandermonde matrix on
0, …, n−1 has unit determinant. This uses the ring determinant formula:
each positive node difference is the cast of a divisor of n!. The
inverse matrix recovers degree-<n coefficient vectors from their
integer samples, with both reconstruction identities. No field, domain,
or ambient scalar division is assumed.

The same sample coordinates give canonical evaluation at arbitrary
target nodes and evaluation of the zero-constant formal primitive.
The primitive uses the inverse of each actual unit j+1. The monomial
primitive and endpoint-1 readout are stated after multiplication by
j+1, so they retain their literal denominator-cleared meaning over
the ring. This is interpolation algebra only, not construction of a
Runge–Kutta tableau or a native order or stage-count certificate.

The [measured body](../../RKCert/ReviewedNative/RingNodeInterpolation.lean)
passed with an empty compiler log, against a stock-only Lean 4.36.0
cut. The [standalone typed audit](../../AuditReviewedNativeRingNodeInterpolation.lean)
passed with six literal clients and no output object. Its
[exact transcript](typed-audit-output.txt) contains the six named
reports, each using only propext, Classical.choice and Quot.sound.
See the [result ledger](result.json) for exact source, object, provider
and actual measurement hashes.

Integration base checked: 85e28e8e3262b2033acf78a827f58a8ea52622af.
Source-only additive evidence; no compiled artifacts, dependency or
package configuration changes, or cold-build claim.
