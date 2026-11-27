# Zero weight at the shared endpoint does not suffice

This is a scoped fixed-block obstruction, not a lower bound for all
twenty-one-stage explicit methods. Its [seed](tableau.json) is an exact
22-stage order-eleven method over \(\mathbb Z[1/11!]\), from the same
weighted reverse architecture as the shared-origin result but with a
second attempted overlap. The moved reverse width is \(4/3\), the
forward width is \(2/3\), and the reverse endpoint has physical clock
\(-1/3\). Give its two essential live donors half the scalar weight
\(-243/88000\) each and transfer their balancing copies into a pure
row of total output weight zero. This row (zero-based index 11) still
appears in four later incoming rows, so its removal is not immediate.
The paid common denominator is \(398337730560000\), and the next
bush has factorial-scaled residual \(1/165\).

Hold all matrix entries fixed except rows 16 through 21 and columns
0 through 15. Allow every redistribution in that rectangle which
preserves the clock vector \(\boldsymbol c\) and makes column 11
identically zero. The column is already zero above row 16. One
would then be free to delete stage 11, assign arbitrary output weights
to the remaining 21 stages, and try again to get order eleven.
Even with those entirely free output weights, this fixed-block
attempt is impossible over \(\mathbb F_{13}\), and hence over
\(\mathbb Z[1/11!]\).

For the proof put each removed coefficient in column 0 to make a
baseline. There are 84 allowed matrix directions: add an amount
to any other surviving column in each of the six rows and subtract
it from column 0. All 141 rooted trees in the [dual receipt](dual-mod13.json)
are spines, with at most one non-leaf child at each root. For such a
tree, \(\boldsymbol{\Phi}_t(A)\) is a product of diagonal clock
powers and strictly lower triangular matrices applied to a clock
power vector. A path in the expansion can cross the chronological
cut at most once; every changed coefficient crosses it. Thus the
vector \(\boldsymbol{\Phi}_t(A)\) is affine in the 84 directions.
The independent verifier recomputes the supplied linear combination
of these 141 vectors at the baseline and after a unit change in each
direction, directly over \(\mathbb F_{13}\). Each of the 21 surviving
coordinates is identically zero, while the same combination of the
prescribed reciprocal tree factorials is one. No choice of the
output weights can fix that contradiction.

    python3 -B audit_dual.py --full
    sha256sum -c sha256.txt

The optional full check also verifies all 3,047 ordinary rooted
equations of the unmodified 22-stage seed. The obstruction does not
apply if a fixed block, the clock vector, or the chosen seed is
changed. This is an independent arithmetic certificate, not a Lean
theorem.
