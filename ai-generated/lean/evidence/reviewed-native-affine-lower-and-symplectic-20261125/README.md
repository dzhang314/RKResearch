# Inclusive affine receivers and paid symplectic pairing

For a lower triangular tableau, the affine prefix can include the
last possible receiver. The normalized order and any shared nonzero
diagonal are preserved. In the original coordinates the combined
self coefficient is exactly the multiplier on the receiver row times
its diagonal entry. When that coefficient vanishes, the same
construction can use the shorter prefix.

At order q the inclusive prefix needs at least q/2 rounded down
distinct effective earlier clocks other than the receiver clock.
Excluding clock zero as well gives (q−1)/2 rounded down.
Effective means nonzero signed aggregate, not merely a nonzero
individual coefficient. The proof uses characteristic zero and
no order or positivity on the field.

For the native symmetric Runge–Kutta pairing, the reviewed tree order
identity cancels the pairing on the m-th and n-th tree spaces when
m+n+2≤p. The separate five-node interpolation theorem reduces the
scaled diagonal of a symmetric matrix with three nodal kernel
vectors to a single quadratic. These are independent ingredients;
the physical weak-four exclusion is not asserted here.

The neutral cubic Jacobi pencil gives the exact endpoint sign
obstruction from six weighted moments. It does not certify that a
physical weak-five chart earns both signs. No numerical stage bound
or construction is claimed.

Six modules compiled and individually kernel-replayed on Lean 4.36.0
with pinned Mathlib. The three audits found only standard axioms.
