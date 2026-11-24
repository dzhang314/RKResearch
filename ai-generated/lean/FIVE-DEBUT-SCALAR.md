# Field-safe five-debut scalar tail

The three additive modules depend only on published baseline `182d77cc`
(`RKCert.DirkTrace`) and pinned Mathlib. Import `RKCert.FiveDebutScalar`.
No physical-array cuts, rank estimates, tableau or stage floor are asserted
by these three modules.

`RKCert.FiveDebut.five_scalar_impossible` takes five distinct nonzero
characteristic-zero field clocks in physical debut order, a common nonzero
scaling of the four differentiated nodal amplitudes, and precisely three
primitive observations: the cubic nodal primitive on the first three sites,
and the two refunded quartic primitives through the fifth site. The paired
Euler eliminations solve the affine coefficient relation at the symbolic
fourth clock, and the final determinant at distinct clock v is exactly
(v-u)^2/252. No specialization, stage deletion, numeric search or
dilation of physical clocks is used. Its upstream physical/Hankel layer
is a separately composable overlay.

Warning-free direct file check with Lean v4.36.0, independent three-module
Leanchecker replay, and standard axioms only. Exact logs and source
SHA-256 receipts included.
