# Denominator-free scalar transfers for the real midpoint DIRK construction

Three elementary polynomials in the first support moments are
\(A=9n_1^2-4n_0n_2\), \(B=3n_1^2-n_0n_2\), and
\(C=3n_1^2-2n_0n_2\). Write \(\eta=n_1n_2\). The
degree-three scaled reverse hull has coefficient vector
\[
 (-3\eta^3,\;3\eta^2(C+2B),\;-\eta(6BC+AB),\;ABC).
\]
Two relations suffice for both paid vanishing scalar hull moments:
\(B n_3-2\eta n_2=0\) and \(A n_4-5\eta n_3=0\).
The native formulas express both cleared moments directly through these
two relations and verify the four paid degree-six primitive pairings.
The second relation follows without division after multiplication
by \(2n_2\) from the older quadratic relation and the first relation.

The compensated reverse quartic correction is affine on every
root of the scaled hull. Lean proves a literal polynomial division
identity over any commutative ring: after multiplying by 60, the
difference between the compensated quartic read and the prescribed
affine correction is an explicit cubic quotient times the true
scaled reverse hull. Thus the reusable identity does not rely on a
prime reduction, root sampling, or any exceptional denominator.

This packet proves the transfer identities, not the two exact
moment relations for the isolated real coefficients themselves and
not the five remaining physical quartic-stage/vector gates. The
source and typed audit passed Lean 4.36.0 with matched Mathlib and
standard axioms only.
