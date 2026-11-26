# Separated stage residuals and explicit stage lower bounds

The order conditions force a prefix of a sufficiently short explicit tableau to decode exact derivative polynomials. A lower bound on the dimension of the residual space of any such decoder then rules out that prefix. The lower bound on residual dimension does not assume that the original tableau supplies a final output.

- Over any field of characteristic zero, an explicit method of order 17, 18, 19, or 20 needs at least 27, 28, 30, or 31 stages, respectively.
- With coefficients in any nonzero commutative ring, the order-19 and order-20 floors are 30 and 31. The order conditions make the corresponding factorial a unit, so the field argument applies after reduction to a residue field.
- The ordered-field column is unchanged. These are mathematical proofs, not Lean certificates.

The [literal detector cutoff](ZERO-OR-ONE-SPARE-DETECTOR-CUTOFF.md) and [transfer theorem](SURPLUS-TRANSFER-AND-SPIKE-OUTPUT-CUT.md) turn additional pure rank into an additional stage. The [prefix and word-budget details](ARBITRARY-ANCHOR-PENULTIMATE-AND-CUTOFF-GUARDS.md) show exactly when the argument applies. The [degree-eight and degree-nine proof](SEPARATED-DEGREE-EIGHT-AND-NINE.md) obtains that extra rank using the chronological Gram and first-provider arguments. In degree nine the final contradiction is an actual ordinary order-nine method on at most ten of the earlier stages, versus the twelve-stage bound.

The [off-core provider rank argument](OFFCORE-PROVIDER-RANK-RENT.md) improves the recurrence for pure dimensions by ruling out shorter runs of unit rank increments. Its feed dimension is an upper capacity for the actual incoming reads. This result does not change the numerical bounds through order 20.
