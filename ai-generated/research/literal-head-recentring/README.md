# From a polynomial fit modulo a subspace to an exact fit on the stages

Let the stage coordinates belong to a field. Let U be a subspace of the stage vectors, stable under coordinatewise multiplication by the clock vector c and by a multiplier vector a. Suppose that the vector whose i-th entry is (aᵢ − P(cᵢ))wᵢ belongs to U. There is a vector v such that w − v belongs to the same U, with vᵢ = wᵢ where aᵢ = P(cᵢ) and vᵢ = 0 elsewhere.

Set dᵢ equal to aᵢ − P(cᵢ). Coordinatewise multiplication by d preserves U because it is the difference of multiplication by a and the polynomial P applied to multiplication by c. There is a polynomial taking the value 0 at 0 and the value 1/x at each distinct nonzero value x among the dᵢ. Apply that polynomial in the diagonal operator to the given vector with entries dᵢwᵢ. The result lies in U and has precisely the entries of w at the mismatching stages, and zero elsewhere. Subtracting it from w gives v. All spaces spanned by U together with a fixed number of successive clock powers of w are unchanged under this replacement. The same holds for the set of clock values at which the restriction of w to a clock block is outside U, since restriction to a clock block is also a polynomial in the clock operator.

The main statement uses no restriction on the characteristic of the field. Over a commutative ring the same conclusion holds if every nonzero mismatch is a unit: the polynomial 1 − ∏ₓ(1 − x⁻¹T), with the product running over distinct nonzero mismatches, vanishes at zero and equals one at each of those mismatches. Its zero constant term lets it act on w as a polynomial in multiplication by d applied to the given vector. Without the unit hypothesis the conclusion can fail. For example, over ℤ with one coordinate, take c = P = 0, a = 2, w = 1, and U = 2ℤ.

## Application to explicit methods

In the order-12 joint-prefix argument, the measured subspace is stable under the particular multiplier supplied by the existing cubic fit. The corrected head is zero on the first mismatching joint block, so any constant fit there must come from the original subspace. This simplifies the detector used by `ERKOrderTwelveCubicAdmission.cubic_chronological_tests`; it does not prove that the required chronological transport holds, or change the characteristic-zero scope of that branch.

In the disjoint square argument at orders 14, 18 and 19, the measured mixed products establish multiplier stability before the replacement. The correction is zero because the head is already zero wherever the subspace can have nonzero entries. Thus the quotient fit was already exact on every nonzero head coordinate, including distinct stages with the same clock value. The marked order-19 overlap still requires its separate degree-nine and site-count argument.

This is a shared proof step, not an improvement to a stage bound or an admitted Lean module.
