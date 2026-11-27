# Two sharp small-characteristic order-six endpoints

The previous [four-multiplier bound](finite-characteristic.md) left both 7 and 3533 as potential six-stage exceptions. The new conclusions distinguish the physical clocks from the scalar chart, and distinguish the characteristic from the coefficient field.

- **Characteristic 7:** Every common-diagonal order-six tableau over a nontrivial commutative ring needs at least seven stages. This includes zero or nonunit common diagonal and does not assume reducedness.
- **The prime field of size 3533:** The same seven-stage lower bound holds, and transfers to any ring admitting a unital map to this field. In a general field of characteristic 3533, a six-stage strict tableau requires a square root of 2077. The obstruction does not apply when the root exists.

Seven stages also suffice over every nontrivial ring of characteristic 7 and over the prime field of size 3533: the archived [rational seven-stage tableau](../../lean/RKCert/ReviewedNative/RationalStrictSDIRKSevenStageSixUpper.lean) has integer scales 1536 for the matrix and 90 for the weights, with common diagonal 1/4. Only the primes 2, 3 and 5 occur in the scales, so its cleared order identities specialize to these rings. No order-six tableau is possible over a nontrivial ring where one of 2, 3 or 5 is not a unit, by the quadrature order conditions.

## Proof

For a hypothetical strict six-stage tableau, use zero-based indices and normalize by z = γ⁻¹, so B = zA has diagonal one. Write u = B₁₀ and v = z(c₅−c₄), where c are the original clocks. The [paid chart](../../lean/RKCert/ReviewedNative/SDIRKSixPaidPhysical.lean) separately exposes the scalar equations and the normalized clocks at indices 0, 1, 2, 4, 5:

    1, 1+u, 1+2u, z−1−v, z−1.

The chart's zero-tap alternative is excluded using powers of the already-paid 30. In both characteristics exactly the second of the four obstruction multipliers vanishes. The remaining receipts force the cubic terminal branch, using only unit denominators dividing a power of 30. In this branch hThree = vThree = 0 gives 8(u+v) = 33z²−440z+344 and 8uv = 21z²−280z+216. Express the symmetric terminal polynomial in u+v and uv, then reduce it against factorThree. The resulting univariate gcd is z−1 in characteristic 7 and z−1645 in characteristic 3533. The [Lean proof](../../lean/RKCert/ReviewedNative/SDIRKSixSmallCharacteristicExclusion.lean) checks both modular reductions with integer linear-combination receipts.

In characteristic 7 this gives v=−u and u²=1 in every field. The five prescribed clocks lie in {0,1,2,3} or {0,1,−1}. Let P be the product of the linear factors for the distinct prescribed clocks. The required quadrature values of P and xP are equal and nonzero, both 1 in the first case and both 5 in the second. Only the unprescribed clock can contribute. It must equal 1, but P(1)=0. Specialization to fields transfers the result to commutative rings; the explicit lower bound handles a nonunit common diagonal.

In characteristic 3533 the reduction gives u+v=824 and uv=524, hence (2u−824)²=2077. Repeated squaring yields 2077^1766 = −1 modulo 3533, so Fermat's little theorem excludes a square root in the prime field. The [independent arithmetic script](checkSmallCharacteristicExclusions.py) verifies the monic reductions, the two moment masks and all square residues.
