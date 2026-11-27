# Five stages over every paid local coefficient ring

Strict SDIRK order five requires at least five physical stages over every nontrivial commutative ring, by the existing [common-diagonal floor](../../lean/RKCert/ReviewedNative/NonsingularDIRKStageFloor.lean). The upper endpoint of five holds over **every local commutative ring in which 30 is a unit**, including every admissible field. No ordered-field machinery or domain assumption is needed for the upper bound. Here, “strict” over a ring means that the common diagonal is a unit.

There are two charts. The first is the archived [repeated-clock tableau](order-five-five-stage-repeated-clock.md), with parameter 1 and diagonal 1. The second is the same scalar family at parameter −1/2, giving diagonal 1/4. The new tableau has these lower rows and weights:

| Row | Nonzero-range entries |
|---:|---|
| 1 | 1/4 |
| 2 | −3/2, 1/4 |
| 3 | 1971/6200, 819/6200, 1/4 |
| 4 | 1642391/6480000, −31991/28080000, 1665289/8424000, 1/4 |
| 5 | 107/270, −2/195, 2850760/18855369, −2000/53719, 1/4 |

The output row is (47/81, 1/1404, 5645875/56566107, −50000/53719, 5/4), and the clocks are (1/4, −5/4, 7/10, 7/10, 3/4).

Using one integer scale for both matrix and weights, the two scales are

    D₁ = 4176902359476000
    D₂ =  140283945360000

and satisfy the explicit receipt

    134909209 D₁ − 4016871581 D₂ = 324000,    324000 · 75 = 30⁵.

In any local ring with 30 a unit the combination is a unit. If neither original scale were a unit, both summands would belong to the maximal ideal. Thus at least one scale can be inverted. The generic integer-scaled rooted-tree transport gives the selected tableau's order-five identities; the diagonal numerator divides the selected scale (exactly or by 4) and therefore becomes a unit.

Exactness also survives this selection. For the two charts respectively, the order-six cleared tall and bush discrepancies are (−151, −29/550) and (11/64, −217/3200). Their integer combinations with coefficients (−5, 14300) and (−8832, −22400), respectively, equal 1. Equivalently, in each chart the corresponding combination of integral scaled discrepancies equals Dᵢ⁶. If both sixth conditions held, this unit would be zero. A discrepancy test alone that can vanish in positive characteristic would not suffice.

The [native Lean module](../../lean/RKCert/ReviewedNative/SDIRKFiveLocal.lean) checks both full sets of order-five conditions, both exactness receipts, the local-ring cover and the minimum, with the reviewed HasOrder contract. The companion [standard-library replay](verify-order-five-paid-local.py) uses unordered rooted trees and rational arithmetic.

**Further coefficient domains, by CRT.** Over any nontrivial ring of finite characteristic m prime to 30, a tableau exists as well: over each local factor Z/qᵏ of Z/m use whichever scale is a unit; combine the tableau entries by CRT and map them to the target. In each prime-power factor the same combination of discrepancies selected for that factor forces a unit. This exactness cannot disappear after mapping Z/m to a ring of characteristic exactly m (the prime subring map is injective). No assertion follows here for an arbitrary nonlocal characteristic-zero ring with only 30 inverted, where the two scales can both be nonunits.
