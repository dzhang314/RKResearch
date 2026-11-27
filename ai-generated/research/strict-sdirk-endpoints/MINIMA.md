# Exact order-six strict SDIRK stage minima

Strict here means a literal common unit diagonal over a ring, or equivalently
a common nonzero diagonal over a field. All minima below require the full
ordinary rooted conditions through order six.

## Every coefficient field

| Coefficient field | Minimum stages |
|---|---:|
| Characteristic 2, 3, or 5 | No method of order six |
| Characteristic 11, 17, 163, 263, 457, or 126963077 | 6 |
| Characteristic 3533 containing a square root of 2077 | 6 |
| Any other field, including characteristic zero | 7 |

The single native theorem
[`strictSDIRKOrderSix_minimum_field_iff`](../../lean/RKCert/Research/SDIRKSixFieldClassification.lean)
pairs the upper and lower bounds. The quadratic extension of the prime field
of order 3533 has a [six-stage witness](QUADRATIC-3533.md), but the prime field
itself requires seven. Ordered-field structure does not enter the theorem.

## Nonzero commutative coefficient rings

A strict order-six tableau exists if and only if **720 is a unit**. Necessity
is the paid sixth-order tall tree. For sufficiency, the
[uniform native upper certificate](../../lean/RKCert/Research/SDIRKSevenStageOrderSixRing.lean)
specializes the archived seven-stage integral numerator tableau: its
denominators 1536 and 90 divide powers of 720. Its common diagonal satisfies
4γ=1, and its seventh-order bush has paid value 385/384, so its order is
exactly six in every such nonzero ring. This bush replaces the old rational
seventh-order tall failure, which can vanish modulo 71.

Put M=11·17·163·263·457·126963077 and D=3533·M. The
[ring support obstruction](../../lean/RKCert/Research/SDIRKSixExceptionalSupport.lean)
forces D to be nilpotent in any ring admitting a six-stage tableau. Hence
the minimum is seven on the paid locus where D is nonnilpotent.

In the other direction, the
[native CRT theorem](../../lean/RKCert/Research/SDIRKSixSquarefreeRings.lean)
builds a six-stage tableau whenever M=0 in the ring. More generally it
suffices that D=0 and [2077] be a square in the CRT component R/(3533).
The two components may contain nilpotent elements. This is a sufficiency
result on the squarefree annihilator locus, not a lifting assertion when D
is merely nilpotent.
