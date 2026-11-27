# Two barriers to the direct ten-stage rational Newton construction

These are obstructions to two particular construction routes, **not** lower bounds of eleven for rational strict SDIRK order seven. A different ten-stage chart remains open.

## Five scalar sites cannot contain all three standard Newton pins

A five-stage seed plus a five-site tail would have ten stages. For the usual two-order lift with a size-three decoder, its last three clocks must be 1−γ, 1−3γ, 1−5γ. But no rational quadrature with just five sites containing these three can pay degrees zero through six, for any nonzero rational γ and any signed weights.

Reflect the variable to t=1−x. Put F(t)=(t−γ)(t−3γ)(t−5γ) and write the remaining quadratic as t²−st+p. Its full hull vanishes on the nodes. The two paid conditions are I(F(t)(t²−st+p))=I(tF(t)(t²−st+p))=0, where I(tʲ)=1/(j+1). Define Mⱼ=I(tʲF). Cramer's rule gives s=2B/(7D), p=C/(7D), where

    D =  33750g⁶ −  51750g⁵ +  28075g⁴ −  7560g³ + 1125g² −  90g +  3
    B = 118125g⁶ − 193200g⁵ + 112245g⁴ − 32400g³ + 5135g² − 432g + 15
    C =  39375g⁶ −  72450g⁵ +  49035g⁴ − 16440g³ + 2943g² − 270g + 10

with g=γ and D=1800(M₀M₂−M₁²). Write γ=a/b in lowest terms and let Dₕ, Bₕ, Cₕ be the homogeneous degree-six numerators. The complete mod-four check on primitive residue pairs gives:

| parities of (a,b) | Dₕ mod 4 | Bₕ²−7CₕDₕ mod 4 |
|---|---:|---:|
| odd, even | 2 | 3 |
| even, odd | 3 | 3 |
| odd, odd | 1 | 3 |

The determinant never vanishes, including rational γ outside a near-endpoint chart. If the two remaining nodes were rational, their difference times 7Dₕ/2 would have square Bₕ²−7CₕDₕ. An integer that is a rational square is an integer square; none are 3 modulo 4. This excludes the five-site tail for all rational common diagonals. Nothing here excludes a five-site quadrature without the three pins.

## A minimal rational seed has no local order-four donor

The other direct route is a six-site tail with one literal merge into the five-stage seed. The merged row would have to be pure on every normalized rooted-tree column through size four. This cannot happen in any rational strict five-stage order-five seed.

For the first row the quadratic defect q=Ac−c²/2 is γ²/2. For the second, its vanishing needs c₂/γ=2±√2. By the [five-stage normal form](order-five-five-stage-normal-form.md), the reflected quadratic defect is a nonzero multiple of q and both first and last pairs are distinct. Applying the two initial-row observations after reflection excludes the last two rows as well.

For the third row, normalize the matrix by γ so the common diagonal is one, let x,y be its second and third clocks, and write the third row as (a,b,1). Purity through size four implies all four equations:

    a+b+1−y = 0
    a+xb+y−y²/2 = 0
    a+x²b+y²−y³/3 = 0
    a+(4x−2−x²)b = 0.

The last equality is the vanishing of Aq after the first quadratic defect of this row is zero. Combining these as E₄+E₃−4E₂+2E₁ eliminates a,b and gives y³−9y²+18y−6=0. This monic integer cubic has no rational root: a rational root would be integral, yet its reduction has no root modulo five. Thus the usual literal donor merge with a minimum-size rational seed is unavailable, not merely absent in the two known seed tableaux.

The [arithmetic replay](verify-order-seven-ten-stage-newton-barrier.py) verifies the polynomial Cramer identities, all primitive residue pairs and the cubic obstruction. It does not purport to check a new Lean stage lower bound.
