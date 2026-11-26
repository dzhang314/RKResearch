# A universal ten-stage explicit method of exact order seven

Let $R$ be a nonzero commutative unital ring. An explicit method of
exact order seven exists over $R$ if and only if $7!$ is a unit.
Necessity follows from the factorial-cleared equation for the
seven-vertex tall tree. The tableau below proves sufficiency in ten
stages. The [uniform explicit lower bound](../../lean/RKCert/ReviewedNative/ERKUniform.lean)
gives nine stages, so the universal construction here leaves a
one-stage gap. It does not change the nine-stage minimum over the reals.

## Tableau

Each row gives the numerators of the strict predecessor coefficients,
all divided by the listed denominator. Unlisted entries are zero.

| Stage | Numerators | Denominator |
|:---|:---|---:|
| 1 | none | 1 |
| 2 | 4 | 27 |
| 3 | 1, 3 | 18 |
| 4 | 1, 0, 3 | 12 |
| 5 | 1, 0, 0, 3 | 8 |
| 6 | 13, 0, −27, 42, 8 | 54 |
| 7 | 389, 0, −54, 966, −824, 243 | 4320 |
| 8 | −231, 0, 81, −1164, 656, −122, 800 | 20 |
| 9 | −127, 0, 18, −678, 456, −9, 576, 4 | 288 |
| 10 | 10721, 0, −3321, 53664, −29616, 4952, −37040, −60, 720 | 20 |

$$
 \mathbf b\coloneqq\frac{1}{840}(41,0,0,27,272,27,216,40,216,1).
$$

## Reusing stage eight removes the extra denominator

The first nine rows are from E. Baylis Shanks,
[*Higher Order Approximations of Runge-Kutta Type*](https://ntrs.nasa.gov/api/citations/19650022581/downloads/19650022581.pdf#page=24),
NASA TN D-2920 (1965), Formula (16), labelled (8–10).
Let $\mathbf a$ be its original tenth row and let $\mathbf r$ be
its eighth row padded with zeros to nine coordinates. The original
tenth row has denominator $820=20\cdot41$ and weight $41/840$;
stage eight originally has weight zero.

The two rows act identically on the original stage columns for
the four rooted trees of sizes at most three. Their common
four child reads, in the order leaf, two-vertex tall tree,
three-vertex bush, three-vertex tall tree, are
$$
          (1,\,1/2,\,1/3,\,1/6).
$$
For a tree $t$, let $P_t(z)$ be its stage weight with row
$\mathbf r+z(\mathbf a-\mathbf r)$ applied to the first nine
stages. The root formula expresses this weight as the product of
the child reads. Since the row difference kills each child of size
at most three, a factor can depend on $z$ only if its child has at
least four vertices. A tree of size at most eight cannot have two
such children. Thus $P_t$ is affine and
$$
 \frac{41}{840}P_t(1)
 =\frac{40}{840}P_t(0)+\frac{1}{840}P_t(41).
$$
The first term on the right is a contribution from the existing
eighth stage. The other uses the replacement tenth row
$41\mathbf a-40\mathbf r$, which belongs to $\mathbb Z[1/210]^9$.
The earlier rows do not change. Consequently the transformation
removes the extra denominator $41$ without adding a stage or
changing any tree output through order eight.

## Exactness and base change

The [exact arithmetic checker](check.py) verifies all 85 order
conditions through order seven, as well as agreement of all 200
original and adapted reads through order eight. For the eight-vertex
tree whose root has three leaf children and a four-vertex bush as
its fourth child, the stage output and tree factorial are
$$
        \mathbf b\cdot\boldsymbol{\Phi}_t(A)=809/25920,
        \qquad t!=32.
$$
The cleared defect is therefore $-1/810$. It is a unit in
$\mathbb Z[1/210]$. The conditions checked over $\mathbb Q$ are
polynomial identities in this subring and hence remain true after
every unital map $\mathbb Z[1/210]\to R$. The defect remains nonzero.

The original Shanks formula also fails this order-eight rooted
condition. Shanks distinguishes his designation for this formula
from traditional order at the end of the report; the claim here
concerns exactly the full rooted-tree order conditions. This is
an exact arithmetic certificate, not a new Lean certificate.
