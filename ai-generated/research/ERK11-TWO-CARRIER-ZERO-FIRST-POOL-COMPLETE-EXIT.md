# Two carriers and two new boundaries: the zero-first-pool branch is excluded

**Scope.** This combines the earlier exact results for the maximal,
all-live, half-clock, seventeen-stage ERK11 chart with exactly two
quadratic carriers, at physical 2 and 16, and both seventh-from-the-end
boundaries genuinely new. Assume the sum of the first pure response
at each active clock is zero after weighting by the actual output
weights. Under these specific hypotheses there is no tableau over
an ordered field. This does not exclude all seventeen-stage
tableaux, or even this carrier count with nonzero first pools or
a repeated boundary.

The pure response is $F=\theta As$ in the established notation
and a pool is $\nu_x=\sum_{c_i=x}b_iF_i$ over noncarriers.
An active row has $F_i\ne0$. The endpoints and the two carrier
rows are response-zero, leaving at most thirteen active physical
rows. A live-weight active site needs at least two active rows
if $\nu_x=0$. Thus there are at most six active clocks. This
count uses no sign.

## At most five active clocks or thirteen active rows

The complete at-most-five branch is covered by the
[pooled census](ERK11-TWO-CARRIER-FOUR-PAIR-EXIT.md),
[Jacobi doubling reduction](ERK11-TWO-CARRIER-JACOBI-POOL-EXIT.md)
and the [final omitted-pair exclusion](ERK11-TWO-CARRIER-OMITTED-PAIR-EXIT.md).
No case of nonzero first pool is included.

With six active clocks and thirteen active rows, there are five
pairs and one triple. If the triple ordinary scalar mass is zero,
the [cross-front census](ERK11-SIX-GROUP-TRIPLE-CROSS-PAIR.md) forces
one crossing in an ordered field and the [exact one-cross exit](ERK11-ZERO-MASS-TRIPLE-ONE-CROSS-EXIT.md)
excludes it. If that mass is nonzero, use the
[complete nonzero-mass atlas](ERK11-NONZERO-MASS-TRIPLE-COMPLETE-EXIT.md).
Weights of the individual physical triple rows are not combined
before their necessary pure-moment tests.

## Six active pairs and twelve active rows

Here there is one internal dormant noncarrier. The
[clock separation theorem](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md)
excludes its sharing an endpoint or active clock in an ordered field
and forces it into physical 8, 9 or 10. It supplies nine distinct
ordinary scalar sites, all with live mass. The following **inner**
atlas excludes every remaining genuine-nine clock geometry over
characteristic zero given those premises.

The calibrations are left plateau $a$, left half $h=a/2$,
right plateau $d=1-b$, right half $e=1-b/2$. Each plateau is a
full active pair. Thus $a=d,a=e,h=d$ are impossible, and no front
extra can be the other plateau. The two extra reads of a front
have genuine distinct clocks under the new-boundary premise.
The only calibration overlap left is $h=e$.

* **Shared half $h=e$.** The two extra sets are either equal or
  different two-element subsets of the three free labels.
  The equal choice is covered at the [center](ERK11-NINE-SITE-HALF-SAME-CENTER-EXIT.md)
  and [edges](ERK11-NINE-SITE-HALF-SAME-EDGE-EXIT.md).
  The different choice is covered at the [matched center](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-MATCHED-EXIT.md),
  [opposite center](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-OPPOSITE-EXIT.md)
  and [edges](ERK11-NINE-SITE-HALF-DIFFERENT-EDGE-EXIT.md).
* **Four distinct calibrations, neither front selects the opposite
  half.** Both choose the free pair. The
  [same-free exit](ERK11-NINE-SITE-DISTINCT-SAME-FREE-EXIT.md)
  covers every inner order.
* **Four distinct, both select the opposite half.** If they also
  select the same free label, the three-crossing
  [central](ERK11-NINE-SITE-DISTINCT-THREE-CENTER-EXIT.md) and
  [edge](ERK11-NINE-SITE-DISTINCT-THREE-EDGE-EXIT.md) exits apply.
  If they select different free labels, use the
  [central](ERK11-NINE-SITE-OPPOSITE-HALVES-CENTER-EXIT.md),
  [matched edge](ERK11-NINE-SITE-OPPOSITE-HALVES-EDGE-MATCHED-EXIT.md)
  and [opposite edge](ERK11-NINE-SITE-OPPOSITE-HALVES-EDGE-OPPOSITE-EXIT.md)
  exits. Their affine and moment-pivot drops are checked in the
  companion notes.
* **Four distinct, just one selects the opposite half.** Put
  the dormant physically at 9, or at 8 by actual reflection if
  needed. At 9, use the
  [matched and zero-affine central exits](ERK11-NINE-SITE-ASYMMETRIC-CENTER-ATLAS.md)
  and the [opposite central exit](ERK11-NINE-SITE-ASYMMETRIC-CENTER-OPPOSITE-EXIT.md).
  At physical 8 there are two actual chooser orientations.
  For the left chooser and the half label at 10 or 9 use,
  respectively, the [fixed-half](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H10-EXIT.md)
  and [variable-half](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-EXIT.md) exits.
  For the right chooser and the half at 10 or 9 use the separate
  [fixed-half](ERK11-NINE-SITE-ASYMMETRIC-RIGHT-FIXED-E-EXIT.md)
  and [variable-half](ERK11-NINE-SITE-ASYMMETRIC-MIRROR-LARGE51-EXIT.md)
  exits. These are separate geometries; exchanging chooser at fixed
  dormant 8 is not asserted to be a symmetry of the tableau.

All uses of reflection in this ledger exchange the actual two-front
mixed grade-five bridges; they do not require full ordinary reverse
order eleven. The inner arithmetic is characteristic zero; the
separation and earlier triple/low-site exits use ordering. The
ordinary seventeen-versus-eighteen question remains open.
