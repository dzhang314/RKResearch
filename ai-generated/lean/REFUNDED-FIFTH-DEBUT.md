# A grade-five single head cannot last through grade seven

**Scope.** Let A,b be an original lower triangular classical rooted-tree
tableau over any characteristic-zero field, of order p≥10. Let the
genuine defect space F₅ contain a clock-invariant coordinatewise
multiplicatively closed subspace U. There is no stage vector w such
that F₅,F₆,F₇ equal U plus, respectively, the first one, two and three
clock powers of w. The hypotheses concern the actual full array.
There is no assumption on F₈, a projected tableau, an arbitrary
nonalgebraic invariant hyperplane, or an independently specified
adjoint array. At p14/r=1, a separate physical core theorem supplies
this algebra and the already checked E_q staircase supplies the three
band equalities. The generic obstruction does not by itself exclude
all possible 18-stage order-14 methods: the other chart must also be
excluded.

## Why five actual distinct clocks and the fifth explicit row exist

On each clock, the clock-invariant finite-product algebra U has its
physical support indicator, from the established core-indicator and
clock-fiber lemmas. Since U is in F₅ the integral of this indicator
against the output row vanishes. A nonzero aggregate-weight clock
cannot occur exclusively inside the support of U. In particular at
least five distinct nonzero clocks occur *outside* the core, by the
ordinary order-p active-node count. Take first physical appearances
of distinct outside clocks z₁,…,z₅; origins, repeated clocks and
interleaved masked or zero-weight rows are never removed.

At any of the first three fresh rows, if the head were zero, all F₆
and F₇ elements would vanish there. Clear the previous distinct
outside nodes with H, their monic nodal polynomial, and use xH minus
the true U-mask. It is zero strictly before and nonzero at the pivot.
The genuine commutator CA−AC−A², of cost two, is zero there by
cleanliness, and triangularity prices it as −a_ii² times the pivot
input. Thus a_ii=0. For k up to deg H≤2 the same cleared inputs
x^(1+k)H (degree≤5) cost no extra grade for the mask. Their primitive
outputs vanish there at grade six. The fixed shifted-Hilbert
detector at the nonzero current clock forces H=0, impossible. This
proves the first three head amplitudes are nonzero. At the fifth debut,
clear x times the four prior site factors. Its commutator vanishes on
all three nonzero head amplitudes with distinct clocks, killing its
quadratic head multiplier. Its current value also vanishes. This again
forces the physical diagonal to be zero, this time regardless of the
fifth amplitude.

## Two paid cuts suffice

The prefix compatibility space consists of head polynomials whose
numerical product with w is a scalar node function (vanishing at
zero) plus a genuine U-vector throughout the same earlier physical
prefix. Its intersection with polynomials of degree below d grows
by at most one when d increases by one, no matter how many repeated
clocks have different amplitudes or how many origins carry w. To fit
an input take P=x f of degree at most j, a compatible q of degree<d,
and impose P(z_i)=w_i q(z_i) at t old distinct clocks. On all physical
rows strictly before the next debut, a genuine U-correction then
clears the entire input. At each chosen old output row A sends it to
zero; a chosen frontier row is covered too when its diagonal has
already been refunded. The actual grade-(j+1) primitive discrepancy
is in U+w times a compatible polynomial of degree at most d. The
same prefix-compatibility space appears on both sides. If j≥t+2 and
d old diagnostic head amplitudes are nonzero at distinct clocks,
the paired rank-nullity lemma produces nonzero P with *all* selected
primitive values zero. No putatively distinct observations are counted
without paying them.

Apply the cut first with three old inputs, three old outputs, j=5 and
d=1, strictly before the fourth. Apply it again with four old inputs,
five outputs through the refunded fifth, j=6 and d=2. Only two of its
old amplitudes need be known nonzero. In the first cut JP=x² V₃ G,
where V₃ is the monic old-node polynomial and G is nonzero of degree
at most one. Differentiating at the old nodes and applying the two
barycentric zero sums to q gives a null direction of the symmetric
matrix H₃=Σ(z_i²/w_i) (1,z_i)ᵀ(1,z_i). Thus H₃ is singular. In the
second cut JP is a nonzero scalar multiple of x² V₅. Differentiating
shows *all four* old w_i are nonzero, and the two barycentric sums
on four old sites give H₄(−z₅,1)ᵀ=0.

No separate fourth-debut cut is needed: if H₄ is nonzero its rank-one
direction is (1,z₅). Subtracting the fourth atom of nonzero weight
and distinct direction (1,z₄) would give nonsingular H₃. The exact
determinant is a nonzero multiple of (z₄−z₅)², valid also over
unordered fields. Thus H₄=0. Its three vanishing moments force
w_i=t z_i² V₄′(z_i), i≤4, with one common nonzero t: differences
of the four monic cardinal numerators have degree≤2, so their paired
weights must all agree. This uses Mathlib's nodal polynomials and
top Lagrange interpolation coefficient, not a numerical rank test.

## Scalar closing data

At the first three clocks the primitive of x V₃ is w times an affine
polynomial. No fourth diagonal refund is used. Through the fifth
clock the primitives of x V₄ and x² V₄ are respectively w times affine
and quadratic polynomials; here the fifth refund is essential. The
separately archived field-valid four-knot Euler skeleton and its
five_scalar_impossible theorem rule out precisely these three actual
observations with the common four-amplitude scale. Their proof makes
no assumption on the sign, order or magnitude of any unknown scalar.

The final ordinary-array lemma is RKCert.FiveDebut.no_grade5_head.
RKCert.FiveDebut.original_refunded_five exposes the whole physical
reduction independently of the final scalar algebra. The proof uses
the previously verified masked-prefix and paired-kernel toolkit,
Mathlib finite-dimensional rank-nullity, polynomial degree and
derivative APIs, native Lagrange nodal cardinals and barycentric sums.
It never deletes rows, divides by an unknown fifth weight, or tests
only one representative of an unpriced equal-clock class.
