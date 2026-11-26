# An explicit 78-stage method of order twenty

There is an explicit Runge–Kutta method of exact order twenty with coefficients in any nonzero commutative ring in which \(20!\) is a unit. The [literal tableau](tableau-20.json) uses 78 stages. The preceding 79-stage construction put the larger of its two charts on the forward side. Putting it on the reverse side allows the physical clock-one row to coincide with a forward stage while still using only 19 scalar sites.

## The two charts and the scalar sites

We use the [signed reverse construction](CONSTRUCTION.md#every-rooted-order-condition-and-the-exact-next-defect) with forward and reverse grades nine and ten. In each chart, write \(u\coloneqq 2x-1\) for the centered version of its own clock. The first 18 rows on each side are those in [the construction](CONSTRUCTION.md#the-larger-charts-and-their-literal-clocks).

| Chart | Four new grade-seven primitive rows | Five grade-eight primitive rows | Seven grade-nine primitive rows |
|:--|:--|:--|:--|
| Forward | (-5,-1/3,1/5,1/3) | (0,-1/3,1/3,-1/2,1/2) | None |
| Reverse | (-1/3,1/3,1/2,-2) | (-8/11,4/7,-2,1/2,0) | (0,-2,2,-1/2,1/2,-4/7,4/7) |

Each new primitive row at a site \(x\) reads the integral from \(0\) to \(x\) of the previous chart's decoded polynomial. The grade-eight decoder uses the two endpoints, the first two old moments, and the four new site values. The grade-nine decoder uses the two endpoints, the old mean, the first bank's weighted reading, and the five new site values. The grade-ten decoder uses the two endpoints, the second bank's weighted reading, and the final seven site values. The weighted readings are specified by `long` in [the reconstruction](construct.py): `ell4` integrates the interpolant obtained after division by \((1-u^2)^2\), with the same factor restored; `ell5` applies `ell4` to the derivative of the corresponding weighted interpolant from the second bank.

For reproducibility, [the chart verifier](verify-reflection-20.py) checks each decoder on every required tree column. For a tree \(t\) and each pair consisting of a numerical row \(\mathbf a\) and its polynomial functional \(\lambda\), the checked equality is
\[
 \mathbf a\cdot\boldsymbol{\Phi}_t(A)
 = \frac{|t|}{t!}\lambda(x^{|t|-1}).
\]
There are 486 trees on the 27-row forward side and 1,205 on the 34-row reverse side. The verifier also checks that the determinants of the two read matrices are units in \(\mathbb Z[1/20!]\). Thus these finite checks give both exact charts over that ring, and the identities remain valid after any base change in which \(20!\) is a unit.

The centered scalar sites are zero and both signs of
\[
 \frac13,\quad \frac12,\quad 1,\quad 2,quad
 \frac8{11},\quad \frac47,\quad \frac45,\quad \frac43,\quad \frac83 .
\]
They contain every reverse clock. Each pairwise difference is a unit in \(\mathbb Z[1/20!]\), as checked when the cardinal weights are formed. The 19 cardinal weights integrate every polynomial of degree at most 18. The monic nodal polynomial of degree 19 is odd in the centered coordinate, so these same weights also integrate degree 19.

## Order and stage count

With forward grade nine, the earliest erroneous child has ten vertices. Two such children in the same tree would require at least 21 vertices. Thus through order twenty there is at most one error in any term of the rooted expansion. The reverse words needed to test it have length at most ten, including the final application of the reverse matrix. The grade-ten reverse chart supplies these word values at the scalar sites. The signed copies cancel, and the two integrals in the remaining scalar test agree by polynomial integration. Both integrands have degree at most 19. This is exactly the all-tree cancellation in the linked construction, with the symmetric scalar rule in place of its original scalar rule.

The negative copies coincide with pure rows at existing scalar sites. The pure physical clock-zero row is the forward origin. The pure physical clock-one row is the endpoint row of the old order-nine method, which gives the mean in the forward chart. The reconstruction verifies the literal equalities and gives \(27+34+19-2=78\) distinct rows.

## Failure of order twenty-one

For \(k=2,10\), consider a tree of size 21 with one child a bush of size \(k\) and the other \(20-k\) children single vertices. The two defects in the order conditions on the literal tableau, in that order, are
\[
 -\frac{22363445161}{274481252204544000},
 \qquad
 \frac{686112683}{400477696819200}.
\]
Both denominators are units in \(\mathbb Z[1/20!]\), and the two numerators are relatively prime. The two defects therefore cannot both vanish in any nonzero ring in which \(20!\) is a unit. [The exact verifier](verify.py) reproduces these values from the [two trees](witness-20.json). No claim of a new Lean certificate is made.
