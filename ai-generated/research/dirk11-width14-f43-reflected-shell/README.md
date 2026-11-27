# Exact order eleven in fourteen DIRK stages over \(\mathbb F_{43}\)

The [literal lower triangular tableau](tableau.json) satisfies all 3,047
unordered rooted-tree conditions through order eleven, with an exact
order-twelve failure. This proves the upper **14 over \(\mathbb F_{43}\)**
and every nontrivial commutative ring of characteristic 43 by coefficient
transport. The reviewed ordinary ring lower bound is 13,
so the certified interval in characteristic 43 is **13–14**.
This does not give characteristic-zero coefficients, a real place,
or a lift to any ring of characteristic 43 squared.

The condition that fails is the tree with four leaf children and
one seven-vertex bush child. Its factorial-scaled residual is \(24\ne0\)
in \(\mathbb F_{43}\), with inverse \(9\). A unit residual certifies
failure after transport to every nontrivial target ring in scope.

## Exact reconstruction

Use the seven-point Lobatto grid, whose interior centered \(z=2y-1\)
satisfies \(z(33z^4-30z^2+5)=0\). Over \(\mathbb F_{43}\), the
grid used in the reflected variable is \(0,22,2,9,35,42,1\).
The actual reverse-row index list is
\((0,1,2,3,4,1,2,3,5,6)\) on this grid; equal clock masses are split
in half. Its ordinary quadrature is exact through degree eleven.

The seven-row forward prefix consists of a scaled five-row rational
order-six seed and two anchors. Evaluations at 0 and the two anchors
and the two seed integrals supply a five-component forward polynomial
lift \(\Pi\) exact on normalized rooted columns through size five.
For a suffix stage of ordinary clock \(x=1-y\) the forward block is
the anchored primitive lift, minus the evaluation lift of every
genuine suffix donor.

The reflected block \(L\) has its final three columns zero and
solves the following exact linear constraints. Write \(g\) for the
reflected cubic head, supported on the three pairs of equal clocks,
with opposite values on each pair. Its first three nonzero entries are
\(26,5,7\) as determined in the builder (the first is \(y_1^3/6\)).
Choose two affine functions \(U,V\) by the first two dirty rows. Require
\[
 L1=y,\quad Ly=y^2/2,\quad Ly^2=y^3/3+g,\quad
 Ly^3=y^4/4+U(y)g,\quad Lg=V(y)g.
\]
If \(e_t(x)=x^5-\Pi(\widehat\Phi_t)(x)\) is a size-six normalized
prefix residual, also require the weighted pairings of \(e_t\) with
\(Ly^4-y^5/5\) and \(L(yg)\) to vanish. The augmented linear system
has 43 pivots. Both residuals are actual polynomial-grade reads,
not a presumed order condition for a folded normalized transpose.

After taking the weighted reverse transpose and correcting the
forward donor block, the first three resulting representatives
literally equal the physical origin and both forward anchors.
Merging these rows and weights leaves fourteen physical stages.
The reproducible builder checks the linear system, all three row
equalities, and lower triangularity. The separate literal order
replay below, not these system claims, is the order certificate.

## Reproduce the checks

```sh
python3 -B build.py
python3 -B replay.py
```

Both scripts use only the Python standard library. The first
reconstructs every entry and compares it to the frozen JSON. The
second reads only the literal tableau and evaluates every unordered
rooted shape from canonical grafts, verifies the prescribed
abscissae and shape, and finds the next-order unit failure.
Sibling order makes no difference to the rooted conditions.
