# Remaining dirty-label cases for a rational rank-three order-five port

This is a necessary profile filter, not a rational order-ten stage bound.
It complements the [one-starter FSAL obstruction](../erk10-seven-opening-pure-high/README.md)
by permitting any number of nonzero second defects. An unresolved
candidate with more than one distinct dirty clock must have exactly
two or exactly four such clocks. A single dirty clock with many
physical occurrences is not excluded here.

## Scope and low-rank consequence

Let \(A\) be a rational six-stage strictly explicit method with actual
order-five output at a nonzero horizon. Divide the clocks and
coefficients by that horizon and normalize the output to horizon one;
the pure spaces below are unchanged up to nonzero scalar multiples
of their generating columns. No sixth-order condition is assumed.

Write \(F_k\) for the span of the actual pure derivative differences
\(\boldsymbol\Phi_\tau-g_\tau(\boldsymbol c)\) for trees of sizes
at most \(k\), where \(g_\tau(X)=|\tau|X^{|\tau|-1}/\gamma(\tau)\).
Suppose \(\dim F_5\le3\). A sufficient reason for this assumption
is that appending the actual six-stage output as a true FSAL stage
leaves a space of missing degree-at-most-four model polynomials of
dimension at most one: the seven physical rows plus this missing
direction have joint rank at most eight, the five bush models are
independent, and the appended pure row adds zero secondary coordinates.
See the linked packet for the precise rank identity.

Let \(\boldsymbol d=A\boldsymbol c-\boldsymbol c^2/2\) and
\(C=\operatorname{diag}(\boldsymbol c)\).
The second clock \(e\) is nonzero, or the second row is another origin.
In particular \(d_2=-e^2/2\ne0\).
The maps \(A,C\) increase the pure grading by at most one:
adjoin a unary root or one extra leaf to a homogeneous pure tree
combination, respectively. The six output weights annihilate \(F_5\)
by order five, and \(F_4\) contains
\(\boldsymbol d,C\boldsymbol d,A\boldsymbol d\).

* A plateau \(F_4=F_5\) of dimension at least two would give an
  \(A\)-invariant subspace. The nilpotent operator induced by \(A\)
  on the quotient then acts on at most four coordinates and its fourth
  power is zero. Since the output kills that subspace, the tall
  five-tree value \(\boldsymbol b^\top A^4\boldsymbol1\) would be zero,
  whereas it equals \(1/120\).
* If \(\dim F_4=1\), \(C\boldsymbol d\) is proportional to
  \(\boldsymbol d\), so nonzero entries have clock \(e\). Also
  \(A\boldsymbol d=0\) because \(\boldsymbol d\) would be its
  eigenvector and \(A\) is nilpotent. The third row coefficient
  \(a_{32}\) is therefore zero (it is multiplied by \(d_2\ne0\)).
  That third row uses only the origin. If its clock is zero it
  duplicates the origin; otherwise its second defect is nonzero,
  so its clock is \(e\) and it duplicates the second row.
  Either duplicate contradicts the
  [strict stage floor](../../lean/RKCert/UniformERK.lean) after merging.

Thus necessarily \(\dim F_4=2,\dim F_5=3\).

## Dirty clock census

Call a physical row dirty if \(d_i\ne0\), and count its distinct clocks
(including zero if it occurs at a dirty row). If at least three
distinct dirty clocks occur, Vandermonde gives
\[
      F_5=\langle\boldsymbol d,C\boldsymbol d,C^2\boldsymbol d\rangle.
\]
The three moments killed by \(\boldsymbol b^\top\) are actual
size-at-most-five differences.

If there are exactly three dirty clocks, those moments force the
\(\boldsymbol b^\top\boldsymbol d\) aggregate at each to vanish.
Thus any clock with just one dirty occurrence has zero weight in
that occurrence. The number of possible repeated dirty clock groups
plus clean nonorigin physical rows is at most
\((\#\text{dirty rows}-3)+\#\text{clean nonorigin rows}=2\).
The output then has at most three sites, including the origin, which
over \(\mathbb Q\) is incompatible with scalar degree-four precision.
Indeed after padding to \(0,a,b\), integrating
\(X(X-a)(X-b)\) and its \(X\)-multiple forces
\((5(a-b))^2=6\).

Moreover \(\boldsymbol d^{\odot2}\in F_5\), by expanding the square
of the local two-vertex unary primitive under a root with two equal
two-vertex children, then subtracting \(C^2\boldsymbol d\) and its
ordinary pure-bush value. Hence \(\boldsymbol d\) is the evaluation of
a single quadratic \(P\) on the dirty rows: divide
\(d_i^2=d_i P(c_i)\) only on the nonzero entries.
At the same dirty clock, all \(F_5\) values, and then all ordinary
profiles through size five, are identical. Two such physical rows
can be merged preserving order five by redirecting taps and adding
output weights. This holds for equality of profiles through the needed
size, not only literal equality of coefficients: induction on tree size
shows each predecessor input retained its original profile after the
replacement. Thus dirty rows at these labels never repeat.

## Exclude five distinct dirty clocks

There are now exactly five dirty physical rows and the clean origin.
Consequently \(C\boldsymbol d=(X P)(\boldsymbol c)\) and
\(C^2\boldsymbol d=(X^2 P)(\boldsymbol c)\) at **all** physical rows
(including the origin, where both sides are zero).
Scalar order five and the two actual annihilations give
\(\int_0^1 X P= \int_0^1 X^2 P=0\).
Solving these two linear equations on the quadratic coefficients shows
\(P\) is a nonzero multiple of \(P_0=X^2-6X/5+3/10\).

Since \(A(C\boldsymbol d)\in F_5\), the primitive of \(XP\)
evaluated at the clocks is in \(F_5\) too: write \(XP\) in the
scalar basis \(X,X^2,X^3\) and replace each \(A\boldsymbol c^j\)
by its primitive plus its actual pure tree defect in \(F_5\).
This operation uses only derivative size at most five; in particular
it does not apply \(A\) to \(C^2\boldsymbol d\).
Thus for some quadratic \(R\),
\(\int_0^{c_i} X P(X)\,dX=P(c_i)R(c_i)\) on the five dirty rows.
Both sides are polynomials of degree at most four in \(c_i\).
Five distinct values force a polynomial identity.
But the Euclidean remainder of the primitive of \(XP_0\) on
division by \(P_0\) is \(27/2000-3X/125\ne0\).
This excludes the five-clock alternative.

For four dirty clocks, exactly four physical rows are dirty.
The sole other nonorigin row is fully pure through size five,
because all of \(F_5\) vanishes there. It must have some nonzero
clock \(\eta\), or it would merge with the pure origin.
Its incoming row gives actual order four at \(\eta\); it needs at
least four predecessors by the strict tall four-chain, so it is
row five or six. On all its predecessors \(C\boldsymbol d\) equals
\((XP)(\boldsymbol c)\). The exact primitive read through
degree three and \(A(C\boldsymbol d)=0\) at this row give
\(\int_0^\eta XP(X)\,dX=0\).
The final output additionally requires
\(\int_0^1 (X-\eta)XP(X)\,dX=0\) by eliminating the clean mass
from the two actual \(\boldsymbol b^\top C^j\boldsymbol d\)
moment equations. These are necessary, not yet sufficient,
constraints on the four-clock port.

## Replay

    python -B audit.py
    sha256sum -c sha256.txt

From the project's ai-generated/lean directory:

    lake env lean RKCert/ReviewedNative/ERK10RankThreePortLabelScalars.lean

The checked scalar statements give the weighted quadratic shape,
the exact remainder, and failure of a quadratic multiple of the
primitive. The grading, quotient and physical merge are mathematical
arguments, not a claimed native all-tableau endpoint.

The [two-label continuation](../erk10-rank-three-port-two-labels/README.md) excludes two distinct dirty clocks under these same order-five rank assumptions. The present intermediate census is kept separately.
