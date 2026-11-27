# The clean scalar schedule in the nonhalf five-carrier endpoint branch

Continue the
[all-live maximal endpoint case](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md),
with \(p\ne1/2\).
Thus the four separate tail carrier clocks are the labels of
rows 12,14,15,16, the clean tail clocks are
\(\theta=c_{13}\ne1\) and \(1\), and the global nonzero
quadratic defect at a carrier is a fixed quadratic in its label.
Work over a field paying \(11!\) given these premises.

If the number \(N\) of distinct quadratic carrier clocks is
4 or 5, the literal first eleven have at least **five**
distinct clean clocks. If \(N=5\), there are exactly five
early clean clocks, and neither \(\theta\) nor 1 belongs
to that set. Writing \(H_5\) for the monic hull of the five
early clean nodes in the ordinary variable \(X\), one has
\[
                    (X-\theta)H_5(X)
                      \in \langle XR_4(X),XR_5(X)\rangle ,
\]
with the fixed anchored Jacobi polynomials \(R_4,R_5\) of
[the earlier packet](ERK11-ARBITRARY-PREFIX-JACOBI-GATES.md).
In particular the seven clean nodes and their exact ordinary
scalar quadrature have become a single Jacobi family with
a distinguished root \(\theta\). This narrows a remaining
carrier-count case but does not exclude it.

## Erase the carriers from the two scalar quadratures

Use \(Z=(1-X)/y\) as the physical reflected weight variable,
where \(y=1-\theta\ne0\), and let \(\kappa=2-1/t\).
The exact early weights are
\[
       Z(Z-1)J(Z),\quad Z(Z-1)R(Z),\qquad
                 J(Z)=Z(Z-1),\quad R(Z)=1-\kappa Z .
\]
Here \(\kappa\ne1\) since \(t\ne1\).
For either exact prefix row \(\rho\), the five pure roots
\(\delta Z^j\) for \(0\le j\le4\) are paid (grade \(2+j\le6\)).
At any carrier label the defect is the same fixed nonzero
value. If there are at most five carrier labels, Vandermonde
on these five powers therefore kills the pooled coefficient
of \(\rho\) at every carrier label. On scalar clock
polynomials, both weighted quadratures consequently see
only the clean sites, whether or not individual carrier
row coefficients vanish. No rooted identity is here
replaced by a fitted scalar quadrature.

The four polynomials \(J,ZJ,R,ZR\) are a basis through
degree three. Indeed if \(aJ+bZJ+cR+dZR=0\), the constant
and cubic coefficients give \(c=b=0\), the linear
coefficient gives \(d=a\), and the quadratic one gives
\((1-\kappa)a=0\).
Adding \(Z^2J\) supplies the extra leading degree
through degree four. This proof includes the possible
case \(\kappa=0\).

If there were at most four distinct clean clocks early,
choose an anchored monic polynomial \(H=XH_3\) of degree
four vanishing on them, padding if necessary. The clean
origin at \(X=0\) supplies the anchored factor.
Exactness through grade six gives
\[
 \int_0^1 Z(Z-1) H(X)\,J(Z) Z^j\,dX
 =
 \int_0^1 Z(Z-1) H(X)\,R(Z) Z^j\,dX=0,\qquad j=0,1,2 .
\]
The span just proved makes these precisely the vanishing
reads against every polynomial through degree four for
\((Z-1)H_3\) in the weight-\(X(1-X)\) Gram, up to the
nonzero scalar \(1/y\). This Gram is nonsingular with
\(11!\) paid, so \((Z-1)H_3=0\), impossible in the
polynomial ring over a field. Thus at least five distinct
clean clocks occur among the literal first eleven.

## Exact clean family at five carrier clocks

If \(N=5\), the four distinct tail carrier labels must
each have a matching early carrier by pooled ordinary
mass zero. The additional carrier label is absent from
the tail and therefore needs at least two early carriers.
There are at least six early carrier rows. The preceding
minimum of five distinct early clean rows forces exactly
six early carriers and five distinct early clean rows.
Exactly one early carrier type is doubled, the one that
does not occur in the tail.

The ordinary weights pool to zero on every carrier clock,
by the nine paid scalar defect moments.
Thus ordinary scalar order eleven is on the distinct
clean clocks alone. A set of at most six distinct clean
clocks including 0 and 1 cannot do this:
take a degree-six hull \(X(1-X)U_4(X)\) vanishing at every
such clock, padding with arbitrary factors if necessary.
The paid ordinary moments give
\(\int_0^1 X(1-X)U_4(X)V(X)dX=0\) for all \(\deg V\le4\).
Again the paid Gram gives \(U_4=0\), contradiction.
The five early clocks and two tails must therefore all
be distinct. This is an algebraic quadrature minimum,
not a positivity assertion.

Now use the early monic clean hull \(H_5\) of degree five.
Both exact weighted quadratures pay its product with
a polynomial of degree at most one.
Their reduced multiplier span \(J,ZJ,R,ZR\) through
degree three yields
\[
               \int_0^1 (1-X)(X-\theta)H_5(X)\,V(X)dX=0
                                     \quad(\deg V\le3),
\]
up to nonzero constants from the definition of \(Z\).
Since \((X-\theta)H_5\) is anchored and has degree six,
this is exactly the earlier fixed four-moment kernel
\(\langle XR_4,XR_5\rangle\).
The whole clean hull is \(H_7=(X-1)(X-\theta)H_5\).
Once its distinct nodes are fixed, their ordinary
weights are uniquely determined by degree-through-six
quadrature. The remaining degree-through-ten scalar
tests follow from the indicated Jacobi orthogonality
of the hull. This only calibrates the remaining scalar
schedule; the stage-order and rooted constraints must
still be proved to hold or fail.

ERK11CleanJacobiGate.lean checks the denominator-free
four-column span gate and explicit coprimality identity.
The actual carrier pooling, paid Gram, and chronology
are mathematical here, and no ordinary bound changes.
