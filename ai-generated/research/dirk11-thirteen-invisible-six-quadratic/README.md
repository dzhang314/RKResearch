# A finite quadratic-carrier macro and two exclusions in invisible DIRK11/13

**Result.** In the normalized invisible six-ghost DIRK11/13 branch
with \(\alpha=0\) and degree-two ghost polynomial \(U\), the five
ordinary non-endpoint clocks and the normalized monic \(U\) belong
to a finite algebraic set. There is no solution on either of two
specific subcharts:

* the simultaneous leading-drop case \(q=-3/10\), for every
  ordinary Jacobi pencil parameter;
* the fixed Lobatto pencil \(\lambda=0\), for every \(q\).

The general finite macro has not been exhausted. This is not a new
unrestricted stage bound: the real DIRK11 interval remains **13–14**.

The input is the actual signed skeleton of the
[forward-prefix packet](../dirk11-thirteen-invisible-six-prefix/README.md):
literal thirteen-stage lower triangle with true order 11, \(C(2)\),
genuine \(D(1),D(2)\), order-six surplus, \(r=0,d=z_{\mathrm{count}}=6\),
and no ghost before the third non-endpoint clean in reverse. With
\(\alpha=0\) the reverse order is the terminal, four consecutive
ordinary non-endpoint stages, \(\beta\) ghosts, the fifth ordinary
stage, \(\gamma\) ghosts, and the origin. Thus the first two
nonorigin clean stages in **forward** order, called \(b,a\), have
all ghosts before \(a\). For a quadratic \(U\), the earlier prefix
bound gives \(\gamma\le4\), so \(\beta\ge2\). The new mathematical
conclusions apply over a characteristic-zero field once that
signed skeleton and its paid ranks are supplied.

## 1. Exact supported grade-six identity

Use a common nonzero scalar to normalize the polynomial on the
ghosts to monic \(U=X^2+sX+t\), scaling the true cubic column \(g\)
and its clean-supported mask \(\phi=U(c)-g\) by the same amount.
This does not change any tableau coefficient or graded span.
The prefix multiplicity obstruction gives \(t\ne0\).
Write \(H=XJ_4\), so the genuine terminal profile is
\(H_T=30b_T H\). The reciprocal clean relation \(G\phi=\tau H_{\rm bary}\)
has \(\tau\ne0\): otherwise the quadratic \(U\) vanishes at the three
distinct live clean cubic samples \(v,u,w\). Thus both \(U(c)\)
and the true reverse \(G\) are live at all nonterminal clean
sites. In particular \(U(b)\ne0\).

Let \(V_b=C(C-b)\phi\), with \(b\) the forward clock.
The causal cut gives \(AV_b=0\) at all ghosts and at \(b\), since
their possible clean donors have clock 0 or \(b\), and \(V_b\)
vanishes there. The actual masked primitive produces
\(AV_b-F_b(c)\in F_6\), \(F_b=I[X(X-b)U]\). The rank-six
terminal head equation is therefore
\[
 F_b-rH+U Q_3=0,
\]
at all six distinct ghosts, with \(\deg Q_3\le3\). It is a degree
at most five identity and holds as polynomials. At the first
nonorigin clean it also gives \(F_b(b)=rH(b)\). The earlier
two-anchor obstruction proves \(r\ne0\).
Since \(F_b(0)=H(0)=0\), \(U(0)\ne0\), and \(U(b)\ne0\), the
quotient has both anchor factors:
\[
 F_b-rH=X(X-b)(\ell X+\mu)U.                 \tag{1}
\]
Consequently as actual stage columns
\[
 AV_b=(\ell C+\mu)V_b+\frac{r}{30b_T}e_T.
\]
In particular the true diagonal at the second forward clean
\(a\) is \(\ell a+\mu\): its only possible nonzero \(V_b\)
donor is that physical stage itself. No ghost weight is inverted.

Put \(q=42r\), so \(q\ne0\).
The \(X^5,X,X^2\) coefficients of (1) give, in turn,
\[
 \ell=\tfrac15-q,\quad \mu=\frac{q}{42bt},\quad
 s=\frac{42bt^2(3/10+q)}{q}-14t+\frac{t}{b}.
\]
Substitute in \(X^4,X^3\) and clear the paid denominators \(b,t,q\)
and rational integers. This gives two degree-at-most-three
polynomials \(P_4,P_3\) in \(t\). The source computes them directly
from (1). The resultant is a nonzero rational scalar times
\[
   b^4 q^5(10q+3)\Gamma(b,q),\qquad
   \deg_b\Gamma=12,\quad \deg_q\Gamma=6,\quad
   \Gamma(b,0)=111132\,b^{12}.
\]
Also \(P_4(t=0)=-50q^2\). Thus at actual \(b,q\) neither the
necessary carrier polynomial \(\Gamma(b,q)\) in \(q\) nor, after
fixing it, the cubic in \(t\) is identically zero. The possible
leading changes are retained, not divided away in the identities.

## 2. Actual read tests on the four consecutive clean rows

Let \(v,u,w,\widetilde a=1-a\) denote the old reverse clean prefix
after the terminal. On any of these define \(h(y)=yJ_4(y)\) and
\(k_y=G_y/b_y\). The reciprocal head and the first genuine \(G_v\)
fix
\[
 k_y=\frac{v^3\, U(1-v)\,h(y)}{6\,h(v)\,U(1-y)}.
\]
The affine profiles \(G_4/G\) and \(NG/G\) are calibrated from
the actual \(v,u\) samples. At \(u\) use moments 1,2; at \(w\)
use moments 1,2,3 to solve the actual inclusive taps. The scalar
targets are \(y^2/2,\ y^3/3+k_y,\ y^4/4+L_1(y)k_y\), where
\(G_4=L_1(Y)G\). At \(v,u,w\) fit the genuine quadratic profiles
of \(G_5/G\) and \(N(YG)/G\) from their fourth scalar and marked
reads. At \(\widetilde a\), the first four moments solve the four
inclusive regular taps uniquely. There is no earlier ghost and all
ordinary denominators are nonzero. The replay checks four actual
necessary residuals: the diagonal \(\ell a+\mu\), the affine
\(NG\) equation at \(w,\widetilde a\), and the \(N(YG)\) equation at
\(\widetilde a\). These need not be algebraically independent.

There is a fifth, forward grade-seven check. The actual column
\(\psi=C(C-a)(C-b)\phi\) kills every possible clean input to \(a,b\)
and all ghosts, so \(A\psi\) is zero there. The exact
\(F_7=g\mathcal P_4+(e_T-H_T)\mathcal P_1\) follows by the same
dimension argument in the [constant-\(U\) closure](../dirk11-thirteen-invisible-six-constant-exclusion/README.md),
which did not use the constancy for that rank assertion.
Let \(F_{ab}=I[X(X-a)(X-b)U]\). The exact affine multiplier \(L\)
of the scaled terminal head is fixed at \(a,b\) by
\(L(a)=F_{ab}(a)/H(a)\), \(L(b)=F_{ab}(b)/H(b)\).
The nonterminal clean hull \(S_6\) has ghost counterpart
\(R_6=S_6-U Q_3^*\) by the actual \(E_6\) shape, since \(UQ_3^*\)
has degree at most five. At all six ghosts,
\(F_{ab}+U Q_4-H L=0\); of degree at most six, it is a scalar
multiple of \(R_6\). Therefore the two coefficient vectors
of \(F_{ab}-H L\) and \(S_6\) modulo the monic \(U\) are proportional.
The replay checks their determinant; it never assumes that \(U\)
has simple roots or divides by a remainder coefficient.

## 3. General finite macro and the exceptional \(q\)

First suppose \(q=-3/10\). Both cubic leaders drop, so independently
specialize \(P_4,P_3\) before taking the subresultants in \(t\).
The new resultant is a primitive degree-nine polynomial in \(b\).
Its evaluation at \(b=1/14\) is nonzero, guarding a further degree
drop of the first resulting quadratic (the second leading term
is a nonzero multiple of \(b^3\)). The linear subresultant
recovers \(t\) with a tested unit leader. The normalized modulo-101
tower uses this rank-nine \(b\), \(\lambda=-J_5(b)/J_4(b)\),
then successive monic degree-four, degree-three and degree-two
choices for the remaining ordered ordinary clocks; the last is
obtained by the sum. Thus the ranks are \(9,36,108,216\).
A fixed linear combination of the four actual reverse residuals
in §2 is a unit in the complete quotient. The 89 verified inverse
products include the final unit and all recursive denominator
tests. This excludes the entire exceptional branch without
reducing an unknown tableau.

In the regular case \(q\ne-3/10\), work first over \(\mathbb Q(b)\).
Normalize \(\Gamma(b,q)\) to be monic in \(q\); the linear
subresultant generically recovers \(t\). Then the normalized
ordinary quintic deflated by \(b\) contributes the degree-four,
degree-three and degree-two monic choice tower just described.
The regular macro algebra has rank \(6\cdot24=144\) over
\(\mathbb Q(b)\). Every prospective division is guarded by the
nonzero constant coefficient or multiplication determinant of
its divisor. That these guards really are nonzero rational
functions is certified by one split specialization: at
\(b=2\bmod43\), the ordinary Jacobi parameter is 0 and the
five distinct roots are \(2,9,22,35,42\). All required divisions
are units in each residue component. The five necessary residuals
of §2 generate the unit ideal for each of the 24 remaining
ordinary orders (their joint univariate gcd with the normalized
\(\Gamma\) is one). Therefore the map given by multiplication by
these five elements onto the rank-144 algebra has a nonzero
maximal minor over \(\mathbb Q(b)\). Equivalently one can first
localize the polynomial coefficient ring at the guard determinants
and use this split residue to certify that minor is not identically
zero.

A characteristic-zero candidate must have \(b\) in the finite
zero/pole set of this nonzero minor and the guard polynomials.
This is a finite algebraic reduction, not an enumeration of that
exceptional set. Even at a bad generic guard, \(\Gamma(b,0)\ne0\)
and \(P_4(0)\ne0\) from §1 leave only finitely many \(q,t\).
The formula for \(s\) is guarded at every actual candidate, and
the ordinary quintic leaves finitely many clock choices. Thus
the macro conclusion includes singular subresultant leaders,
not just the generic quotient. It does not claim a finite list
for all ghost taps, clock labels, or unnormalized amplitudes.

## 4. The complete fixed Lobatto pencil, including midpoint contacts

For \(\lambda=0\), modulo 181 the ordinary five roots split and
are distinct. For every nonmidpoint \(b\), the residue checks
show the five residuals generate the unit ideal for all 24
orders on the rank-six coefficient algebra in \(q\). This
excludes the exact characteristic-zero nonmidpoint branch
by good reduction in the full monic ordinary-clock tower.
At the midpoint \(b=1/2\), \(\Gamma(1/2,q)\) factors as
\((20q-9)\) times a degree-five factor, up to a nonzero scalar.
The exact source checks the factorization and that the two
factors are coprime modulo 181. In all 24 midpoint orders
the exact residue gcd with the five residuals is precisely
the linear factor, so the degree-five factor is excluded
by the same unit-ideal argument. Division guards are tested
in the whole rank-six algebra before these component checks.

For clarity, such an exact residue unit-ideal check on any
finite-free tower lifts as follows: lift residue Bézout
coefficients arbitrarily through the finite-free basis. The
same linear combination of the exact residuals has invertible
multiplication operator modulo the prime. Its determinant is
a unit of the localization, so it is an exact unit by the
adjugate. It cannot map to zero under an evaluation at a
hypothetical tableau. This checks clock/profile algebras only,
not integrality of unknown stage coefficients.

The remaining case is exactly \(b=1/2,\ q=9/20\), with unit
linear subresultant leader over the rationals, and
\(t=1/7,\ s=-1\). Thus \(U=X^2-X+1/7\). At each of the four
noncentral clean clocks the quartic factor of \(J_5\) is zero,
and \(J_4=(28/11)U\) by the exact Jacobi polynomial identity.
Symmetry gives \(U(1-y)=U(y)\), so at the four consecutive
reverse clean clocks \(v,u,w,\widetilde a\) one has
\(k_y=\kappa y\). The genuine affine and quadratic marks
are therefore
\[
 NG=(Y/2)G,\qquad N(YG)=(Y^2/3+\kappa)G .
\]
Indeed on these four clean rows the normalized marked reads
are \(\kappa\) times weighted powers 1 and 2, respectively,
and their true polynomial degrees give equality on the full
actual row. Use the true grade-six shape
\(N(Y^2G)=R_3(Y)G+\theta H_{\rm bary}\).
Its effective quotient on clean sites is a cubic, since
\(H_{\rm bary}/G=U(1-y)/\tau\) there. On the four samples
the normalized reads are \(\kappa\) times power 3, so this
effective cubic is \(y^3/4+\kappa L_1(y)\).

There are at least two physical ghosts before the fifth
ordinary in reverse. At the first such ghost \(x\), the
paid \(NG\) fixes the literal diagonal \(d_x=x/2\) using the
zero first weighted moment. Its \(N(YG)\) read is
\(\kappa+x d_x\), because its weighted second moment is one
after division by the live \(G_x\). Thus \(x^2/6=0\), so
**the first ghost has \(x=0\)**. This is allowed: the census
requires distinct dirty clocks, not that a ghost clock differ
from a clean clock. The first ghost therefore may share the
reflected clock of the actual terminal; it is not identified
with the terminal. No formula above divides by \(x\).
At this ghost the actual third marked quotient is
\(\kappa L_1(0)\), since its own \(Y^2\) is zero. It equals
the already fitted effective cubic there, so
\(\theta U(1)/\tau=0\); named factors \(U(1)=1/7,\tau\ne0\)
make \(\theta=0\).

At the **second physical ghost**, its clock \(y\ne0\) by
distinctness from the first dirty clock. The first ghost's
\(YG\) and \(Y^2G\) coordinates are zero, regardless of its
actual tap into the second. The quadratic mark then gives
\(y d_y=y^2/3\), whereas the now-global cubic mark gives
\(y^2 d_y=y^3/4\). They are incompatible at nonzero \(y\).
Thus both the noncentral arithmetic branch and the surviving
midpoint branch are impossible.

## Reproduction and Lean scope

Run \(\texttt{python3 replay.py}\) with SymPy. The residue
arithmetic reuses the exact finite-free classes of the previous
constant packet and exposes separate exceptional, generic and
Lobatto modes. Lean independently verifies the guarded coefficient
extraction, quartic ratio, the first and second actual ghost
scalar gates, and calibration of the clean head to zero.
The full support/chronology and good-reduction arguments are
exact source proofs, not an end-to-end Lean endpoint theorem.
