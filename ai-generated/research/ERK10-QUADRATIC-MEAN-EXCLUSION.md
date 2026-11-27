# The all-live ERK10 forced two-pair chart has no quadratic mean

Over a characteristic-zero field, continue the
[all-live eight-clock ten-active-row chart](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md).
Its two repeat groups are literal rows 4/5 at \(p=2c_3\) and
10/11 at \(q=2c_{12}-1\), with unequal nonzero amplitudes in
each. The [earlier finite exits](ERK10-FORCED-TWO-PAIR-FINITE-EXITS.md)
give \(p,q\notin\{0,1\}\) and rule out a constant or linear
\(br\)-weighted mean. **Here the degree-two mean is excluded
as well.** A cubic mean in this chart remains open.

All scalar elimination below is exact, irrespective of field
ordering or of the sign of the weights. The proof consists of
two rational polynomial norms with a verified common factor,
a valuation-at-infinity check (not a height cutoff), and a
separate finite check on every remaining factor. The
[complete replay](replay_quadratic_mean.py) uses Python's
standard library and the supplied GMP rational norm generator.

## 1. Actual conditions and the one-parameter family

Fix count \(q=8\) of distinct active labels; within this note
\(q\) in a formula denotes the *clock* of the late pair.
Use \(t=p/2,\ t_R=(q+1)/2,\ x=c_6,\ y=c_7,\ z=c_8,\ w=c_9\).
On the six singleton labels, \(r_i=R(c_i)\). At the two pairs
\(R\) is the \(\nu\)-weighted mean, so no fictitious equality
of individual amplitudes is used. The genuine grade-three
mask \(T=R(c)-r-R(\theta)s\) has scalar model \(R\) and is
numerically supported only on the two repeat groups and the
physical endpoints. The three paid anchored moments give
\[
 \int_0^1 X(1-X)(X-p)(X-q)R(X)X^j\,dX=0,\qquad 0\le j\le2 .
\]
Normalize the degree-two \(R\) to monic, rescaling \(r,\kappa\)
by the same factor. Put
\[
 S_\delta=(X-p)(X-q)R
     =\frac{L_4}{42}+\delta\,\frac{J_3}{14},\quad
 L_4=42X^4-84X^3+56X^2-14X+1,\quad
 J_3=14X^3-21X^2+9X-1 .
\]
This follows because the three independent anchored moment
functionals on degree at most four have kernel spanned by
the indicated two polynomials, and the quartic is monic.
Reflection sends \(\delta\mapsto-\delta\).

We recall the actual tests (all proved in the
[paired seam packet](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md)):

1. The quadratic for \(x\) is
\[
  Q_L(X)=\frac{ t^3 R(X)+R(t)X^2(X-p)}{X-t},
\]
and the reflected condition is \(Q_R(w)=0\), where
\(Q_R(W)\) is obtained by applying the same formula to
\(R(1-X),1-q,(1-q)/2\) and evaluating at \(X=1-W\).
The cleared numerators divide exactly by the stated
linear factors; no normalization by a quadratic leading
coefficient is required to state these equations.
2. \(P_L(y)\) and \(P_R(z)\) are the scalar polynomial
models
\[
 \begin{split}
 P_L(y)(X)&=(X-p)[R(0)(X-t)(X-x)(X-y)
                         +txy\,R(X)],\\
 P_R(z)(X)&=(X-q)[R(1)(X-t_R)(X-w)(X-z)
                         -(1-t_R)(1-w)(1-z)R(X)] .
 \end{split}
\]
Their actual grade-four lifts vanish on the appropriate
physical seven-row halves. The ordinary one-step seam is
\(\int JP_L(y)\,P_R(z)=0\), paid at total grade nine.
3. Write \(H_p=J^2[X(X-t)(X-p)]\), giving
\(H_p=X^5/20-pX^4/8+p^2X^3/12\).
Let \(\bar H_q\) be the reflected right version. The two
genuine two-step seams give
\[
      A_L y+B_L:=\int \bar H_q\,P_L(y)=0,\qquad
      A_R z+B_R:=\int H_p\,P_R(z)=0 .
\]
Both equations are literal chronological products, paid
at total grade nine. Their coefficients are defined by
evaluation at \(0,1\): constant is value at 0, slope is
value at 1 minus value at 0. No nonzero slope premise
is introduced here.
4. The paid singleton residue is
\[
 J_R(X)D_s(X)+\kappa h(X)=0\pmod R,\qquad
 D_s=(X-t)(X-x)(X-y)(X-z)(X-w)(X-t_R),\quad h=X(X-1),
\]
where
\[
  g=X(X-1)(X-p)(X-q),\qquad
  J_R(U)=\int g(X)\frac{R(X)-R(U)}{X-U}\,dX .
\]
This exact algebraic residue cancels the repeat-root
factors only at singleton labels. It holds even if
\(R(p)\) or \(R(q)\) is zero or \(R\) has a multiple
root. No division by these values is used below.

## 2. Cleared polynomial norms with no lost poles

Use the two cleared models
\[
  \widetilde P_L=A_L P_L(0)-B_L(P_L(1)-P_L(0)),\qquad
  \widetilde P_R=A_R P_R(0)-B_R(P_R(1)-P_R(0)).
\]
At the actual \(y,z\), they are \(A_L P_L(y)\) and
\(A_R P_R(z)\). In particular the ordinary seam
gives
\[
                    \mathcal H=\int J\widetilde P_L\,
                                     \widetilde P_R=0 .
\]
This identity remains necessary if \(A_L\) or \(A_R\)
vanishes. Similarly reduce
\[
  J_R D_4(A_L X+B_L)(A_R X+B_R),\qquad
  D_4=(X-t)(X-x)(X-w)(X-t_R)
\]
modulo monic \(R\), and take its \(2\times2\) coefficient
determinant against the residue of \(h\).
Call this scalar \(\mathcal G\).
The two parenthetical factors equal \(A_L(X-y)\) and
\(A_R(X-z)\) on an actual solution, and the singleton
congruence implies \(\mathcal G=0\), again without
division. Both \(\mathcal H,\mathcal G\) are polynomial
in the remaining data, of degree at most two in each
of \(x,w\). Here \(P_L\) and the left affine coefficients
are separately affine in \(x\), and those on the right
are separately affine in \(w\).

Form the following polynomials over the rational parameter
ring \(\mathbb Q[\delta]\).

- Adjoin \(p\) by the monic relation \(S_\delta(p)=0\).
  Adjoin \(q\) by the monic cubic \(S_\delta(X)/(X-p)\).
  The true monic \(R\) is the second synthetic quotient.
  These universal algebras include all ordered choices
  and do not assume squarefree fibers.
- For \(U=\mathcal H\) and \(U=\mathcal G\) separately,
  take the padded resultant \(\operatorname{Res}_x(Q_L,U)\)
  of degree bounds \((2,2)\). Its degree in \(w\) is
  at most four. Then take the padded resultant
  \(\operatorname{Res}_w(Q_R,\operatorname{Res}_x(Q_L,U))\).
  These determinants vanish on every actual root
  selection of their operands, even in a specialization
  with smaller degree or with zero leading coefficient.
- Take the determinant of multiplication by the resulting
  element, first in the rank-three monic \(q\) algebra,
  then in the rank-four monic \(p\) algebra. Denote the
  scalar polynomials \(N_{\mathcal H}(\delta)\) and
  \(N_{\mathcal G}(\delta)\). An actual root assignment
  maps the multiplication element to zero; hence its
  norm (determinant) is zero. This implication does not
  require field or separable algebras.

Thus any actual \(\delta\) is a common zero of the two
rational polynomial norms. The supplied program computes
them by the following exact operations: padded quadratic
resultants via the root power-sum recurrence (a polynomial
identity even at a zero leading coefficient), exact
interpolation at three values in \(x\) for each of five
values in \(w\) using the stated degree bounds, and literal
rank-three/rank-four determinants of multiplication.
The interpolation is of known bounded-degree polynomials,
not a finite trial of clock heights or parameter values.

The exact rational result is:
\[
 \begin{gathered}
 \deg N_{\mathcal H}=\deg N_{\mathcal G}=336,\qquad
 N_{\mathcal H}=E\,Q_{\mathcal H},\quad N_{\mathcal G}=E\,Q_{\mathcal G},\\
 E=(3\delta-1)^{36}(3\delta+1)^{36}F(\delta)^8F(-\delta)^8,\\
 F(D)=32400D^6+31860D^5-864D^4+1767D^3
                          +109D^2+283D-59 .
 \end{gathered}
\]
The replay performs **exact** rational division: both
remainders are zero. Both quotients have degree 168 and
coefficients integral at 37; their reductions have gcd
exactly 1 by the ordinary finite-field Euclidean algorithm.
Thus, once \(\delta\) is shown integral at 37, it must be an
**exact** zero of \(E\): if not, both exact quotients vanish
and so would their coprime reductions. We never exclude a
parameter just because its residue lies at a pole.

## 3. No parameter root is lost at infinity

The nonzero exact norm polynomial already makes any actual
\(\delta\) algebraic. Fix a place over 37 of a finite
splitting field of \(S_\delta\). Suppose the normalized
valuation of \(\delta\) is negative. The monic quartic then
has exactly one nonintegral root \(\xi\), with
\(\xi/\delta\equiv-1\), and three integral roots reducing to
the three distinct roots of \(J_3\).

Here is an elementary proof of this root description.
Upon scaling by \(\delta\), the monic polynomial
\(\delta^{-4} S_\delta(\delta Y)\) has integral coefficients
and reduction \(Y^3(Y+1)\). Thus exactly one root has
\(\xi/\delta\equiv-1\). A further root \(u\) cannot have
negative valuation greater than \(v(\delta)\): within
\(S_\delta(u)\), the term \(\delta u^3\) would be the unique
term of smallest valuation. The other three roots are
therefore integral. Dividing the factorization by
\(\delta\) makes \((X-\xi)/\delta\) reduce to 1, so the
other monic triple reduces to \(J_3/14\), which splits
simply at \(12,19,26\) mod 37.

There are only the following cases.

* **The nonintegral root belongs to \(R\).** Scale the
  entire \(R\) by \((-\xi)^{-1}\). The result reduces to
  a monic linear polynomial \(X-a\), with \(p,q,a\)
  the three \(J_3\) roots. The local contact equations,
  two-step seams and ordinary seam are homogeneous in \(R\),
  so this normalization is legitimate. The exact finite
  linear-mean replay at prime 37 applies: the local
  quadratic leading residues and both affine seam pivots
  are units on all branches, and the resulting ordinary
  seam is a unit. Thus this case is impossible.

* **The nonintegral root is \(p\).** If instead it is
  \(q\), take the physical reflection. Now \(q\) reduces
  to one of the \(J_3\) roots, and monic \(R=X^2+aX+b\)
  reduces to the product of the other two. The cleared
  left quadratic \(Q_L\), divided by \(t^2\), has
  reduction \(X^2-aX-b\): its exact coefficients before
  scaling are
  \[
      t^2+at+b,\quad -(at^2+bt),\quad -bt^2 .
  \]
  These follow by synthetic division of the numerator in
  §1. The leading coefficient is therefore a unit in
  this normalization, making \(x\) integral. The reflected
  quadratic for \(w\) has finite coefficients and a unit
  leading coefficient by the finite check. The left
  ordinary model and the left double primitive, scaled
  by \(p^2\), have limiting **coefficient polynomials**
  \[
   \frac{P_L(y)}{p^2}\ \mapsto\
       \tfrac12\{R(0)(X-x)(X-y)-xyR(X)\},
    \qquad
   \frac{H_p}{p^2}\ \mapsto\ X^3/12 .
  \]
  These are reductions of coefficients in the affine
  variables \(y,z\); no integrality of \(y,z\) is assumed
  to write them. On every \(q\)-root assignment and both
  local quadratic choices, the resulting two affine seam
  slopes are units. Cramer's one-dimensional rule
  therefore makes \(y,z\) integral and computes their
  reductions. The reduced scaled ordinary seam is a
  unit in **all** these choices (exact finite replay).
  This also contradicts its zero value.

At each step a place extends to the next monic root
algebra, localizing first at its asserted residue units.
This uses only algebraic parameters \(p,q,x,w\);
the affine rules themselves make \(y,z\) algebraic and
integral in the branches where they are reduced.
The parameter is therefore integral at 37. Applying §2
forces \(\delta\) to be an exact root of \(E\).

## 4. All finite exceptional factors

### Endpoint-root parameters \(3\delta=\pm1\)

Since both repeat clocks are nonendpoint, \(3\delta=-1\)
forces \(R(1)=0\), by \(S_\delta(1)=1/42+\delta/14\).
The singleton hull \(D_s(1)\ne0\), as an active singleton
cannot have a root of its amplitude polynomial \(R\).
The genuine residue in §1 at \(X=1\) gives \(J_R(1)=0\).
But it equals
\[
     J_R(1)=\int_0^1 X S_\delta(X)\,dX
             =1/1260+\delta/280=-1/2520,
\]
a contradiction. Reflection handles \(3\delta=1\).

### Contact-lead factors \(F(\delta)F(-\delta)=0\)

Reflection reduces to \(F(\delta)=0\).
The exact Sylvester identity
\[
 \operatorname{Res}_X(S_\delta(X),S_\delta(X/2))
               = (3\delta-1)F(\delta)/611784327168
\]
is checked by the Lean companion (integer rescaling
and nine evaluations for a degree-at-most-eight
determinant). Thus there is a distinguished exact root
\(p_0\) such that both \(p_0\) and \(p_0/2\) are roots
of \(S_\delta\). It cannot be zero, since \(3\delta=1\)
was excluded. The actual \(p\) **cannot equal \(p_0\)**:
its half \(t=p/2\) is a distinct singleton active clock,
so \(t\) differs from \(p,q\) and \(R(t)\ne0\), inconsistent
with \(S_\delta(t)=0\).

Modulo 37, \(F\) factors into the two distinct irreducible
cubics with coefficient arrays
\([35,15,17,1]\) and \([33,8,29,1]\), low degree first,
up to the nonzero leading scale. The exact finite replay
checks all of the following within each factor field:

* The quartic \(S_\delta\) is squarefree, and the gcd
  of \(S_\delta(X)\) with \(S_\delta(X/2)\) is exactly
  a linear polynomial, giving the residue of the
  unique distinguished \(p_0\). Since the four roots
  have distinct reductions, the actual \(p\ne p_0\)
  really does reduce to a root of \(S_\delta/(X-p_0)\).
  This is not a discarded high-order congruence case.
* Adjoin \(p\) by this monic cubic and \(q\) by
  \(S_\delta/(X-p)\). Construct monic \(R\) by
  synthetic division. Both local quadratic leads
  and all divisors of the two contacts are units
  in the full product-covering algebra. Thus the
  two local monic quadratics include both choices
  of \(x,w\) and certify their integrality.
* The two affine seam slopes are units in that
  full algebra, so their solutions for \(y,z\)
  are integral and cover every actual branch. The
  ordinary paid seam is a unit in the resulting
  algebra, contradicting its genuine zero value.

Reflection gives the same exact exclusion at \(F(-\delta)\).
This exhausts the entire exceptional factor \(E\).

## Verification scope

[ERK10QuadraticMeanGate.lean](ERK10QuadraticMeanGate.lean)
checks the exact small scalar identities (endpoint moments,
quadratic clearing, distinguished-root resultant, and
modular factors). The supplied [rational norm generator](quadratic_mean_norms.cpp)
and [exact replay](replay_quadratic_mean.py) verify all
polynomial divisions, reduced gcd, and relevant finite
unit towers. The actual rooted-space and prime-lifting
arguments are the mathematical proof above.
This does not touch other coefficient domains indirectly:
the theorem is characteristic-zero and conditional on
the stated stage chart. In particular the cubic mean
and unrestricted 14–15 interval are still open.

The [cubic endpoint follow-up](ERK10-CUBIC-MEAN-ENDPOINT-EXIT.md) shows that the remaining cubic mean cannot vanish at either physical endpoint.
