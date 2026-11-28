# Four distinct calibrations: two shared free crossing pairs are impossible

**Scope.** Continue the characteristic-zero
[nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md)
with four distinct calibrations \(a,h,d,e\). Assume both fronts choose
the same two free active labels \(t,u\) as their extras and both
labels are ordinary pairs (rather than one the triple). This
excludes this particular two-cross chart over any characteristic-zero
field. The same-extras case with one free label the triple is
not covered. Neither the whole four-distinct atlas nor an ordinary
ERK11 stage bound follows.

## 1. Two independent symmetric clock equations

Write \(h=a/2,\ d=1-b,\ e=1-b/2\), and use the eight-clock
Hankel data \(P_4=(X-a)(X-h)(X-d)(X-e)\) and
\(m_j=\int_0^1X(1-X)P_4(X)X^j\,dX\).
Let \(D=\det(m_{i+j})_{i,j=0}^2\). The actual layout has
\(D=0\) and the proved-live pivot
\[
 \Delta=m_0m_2-m_1^2\ne0.
\]
With \(A=m_1m_2-m_0m_3\) and \(B=m_1m_3-m_2^2\), the free
clock roots \(t,u\) solve \(X^2+(A/\Delta)X+B/\Delta=0\).
They are distinct, no calibration, and nonendpoints.
In the scaled coordinate \(Y=\Delta X\) their monic
quadratic is \(Y^2+AY+\Delta B\).

For the paid first contact, both front extra sets are
\(\{t,u\}\). The four \(\ell,r\) factors, multiplied by
\(\Delta\), are
\[
 \begin{split}
 L_0&=a^2\Delta+aA+B,& L_1&=-B,\\
 R_0&=d^2\Delta+dA+B,& R_1&=-\Delta-A-B .
 \end{split}
\]
Thus the inverse mixed-Gram contact equation requires
\[
 C=L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+
                        U_{4,4}(a,b)L_1R_1=0 .
\]
This is \(\Delta^2\Psi=0\), so no further denominator
was introduced.

The two free labels are both literal crossing pairs.
The [cross-pair response equality](ERK11-MIXED-OVERLAP-TWO-CROSS-EXIT.md)
therefore gives \(\Xi(t)=\Xi(u)\), with
\[
 \Xi(y)=\mathcal J(y)y(1-y)(a-y)(y-d),\qquad
 \mathcal J(y)=\int_0^1 X(X-1)
        \frac{H_6(X)-H_6(y)}{X-y}\,dX.
\]
Construct its numerator using
\(\widehat H=P_4(\Delta X^2+AX+B)=\Delta H_6\).
The corresponding \(\widehat\Xi(y)\) is \(\Delta\Xi(y)\)
and is a polynomial of degree at most nine in \(y\).
Take the linear coefficient \(E\) of the remainder of
\(\Delta^9\widehat\Xi(Y/\Delta)\) modulo the monic
quadratic \(Y^2+AY+\Delta B\). This is a rational polynomial
in \(a,b\): if the current remainder is \(v+wY\), a
Horner step with coefficient \(c\) gives
\((c-\Delta B w)+(v-Aw)Y\). The actual two scaled roots
are distinct and have equal evaluations, so \(E=0\).

The polynomials \(D,\Delta,C,E\) are symmetric in \(a,b\).
The symmetry can be checked coefficientwise, as in the
standalone replay, by expansion in \(S=a+b,\ T=ab\).
Conceptually flipping \(a,b\) reflects \(X\) to \(1-X\):
the degree-six hull is monic/reflected even, \(\Delta\)
is invariant under the two-by-two moment basis change,
the Gram contact pairs the two fronts in reverse order,
and the sign change in \(\Xi\) cancels the sign change
of the divided linear remainder. This does not require
ordinary order eleven of the reflected tableau.

## 2. Exact resultants, including the exceptional fibers

Clear constant rational denominators and integer contents
from the symmetric polynomials. In \(S,T\), the total degrees
of \(D,\Delta,C,E\) are \(6,4,12,39\). Actual \(S,T\) solve
\(D=C=E=0\) with \(\Delta\ne0\). The exact resultants
\(\operatorname{Res}_T(D,C)\) and
\(\operatorname{Res}_T(D,E)\) have degrees 72 and 234
in \(S\). Any common finite \(T\) forces both resultants to
vanish, even at a drop of specialized polynomial degree.

Their gcd in \(\mathbb Q[S]\) has degree 24 and, up to
nonzero rational scale, equals \(\operatorname{Res}_T(D,\Delta)\).
It factors as \(g_4g_{10}^2\), with \(\deg g_j=j\).
This **does not by itself show** the actual \(T\) has
\(\Delta=0\), since several \(T\)'s might lie over the same
\(S\). The receipt checks both fibers directly.

For \(g=g_4\) and \(g=g_{10}\), reduce all coefficient
polynomials modulo \(g(S)\). Exact Euclidean arithmetic in
\((\mathbb Q[S]/g)[T]\) gives the common gcd of \(D,C,E\)
monic and of degree one. For each \(g\) that gcd divides
\(\Delta^2\) (checked by its zero remainder). The replay
inverts only Euclidean pivots that are units in the exact
quotient. Therefore evaluation at any actual \(S\) root of
one of these factors and then actual common \(T\) gives
\(\Delta^2=0\), hence \(\Delta=0\) in the tableau's field.
This contradicts the independently proved-live Hankel
pivot. No exceptional resultant fiber was discarded.

The [standalone Python replay](erk11-four-distinct-same-free-pair-exit/replay_four_same.py) constructs the
polynomials and checks both exact projection/fiber steps
with SymPy. There is no numerical scouting or Lean
kernel replay claimed for this separate calculation.
