# The distinct-dormant eight-singleton all-live ERK10 chart is impossible

Work over any characteristic-zero field in the
[all-live constant two-carrier equality ledger](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md).
Assume the outgoing pure column \(r=As\) has eight nonzero physical
occurrences at eight distinct numerical clocks. By the
[fifth-head contact](ERK10-FIFTH-HEAD-CONTACT.md), the two middle
\(r\)-dormant rows are physical 5 and 10. The shared-clock case
was already excluded there. **This note excludes the distinct-clock
case as well**, without ordering the active clocks or the field.
It does not exclude the eight-label ten-active-row case, the
zero-pooled cases, zero output weights, or arbitrary ERK10.

Write \(p=c_5,\ q=c_{10},\ p\ne q\), \(t=p/2=c_3\), and
\(t_R=(q+1)/2=c_{12}\). The repeated active/dormant clocks
are \(c_4=p\) and \(c_{11}=q\), but all eight active clocks
are distinct. Write \(x=c_6,\ y=c_7,\ z=c_8,\ w=c_9\).
The carriers at physical 2 and 13 have the same clock
\(\theta\) and opposite weights. Let \(C=\operatorname{diag}(c)\).

## 1. The scalar cubic, both orientations, and the endpoint exits

The [eight-label barycentric fits](ERK10-THREE-CARRIER-EXCLUSION.md)
give, on the eight active labels,
\[
  \nu_i=b_i r_i=\frac{\kappa}{D'(c_i)},\qquad
  r_i=R(c_i),\quad D(X)=\prod_{\rm active}(X-c_i),\quad
  \deg R\le3,\quad \kappa\ne0 .
\]
One can rescale \(r\) and \(\kappa\) together by a nonzero
constant. Only ratios of local amplitudes are used.
The genuine rooted grade-three mask \(T=R(c)-r-R(\theta)s\)
has polynomial model \(R\) and is supported on the four
clean physical rows 1,5,10,14. In particular \(\int RP\)
is read only on their actual clocks for \(\deg P\le6\).
The mask still costs grade three even if \(R\) has smaller degree.

By the literal Simpson rows in both orientations,
\[
   p\ne0,\quad q\ne1,\qquad
   R(p)+4R(p/2)=0,\qquad
   R(q)+4R((q+1)/2)=0.                           \tag{1}
\]
If both dormant clocks are endpoints the anchored Beta Gram
already contradicts \(R\ne0\). If exactly one equals an endpoint,
let \(\zeta\) be the other. The supported scalar moments give
\(R(X)(X-\zeta)\propto L_4(X)\) for
\(L_4=42X^4-84X^3+56X^2-14X+1\): the alternative smaller degree
is impossible by the nonsingular anchored \(X(1-X)\)-Gram.
Then the Simpson identity in the direction starting at
\(\zeta\) gives the forbidden doubled contact of the
[shared-clock scalar norm](ERK10-SHARED-DORMANT-PURE-PORT.md)
(reflect \(X\) if the contact is the one at \(q\)).
Thus \(p,q\notin\{0,1\}\).

Testing the support polynomial \(X(1-X)(X-p)(X-q)\) gives
\[
 \int_0^1 X(1-X)(X-p)(X-q)R(X)X^k\,dX=0
                            \quad (0\le k\le 2).             \tag{2}
\]
At this point \(R\) is only known nonzero of degree at most
three. The finite base-matrix pivot in §5 will itself force
its degree-three coefficient to be nonzero; no extra paid
scalar moment is introduced to dispose of lower degree.

## 2. Two forced outer middle clocks

Let \(B(X)=X(X-t)(X-p)\), \(p=2t\).
The true input \(B(c)-B(\theta)s\) vanishes through physical
row 5. Its actual unary advance, through grade four, vanishes
through physical row 6; its genuine pure difference from
\(JB(c)\) is in \(Ks+r\mathcal P_{\le1}(c)\).
At active row 4 (clock \(p\)), \(JB(p)=0\), so the affine
coefficient of \(r\) vanishes at \(p\). At active row 3,
\(JB(t)=t^4/4\), fixing that affine coefficient to
\(t^3(X-p)/(4R(t))\), since \(JB(X)=X^2(X-p)^2/4\).
At active row 6, whose clock is different from \(p,t\), this
gives
\[
       R(x)+R(t)x^2(x-p)/t^3=0 .                            \tag{3}
\]
The left polynomial is divisible by \(X-t\). After
division (3) is a quadratic condition on \(x\).
The reflected direction applies to \(x^\vee=1-w\) with
\(R^\vee(X)=R(1-X)\) and \(p^\vee=1-q\).
All guards on those two leading coefficients are paid in
the finite verification below, not added to the hypotheses.

## 3. A linear algebraic reconstruction of the two inner clocks

Put \(g(X)=X(X-1)(X-p)(X-q)\) and
\[
 J_R(U)=\int_0^1 g(X)\frac{R(X)-R(U)}{X-U}\,dX .
\]
The integrand is polynomial in \(X,U\), of degree at most
six in \(X\). Its numerical clean read is zero, and the two
carriers cancel. Using the exact ordinary clock moments and
the active weights \(b_i=\kappa/[R(c_i)D'(c_i)]\), and reducing
in the polynomial quotient ring \(K[U]/(R(U))\), gives
\[
  J_R(U)=\kappa\sum_{\rm active}
       \frac{g(c_i)}{(c_i-U)D'(c_i)}
       =-\frac{\kappa g(U)}{D(U)}\pmod{R(U)}.
\]
Every inverted \(c_i-U\) is a unit in that quotient because
\(R(c_i)\ne0\); their product \(D(U)\) is therefore also a
unit. The last equality is the ordinary Lagrange partial
fraction identity for \(g/D\), with \(\deg g<\deg D\).
**No simple-root assumption on \(R\) is used.**

Let \(D_6(X)=(X-t)(X-p)(X-x)(X-w)(X-q)(X-t_R)\).
Then \(D=D_6(X)(X^2+lX+d)\), where
\(l=-(y+z)\), \(d=yz\). The three coefficient equations
of
\[
 J_R(X)D_6(X)(X^2+lX+d)+\kappa g(X)=0\pmod R             \tag{4}
\]
are linear in \(l,d,\kappa\). The finite verifier below
establishes the required nonzero \(3\times3\) pivot on
every allowed reduction branch. Then \(y\) is one of the
two roots of \(X^2+lX+d\) and \(z=-l-y\); both chronologies
are included.

## 4. The genuine rooted seam test

Let \(H_L(X)=(X-t)(X-x)(X-y)\) and
\(H_R(X)=(X-t_R)(X-w)(X-z)\).
Use the physical formal models
\[
 \begin{split}
 P_L(X)&=(X-p)\,[R(0)H_L(X)-H_L(0)R(X)],\\
 P_R(X)&=(X-q)\,[R(1)H_R(X)-H_R(1)R(X)].
 \end{split}
\]
Their genuine grade-four lifts are
\[
  P_L(c)+(C-p)H_L(0)r-P_L(\theta)s,\qquad
  P_R(c)+(C-q)H_R(1)r-P_R(\theta)s .
\]
The first vanishes on physical rows 1 through 7:
check the origin, the carrier, the repeated clock \(p\),
and the three \(H_L\)-roots. The second vanishes on rows
8 through 14 by the corresponding check. These statements
remain true in case of numeric endpoint-clock collisions at
any active row; the actual stage tags are what is used.
Strictness makes the product of the unary advance of the
first lift and the second lift **literally zero**, costing
\(4+1+4=9\). Therefore
\[
               \int_0^1 (J P_L)(X)P_R(X)\,dX=0 .            \tag{5}
\]
The finite verification below shows this scalar is nonzero
under the preceding necessary conditions.

## 5. Exact scalar elimination and no dropped reduction factors

For the three equations (2), center
\(Z=2X-1\), \(m=p+q-1,\ h=p-q\) so the two centered
contacts are \(m+h,m-h\). Their centered support factor is
\(Q(Z)=Z^2-2mZ+m^2-h^2\). With the four coefficient slots of the centered polynomial
\(R_Z\) (allowing leading zero), the five homogeneous scalar rows are:
- the three coefficient rows of \(\int_{-1}^1(1-Z^2)Q R_Z
  Z^i=0\), \(i=0,1,2\);
- the two contact rows
  \(R_Z(m+h)+4R_Z((m+h-1)/2)=0\) and
  \(R_Z(m-h)+4R_Z((m-h+1)/2)=0\).

Scale the moment rows by 315 and a contact row by 8.
The determinant of the first three moment rows and first
contact row is \(6144(E(h,m^2)+mO(h,m^2))\), with the
explicit integer coefficient lists in
[the Lean companion](ERK10DistinctDormantElimination.lean).
Reflection \(Z\mapsto-Z\) gives the other necessary
determinant test \(E(h,m^2)-mO(h,m^2)=0\).
Two exact identities are used:
\[
 E(h,0)=-J_4(h)S_5(h),\qquad
 \operatorname{Res}_\xi(E(h,\xi),O(h,\xi))
       =-3288952542855168\,G_4(h)G_{14}(h).
\]
Here \(J_4,S_5,G_4,G_{14}\) are explicitly listed companion
polynomials. The determinant identities are checked by
integer interpolation: grid 10 by 10 for the first
determinant (degree at most nine in each variable), ten
points for the first displayed factorization, and 69 for
the Sylvester determinant (bound \(4\cdot9+4\cdot8=68\)).
The resultant is used only in the direction that a common
finite root forces determinant zero, even if a leading
coefficient specializes to zero.

Here is the complete reduction and its guards.

1. If \(m=0\), \(h\) is a root of \(J_4 S_5\). If \(m\ne0\),
   \(h\) is a root of \(G_4 G_{14}\) and \(m^2\) a common
   root of \(E,O\). These starting polynomials in \(h\)
   have **unit leading coefficient** over
   \(\mathbb Z_{(41)}\); \(O\) has constant leading
   \(\xi\)-coefficient 1323, also a unit. Thus \(h,m^2,m\)
   are integral over \(\mathbb Z_{(41)}\) in either case.
   This step never divides by a residue of \(m\);
   an \(m\ne0\) in characteristic zero that reduces to zero
   is still included in the \(m^2\) branch.
2. Choose a prime above 41 in the integral root algebra.
   The factorization modulo 41 of the \(m=0\) polynomial
   has irreducible degrees 2,2,5. The other one has
   factors of degrees 1,1 (the second repeated), 2,13.
   The factors, their multiplicity and their irreducibility
   are checked in the [dependency-free finite algebra replay](replay_distinct_dormant_mod41.py).
   In each \(m\ne0\) factor field, compute the gcd of
   \(E(h,\xi),O(h,\xi)\): constant gcd rejects the factor,
   and otherwise the computed gcd is **linear**, so
   \(\xi\) is fixed. The universal monic quadratic
   \(M^2-\xi\) then covers both signs and any coincidence
   in the residue. We never discard a group by choosing
   a single square root.
3. On those base rings check **all five** literal
   \(4\times4\) minors of the five equations. A unit
   minor rejects a branch. On every branch not thus
   rejected, the replay finds a \(3\times3\) unit minor
   in the first three coefficient columns. No coefficients
   of \(R\) have needed reduction up to this point: only
   the base data \(h,m\) and the zero full-order minors.
   That unit pivot implies over characteristic zero that a
   nonzero actual solution cannot have fourth coefficient
   zero; the first three columns already have rank three.
   Thus the normalized monic cubic is forced. Cramer's rule
   with the very same pivot computes its first three
   coefficients in the localized integral ring and proves
   their integrality at the selected prime. No degree or
   normalization case was dropped.
4. The replay checks units for \(p,p-1,q,q-1,p-q\) and
   both values \(R(0),R(1)\); it also checks the local
   quadratic leading coefficients and all denominators
   in (3). Each of \(x,1-w\) is then a root of a
   **monic** quadratic with localized integral
   coefficients. Extend the prime and use the universal
   two quadratic quotient algebras, rather than ordering
   or choosing roots. The \(3\times3\) determinant of (4)
   is a unit in this full product-covering algebra.
   Cramer's rule yields integral \(l,d\), and the monic
   quadratic for \(y\) then covers either order for \(y,z\).
5. At the top of the tower the exact value of the
   primitive pairing in (5) is a **unit** in all retained
   algebras. Every real or complex root assignment of the
   characteristic-zero conditions reduces via the
   corresponding evaluation map from one of these
   universal quotient algebras, so the pairing would
   reduce to a nonzero scalar. This contradicts (5).
   The finite unit test uses trace/norm inversion for
   each quadratic extension even if it is split or
   nonreduced; it does not assume every quadratic is
   irreducible. The base residue fields alone use the
   checked irreducible factors. Of the seven distinct
   base factors, four are discarded by literal base
   tests and all three retained towers pass the unit
   seam test.

A prime above 41 exists by lying-over on each finite integral
root algebra used here; at each pivot localize at the chosen
prime before adjoining the next roots. The proof applies to
an arbitrary characteristic-zero field because the relevant
algebraic parameters lie in these finitely generated
algebraic subfields. The actual fitting and seam conditions
did not require a real-order or sign hypothesis.

[ERK10DistinctDormantElimination.lean](ERK10DistinctDormantElimination.lean)
checks the integer determinant grids and both modular
factorizations.
The separate exact sparse-polynomial replay checks all
finite algebra tower operations, including the unit guard
at the seam. The rooted correspondence, interpolation
bounds, and prime-lifting argument are given mathematically
above. Neither the eight-label ten-active chart nor the
unrestricted 14–15 numerical interval closes here.
