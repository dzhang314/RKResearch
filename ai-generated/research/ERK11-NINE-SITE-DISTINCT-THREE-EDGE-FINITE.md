# Nine live sites: finite edge atlas for the four-distinct three-cross diagram

**Scope.** Continue the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md)
with four distinct calibration labels, left extras \(\{e,t\}\) and
right extras \(\{h,t\}\). All three shared labels \(h,e,t\) are
ordinary crossing pairs. Assume the dormant stage is physical 8
or 10. Over an ordered field this earns a live shifted linear
pivot and a **finite algebraic width atlas**, including exact
elimination of the full singular-pivot fiber. It does not yet
exclude the finite regular candidates. The algebraic conclusions
also hold over characteristic zero if the two stated centroid
denominators are live.

## 1. Actual centroid and shifted rows

The other free active label \(u\) occurs twice in the inner
three slots. At physical dormant 8 these are rows 9 and 10.
Use the [literal repeated-inner centroid argument](ERK11-NINE-SITE-HALF-SAME-EDGE-EXIT.md):
the actual \(AV_L\) and \(V_R\) pair only on 9 and 10,
at a single clock. With
\[
 J_a(X)=\int_0^X Y^2(Y-a)^2\,dY,\quad
 V_b(X)=(1-X)^2(X-d)^2,\quad W=X^2(X-a)^2 V_b,
\]
put \(H=\int J_aV_b,\ C=\int XJ_aV_b,\ I_j=\int X^jW\).
Then \(C=uH\) by the actual grades \(5+4+1\le10\).
The positive simplex square for \(H\) makes it nonzero
over any ordered field. Since the actual \(V_LV_R\) only
sees the repeated \(u\) and the dormant \(\zeta\), its
tests with \(X-u\) and \(X(X-u)\) give
\[
 \zeta=\frac{N}{M},\qquad M=I_1H-I_0C,\quad N=I_2H-I_1C .
\]
Indeed if \(M=0\) these tests force \(N=0\), contradicting
the strictly positive \(I_0I_2-I_1^2\) of the nonzero square
weight \(W\). No sign or value of the dormant mass is
assumed. Both positivity claims extend from rational
positive Gram pivots to ordered fields.

The monic active hull is \(P(X)(X-t)/H\), where
\[
 P=(X-a)(X-h)(X-d)(X-e)(HX-C).
\]
Set \(m_j=\int X(1-X)P X^j\) and
\(e_j=M m_{j+1}-N m_j\). The **actual two shifted
nodal rows** at the nine scalar nodes are
\[
 e_1=t e_0,\qquad e_2=t e_1 .
\]
These are exact after multiplying by the live \(HM\).
Unlike the eight-node proof there is no third shifted
test available here, and no old Hankel minor is assumed.

## 2. The whole singular linear fiber is impossible

If \(e_0=0\), consistency forces \(e_1=e_2=0\).
The standalone replay keeps these three exact polynomials
after stripping only proven-live factors. Those factors
are the widths; calibration collisions and endpoints;
\(H,M\); the differences of \(u=C/H\) and \(\zeta=N/M\)
from the calibrations and endpoints; and \(\zeta-u\),
all cleared by the already-live denominators. No
regular-pivot assumption enters this branch.

Eliminate \(b\) between residual \(e_0\) and each of
\(e_1,e_2\). The resultants have degree 124 in \(a\).
Their gcd has the factor \(a\) with multiplicity eight,
a degree-8 factor with multiplicity four, and a degree-12
factor once. The root \(a=0\) is invalid. At the degree-8
factor the exact common \(b\)-gcd of all three residual
equations has degree two, and **divides \(C-dH\)**.
Thus \(u=d\), a forbidden active label collision.
At the degree-12 factor the common \(b\)-gcd is linear
and divides \(M\), a forbidden centroid pivot.
These gcds are computed in the actual coefficient
quotients using only unit Euclidean pivots. Hence no
singular \(e_0=0\) value has been dropped.

## 3. Finite regular widths and two more paid gates

Now \(t=e_1/e_0\), and the second actual shifted row
requires \(D=e_0e_2-e_1^2=0\). Use the first inverse-Gram
contact with scaled factors
\[
 L_0=(a-e)(a e_0-e_1),\quad L_1=-e e_1,\qquad
 R_0=(h-d)(e_1-d e_0),\quad R_1=-(1-h)(e_0-e_1).
\]
It is the same row-7/row-11 zero pairing as in
the eight-clock atlas, multiplied by \(e_0^2\).
After removing only actual live guards (now including
\(e_0\) and the distinctness of \(t\) from all other
labels and endpoints), the primitive determinant and
contact polynomials have total degrees 32 and 40.
The exact rational bivariate gcd is constant. Their
common affine zero set in the plane is consequently
finite over an algebraic closure: the resultant in
\(b\) is nonzero, and an infinite vertical fiber would
be a common nonconstant factor. This gives finite
width candidates and fixes \(u,\zeta,t\) for each;
it is not already a contradiction.

Two further exact necessary gates are built in the
replay, but not claimed to empty this finite set:
* use the actual dormant edge \(D_\zeta\)-pairing
  with the derivative character of physical row 11,
  clearing \(M^5\) and \(e_0\);
* for the repeated inner pair, test
  \(V_LV_R(C_{\rm clk}-uI)^2\), then use the scalar
  Lagrange weight at the dormant. If
  \(I_{uu}=\int W(X)(X-u)^2\) and
  \(I_H=\int X(X-1)H_6\), the cleared equation is
  \[
    I_{uu}(\zeta-h)(\zeta-e)(\zeta-t)
      = I_H\zeta(\zeta-1)(\zeta-a)(\zeta-d)(\zeta-u).
  \]
  The cancellation uses only the genuine new
  dormant clock, with all active labels distinct.
  This is grade \(4+4+2=10\).

At dormant physical 10 run the same polynomial proof
in the reflected coordinate, exchanging the front
roles. The mixed grade budgets remain valid without
ordinary reverse order eleven. The standalone
[`replay_n12_distinct_three_edge_finite.py`](erk11-nine-site-distinct-three-edge-finite/replay_n12_distinct_three_edge_finite.py) checks all
claimed singular fibers and the exact coprimality in
the regular branch; no Lean replay or complete regular
fiber exclusion is claimed.
