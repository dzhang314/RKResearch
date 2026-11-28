# A zero first reverse diagonal, and the five-prefix zero-multiplier exclusion

**Results.** In the normalized no-late invisible-six DIRK11/13
census, whenever \(\alpha\ge1\), the *literal first reverse ghost*
after the fixed old three ordinary rows has diagonal zero. When
\(\alpha=2\), the second such ghost instead has nonzero diagonal and
nonzero tap to the first. This is independent of the carrier degree
and the value of the reciprocal multiplier. Further, in the cubic
\(\tau=0\) case no candidate has \((\alpha,\beta,\gamma)=(1,0,5)\).
These are characteristic-zero results, with no order/sign assumptions.
The unrestricted real stage interval remains **13–14**.

Use exactly the normalized actual rooted-order-eleven invisible
six-ghost hypotheses of the [no-late count](../dirk11-thirteen-invisible-six-no-late/README.md)
and [forward masks](../dirk11-thirteen-invisible-six-prefix/README.md).
In particular all six ghosts are zero-weight and individually live
for both cubic heads; the three old ordinary reverse clock labels
are distinct, nonzero and live with nonzero weights. The true
terminal is an additional initial reverse row whose clock and
reverse cubic value are zero. The true spaces needed here are
\(F_5=g\mathcal P_2(c)\), \(F_6=g\mathcal P_3(c)+K(e_T-H_T(c))\),
\(Z_4=G\mathcal P_1(Y)\), \(Z_5=G\mathcal P_2(Y)\), in the notation
of those packets. Thus the order and chronology are used on the
given tableau, not on any altered or truncated tableau.

## 1. The actual first reverse gap

Write \(N=A^\mathsf T\) in literal reverse order, \(Y=1-c\) for
the reverse clock, \(W(P)=bP(Y)\) for its weighted row, and \(I\)
for scalar primitive from zero. Let \(R(Y)=Y^3+c_2Y^2+c_1Y+c_0\)
be the old three-root hull. In its cubic quotient choose the
quadratic-or-lower representative \(m\) of \(G_r/(r b_r)\) at each
old row \(r\). Set \(P=Ym,\ P_0=YR,\ \kappa=[Y^2]m\), and
\(P_1=YP-\kappa P_0\). Thus \(P,P_1\) of degree at most three
match \(G/b,YG/b\) on the old sites and the actual weighted
rows vanish at the literal terminal. Any nonzero common scale of
\(G\) can be used throughout.

Define \(l,r_1,t,w_0\), of degree at most two, by reducing
\(IP/P,IP_1/P,I^2P/P,IP_0/P\) modulo \(R\), respectively. The
\(P\) values are live on the old three. The actual paid cubic
row \(W(IP)-NW(P)\), and \(NG\), are both affine times \(G\).
Through the old three rows \(NW(P)=NG\) by inclusive donor
equality. Hence \(l\) is affine and
\[
 IP=lP+\delta P_0
\]
is an exact polynomial identity, since its difference vanishes
on the old three and at zero and has degree at most four.
Here \(l=l_0+l_1Y\); comparison with \(IP\) near 0 shows
\(l\) cannot be identically zero. Indeed in that case the
coefficient of \(Y\) in \(IP=\delta YR\) forces
\(\delta c_0=0\), whence \(\delta=0\), and then \(P=0\).

Use the actual degree-three matching for \(P_1\), with
\(N(YG)\in Z_5\), and the actual degree-four zero-weighted-input
read for \(P_0\), with primitive difference in \(Z_5\). At the
first reverse ghost \(z\), before the fourth ordinary row, the
only within-block donor is its own diagonal, so
\[
 d_z=l(z),\qquad r_1(z)=z\,l(z),\qquad w_0(z)=0 .
\]
These relations follow by subtracting the matched old weighted row
from the marked cubic row; at a ghost its own output weight is zero
but \(G\) is individually live. For \(P_0\), all weighted inputs
through the entire first gap vanish; hence \(w_0\) vanishes at *all*
of its ghost clocks.

Integration by parts gives, as polynomials after reduction:
\[
 r_1=Yl-t-\kappa w_0,\qquad
 (1+l_1)t=l^2+\delta w_0.
\]
The second follows by differentiating \(l\,IP\) and integrating
\(IP=lP+\delta P_0\); the exact polynomial identity before old
division is \((1+l_1)I^2P=l\,IP+\delta IP_0\).
All expressions divided at old sites have degree at most two
after reduction, so agreement on the three sites is actual
polynomial equality. At \(z\) the first relation gives \(t(z)=0\),
the second \(l(z)^2=0\). Thus \(d_z=0,\ l(z)=0\). Since \(l\)
is not identically zero, \(l_1\ne0\) and \(z=-l_0/l_1\).
There is no division by \(1+l_1\), any diagonal, \(z\), or any
possibly coincident ghost-clean clock here.

If there are two distinct gap ghosts, \(w_0\) is a genuine
quadratic. Otherwise its two zero evaluations imply \(w_0=0\),
in which case \(IP_0\) vanishes at the three old roots. Its
derivative \(P_0\) also vanishes there. These are three distinct
double roots of the nonzero degree-five primitive, impossible
in characteristic zero. Thus its other root is the second
physical reverse ghost \(w\). For the normalized actual tap
\(e=N_{w,z}G_z/G_w\) and diagonal \(d=d_w\), triangularity yields
\[
 d+e=l(w),\qquad z e+w d=w l(w)-t(w).
\]
The latter follows from \(r_1(w)=w l(w)-t(w)\), because \(w_0(w)=0\).
Combining with \((1+l_1)t(w)=l(w)^2\) and
\(l(w)=l_1(w-z)\) gives
\[
 (1+l_1)d=l(w),\qquad (1+l_1)e=l_1^2(w-z).
\]
The right-hand sides are live. Hence \(1+l_1,d,e\ne0\).
The native companion proves the two diagonal/tap implications
and the denominator-free scalar transfer below.

## 2. The exact five-prefix restriction when \(\tau=0\)

Now take \((\alpha,\beta,\gamma)=(1,0,5)\) and cubic \(\tau=0\).
Let \(a,b\) be the second and first **forward** nonorigin
ordinary clean clocks, \(V=1-a,\ B=1-b\). Write \(\xi=1-z\)
for the one other, late forward ghost. Scale the forward cubic
carrier \(U\) to be monic. Reciprocal support gives
\[
 U(X)=-R(1-X),\qquad G_a=G_b=G_O=G_T=0.
\]
Indeed \(U\) vanishes on the old three distinct forward clocks,
where \(G\) is live, and is live at all remaining clean labels.
Every ghost is disjoint numerically from the old three, since its
\(U\)-value is live. Therefore \(R(z)\ne0\).

Set \(\phi=U(c)-g\), and write \(H=XJ_4(X)\) with
\(H_T=30b_T H\). The true grade-four input \(C\phi\) is zero
on every inclusive donor to the five initial forward ghosts,
including the origin whose clock equals zero. The actual
\(F_5\) error gives
\[
 J+UQ_2=\eta R_5,\qquad J=I(XU),
\]
where \(R_5\) is the hull of those five ghosts. Indeed the left
side has degree at most five and is not zero: \(U\mid I(XU)\)
would force a monomial \(U\), contrary to its three distinct
nonzero roots. Thus \(\eta\ne0\) and \(J\) is a unit modulo
\(U\), since \(R_5\) and \(U\) are disjoint.

The actual grade-five input \(C(C-b)\phi\) vanishes on the
same inclusive donor sets and also through the first clean
\(b\). The actual \(F_6\) error yields an affine polynomial \(L\)
with
\[
 F_b-rH+UQ_3=R_5 L,\quad
 F_b=I[X(X-b)U],\quad r=F_b(b)/H(b).
\]
This uses degree at most six and makes no assumption about
the leading coefficient of \(L\) or its roots. The scalar \(r\)
is determined by the literal zero read at \(b\), and \(H(b)\)
is live by Jacobi coprimality. Consequently the ratio
\((F_b-rH)/J\bmod U\) is affine. The closed equation is the
three-coordinate determinant
\[
 \det(J,\ XJ,\ F_b H(b)-F_b(b)H)\pmod U=0.
\]

In the old **forward** coordinates
\(U=X^3+u_2X^2+u_1X+u_0\), exact coefficient calculation
factors the determinant as \(-b u_0 F_9/216000\), where the
source constructs \(F_9\) of total degree nine. The two
removed factors \(b,u_0\) are live. Ordinary quadrature gives
\(T_5=(J_5+\lambda J_4)/132\) with its five distinct
nonendpoint roots. Use \(\lambda=-J_5(a)/J_4(a)\), deflate
at \(a\), and then at \(b\) to recover \(U\). The cleared
ordinary quartic in \(b\) has leading \(132J_4(a)\).
Substituting the three recovered \(U\) coefficients into \(F_9\),
clearing that leader and taking the pseudo-remainder gives a
cubic in \(b\); its exact scalar content is proportional to
\((a-1)^2 J_4(a)^{12}\), live at the candidate. Its resultant
with the quartic factors as \(J_4(a)^4\) times an irreducible
degree-60 factor, up to a nonzero scalar. All these reductions
are performed symbolically in the rationals before reduction.

## 3. A genuine reverse quartic gate without the ghost clock

The \(G\) support now consists of the three old sites and six
ghosts, all nine clocks distinct. Pairing \(G\in E_7^\perp\)
with powers \(0,\ldots,7\) gives one direction, the inverse
derivatives of the nine-root hull. Likewise the flat clean
barycentric row is supported on the old three, \(V,B,1\)
in reverse coordinates, and there proportional to their hull
inverse derivatives. On regular old sites the clean weight
normalization is \(H_{{\rm bary},r}/b_r=h(r)=rJ_4(r)\).
Since \(R_6^{\rm fwd}=(X-\xi)R_5\),
\(R_5(1-r)=J(1-r)/\eta\) at each old zero of \(U\).
Comparing the two barycentric rows consequently gives, up to
one live scalar,
\[
 \frac{G_r}{r b_r}=\frac{m_0(r)}{r-z},
 \qquad
 m_0(Y)=\frac{J_4(Y)(Y-1)(Y-V)(Y-B)}{J(1-Y)}\pmod R.
\]
Each divided factor is live at every actual old root; the
transposition's common scalar is harmless in every homogeneous
zero condition. This comparison uses only the moment pairing
of the two rows, not any extrapolation of ghost weights.

Put
\[
 W_0(Y)=\frac{IP_0(Y)}{Y m_0(Y)}\pmod R .
\]
Cancel the polynomial factor \(Y\) in the numerator before
taking the old remainder. The actual quartic signal \(w_0\)
then equals \((Y-z)W_0(Y)\bmod R\), up to the same scalar
normalization. A monic cubic division of this degree-at-most-three
product subtracts precisely \([Y^2]W_0\cdot R\).
Hence evaluating \(w_0(z)=0\) yields
\[
 0=-[Y^2]W_0\cdot R(z),\qquad [Y^2]W_0=0 .
\]
The second follows from \(R(z)\ne0\). This pays a new
clock-only equation independent of any grade-seven ghost
polynomial or restriction on its leading coefficient.

The replay recovers \(b\) in the exact degree-60 clock algebra
by the linear cofactor of the two polynomials in \(b\). This
cofactor is necessary at every common root, including degree
drops. It verifies that the linear pivot is a unit modulo 101,
deflates and constructs \(U,R\), and checks the quotient
inversions and the **unit** \([Y^2]W_0\) modulo 101. These units
lift in the prescribed finite-free base algebra by the
multiplication determinant before any adjunction. A hypothetical
characteristic-zero candidate would specialize this unit to zero;
no coefficient or weight of it is assumed 101-integral.

## 4. Reproduction and native scope

Run **python3 replay.py** with SymPy and the two sibling
arithmetic sources. Optional **--arithmetic PATH** and
**--old-pair PATH** locate those sources in an isolated tree.
Python-FLINT as SymPy ground arithmetic substantially accelerates
the exact resultant but is not an additional mathematical
assumption. The companion **DIRKOrderElevenInvisibleSixEarlyGhost**
module verifies the common-hull and canceled-pole identities,
and the first and second literal diagonal implications. The
coefficient-ring rank argument, support ingress and finite
elimination are not claimed as one native tableau theorem.
