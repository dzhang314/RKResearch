# A non-Christoffel multiplier zero in the seven-active chart

Use the [seven-distinct-active, two-zero-weight chart](../strict-sdirk7-two-ghost/README.md)
over \(\mathbb Q\). The affine adjoint numerator \(W\) is assumed
nonzero at every active clock. The virtual cubic still has the
form \(V=WL/K\), with affine \(L\). This packet analyzes the case
where the multiplier \(L\), **not** \(W\), vanishes at an active
clock \(e\). It gives an exact quadratic-Padé classification and
two literal finite controls; no rational nine-stage tableau or
general exclusion is claimed.

## Exact quadratic classification

Remove \(e\) from the seven-site node polynomial, writing
\(P(Y)=(Y-e)S(Y)\), with \(S\) monic sextic. Use the original
degree-six quadrature functional \(I\), weights \(\beta_i\),
and the mass-deleted functional \(\ell=I-\beta_e\delta_e\).
Let \(g(Y)=\mathcal K(e,Y)\) be the uniform degree-three kernel
and \(U(Y)=(Y-e)g(Y)\). Define, as polynomials in \(Y\),
\[
 J_\ell(Y)=\ell\!\left(\frac{S(Y)-S(X)}{Y-X}\right),\qquad
 H_\ell(Y)=\ell\!\left(\frac{U(Y)-U(X)}{Y-X}\right),\qquad
 p(Y)=U(Y)J_\ell(Y)-H_\ell(Y)S(Y).
\]
Analogous subscripts \(I\) use the full uniform functional.
At a support clock \(y_i\ne e\), \(J_\ell(y_i)=\beta_i S'(y_i)\).
The expression for \(p\) is also
\(S(Y)\sum_{i\ne e}\beta_i U(y_i)/(Y-y_i)\).
Since \(\ell(UX^k)=I(UX^k)=0\) for \(0\le k\le2\)
by kernel reproduction and the exact sixth moments, \(p\)
has degree at most two. Also
\[
 p=U J_I-H_I S+I(S)g,\qquad
 p(e)=-S(e)(1-\beta_e g(e)).
\]
The first identity uses \(\beta_e S(e)=I(S)\);
in particular \(p\) is linear in the coefficients of \(S\).

With the nonzero multiplier scaled to \(Y-e\), put
\[
 V_i=\frac{W(y_i)}{\beta_i S'(y_i)}\quad(i\ne e),\qquad V_e=0 .
\]
The exact rational condition for this \(V\) to be isotropic
and to pay both \(D\) and \(DY\) is
\[
                         p=\tau W^2,\qquad \tau\ne0.
\]
Here the adjoint \(D_i=W(y_i)/P'(y_i)\) can be independently
scaled without affecting those payments. This condition does
not prescribe the Christoffel mass.

For necessity, first note that \(\beta_e g(e)=1\) is impossible.
It would make the restricted weighted cubic Gram matrix have
radical \(g\). The six-site orthogonal complement of the cubic
polynomials would be a two-space with one-dimensional radical
\(g\); every isotropic vector would be in that radical.
But the \(D\)-payment of \(g\) on the support would be
\(-D_e g(e)\ne0\), by the paid full \(D\) moments and \(W(e)\ne0\).
Thus the six-site cubic form is nondegenerate.
The projection of \(D/\beta\) onto this cubic space is
\(\gamma g\) with \(\gamma=-D_e/(1-\beta_e g(e))\ne0\),
since \(\ell(g q)=(1-\beta_e g(e))q(e)\) for every cubic \(q\).
Its remaining part is in the nondegenerate two-dimensional
complement and perpendicular to isotropic \(V\), hence is a
scalar multiple \(\lambda V\). Because \(D_i/\beta_i=V_i/(y_i-e)\)
on the support, interpolation yields
\[
 p=W L_0,\qquad L_0(Y)=(1-\lambda(Y-e))/\gamma,\qquad L_0(e)\ne0.
\]
At a support site \(V=U/L_0\), so the isotropy equation is
\(\sum_{i\ne e} W(y_i)U(y_i)/(S'(y_i)L_0(y_i))=0\).

If \(L_0\) is nonconstant with root \(h\), that root is not a
support site. Divide \(WU\) by \(L_0\); the quotient has degree
at most four and has zero six-site barycentric sum.
The constant remainder is \(W(h)U(h)\), multiplied in the
sum by the nonzero value \(-1/(L_{0,1}S(h))\).
Hence \(W(h)U(h)=0\). Since \(h\ne e\) and the
[rational kernel has no finite rational zero](../strict-sdirk7-christoffel/README.md),
\(W(h)=0\), so \(L_0\) is proportional to \(W\).
If \(L_0\) is constant and \(g\) is cubic, the barycentric sum
of \(WU\) is its degree-five coefficient, forcing \(W\)
constant. This again gives \(p=\tau W^2\).
For rational \(g\) of degree below three, the normalized
kernel argument must be at the center (the other roots of
Legendre \(P_3\) are irrational). There \(p\) has nonzero
quadratic coefficient (see below), so \(L_0\) cannot be constant.

Conversely with \(p=\tau W^2\), \(V=U/(\tau W)\) on the
support. Then \(bV=W/S'\) pays through degree three.
The terms in its norm are \(U/(\tau S')\) and those of
its \(D\)-pairing are \(g/(\tau S')\); both are zero by
six-site barycentric degrees at most four. Multiplication
of the latter by \(Y\) still has degree at most four.
Thus this is a sufficient scalar Gram construction too.

## Clock recovery and scope

Suppose \(e\notin\{1,u,v\}\). On every other site,
\[
 K_y=\tau W(y)^2/g(y),\qquad
 g(y)/r_y=(\tau/\Lambda)W(y)
\]
at the three terminal sites, where \(\Lambda W/P'\) is the
actual adjoint. Therefore this chart uses the same affine
opener \(\nu(g)=0\) as the
[Christoffel mass atlas](../strict-sdirk7-two-ghost-mass/README.md),
but a **different** clock polynomial. Choose \(W\) to equal
the affine interpolant, giving \(\Lambda=\tau\).
If \(e\) precedes fourth \(c\), the exact
\(G(c)W(c)+E(c)g(c)=0\) fourth read is also the same linear
clock recovery as in that atlas. It does not impose \(W(e)=0\).

For noncentered cubic \(g\), \(p=\tau W^2\) is equivalent to
\(S\equiv-\tau W^2 H_I^{-1}\bmod g\), since both polynomials
under comparison have degree at most two.
The inverse exists: \(U\) is a linear combination of monic
Legendre \(P_4,P_3\) with nonzero leading term; the usual
second-kind Wronskian with \(P_3\) is a nonzero constant.
Thus for an early \(e\) with known \(c\), divide also by
\((Y-c)R_3\) modulo \(g\) and normalize the residual quadratic.
For \(e=c\) itself, \(S=R_3S_3\) with \(S_3\) monic cubic:
the residue condition gives \(S_3=g/g_3+\tau H_*\).
The fourth row uses \(K_e=I(S)\) directly rather than removing
a zero factor:
\[
 G(e)I(R_3 S_3)+E(e)\tau W(e)=0 .
\]
Here \(G(e)\ne0\) for a valid candidate, since \(G+Eq\)
is the nonzero multiple of \(R_3\) and \(e\) is not a suffix site.
Also \(I(R_3 g/g_3)=R_3(e)/g_3\ne0\), so that row fixes
\(\tau\) in one rational linear solve. These recoveries still
require rational split roots and a feasible helper chronology.

At the uniform center one can use \(g=X^2-3/5,\ U=Xg\),
up to a nonzero scale in the centered coordinate \(X\).
Then \(H_I=X^2-4/15\) and the leading coefficient of \(p\)
is \(1/7-(3/5)(1/5)=4/175\), independent of the nodes.
With \(W\) made monic and root \(h\), the split condition is
equivalently
\[
 S\equiv-\frac{12}{175}(X-h)^2\pmod{X^2-3/5}.
\]
This verifies the centered two-by-two residual recovery
from known \(R_3,c\), without assuming any root split.
In a different placement, the center can equal the last
site \(e=1\). In the reflection suffix \(v=4-u\), interpolate
using just \(u,v\); \(W=(2/M)(M+2Y-8/5)\). The fourth
equation then factors through the two supported terminal sites,
leaving \(5c^2-19c+10=0\), rationally impossible
(discriminant \(161\)). This terminal-centered exclusion does
not cover arbitrary \(e\) or the arithmetic suffix.

## Independent finite controls

Both controls have \(W\) nonzero at every active site.
The actual normalized adjoint is checked against \(\tau W/P'\).
The computed cubic stage error \(B^2x-x^3/6\) of the scaled
tableau \(B\) is a verified nonzero scalar times \(V\), not
merely a supplied auxiliary vector.

| Placement of \(e\) | \((z,u,e,c,t)\) | Active reflected clocks | Eighth-bush residual |
| --- | --- | --- | --- |
| Second | \(3,0,13,8,8\) | \(5,13,16,8,18,0,1\) | 1 |
| Fourth | \(15,5,12,12,4\) | \(11,15,17,12,9,5,1\) | 11 |

The masses satisfy \(\beta_e g(e)=11,18\) respectively
over \(\mathbb F_{19}\), so neither is a Christoffel mass.
Both are native all-85 tableaux over that finite field only.

Run the standard-Python [rooted replay](check-controls.py)
and the [exact centered scalar replay](check-centered-scalars.py)
(SymPy 1.14). Build
[SDIRKSevenMultiplierZeroF19](../../lean/RKCert/Research/SDIRKSevenMultiplierZeroF19.lean)
and run [proof-audit.lean](proof-audit.lean).
The classification and clock reconstruction are written
mathematical arguments rather than a native HasOrder wrapper.
