# An elliptic test for two-shift rational quadrature completion

For \(m\ge3\), can \(m\) distinct contributing rational sites pay
quadrature order \(p=m+2\) for the uniform functional
\(\mathcal I(X^j)=1/(j+1)\)? The
[ordered-root geometry](../rational-root-chart-geometry/ordered-root-geometry.md)
gives a genus-one curve for a generic fixed prefix. Genus one neither
excludes rational points nor supplies a rational origin. Here is an
exact point test and a conditional way to get an origin, including a
candidate that needs no rank computation. The result does not settle
a rational support endpoint or change an RK stage bound.

## The pencil and the contributing-point test

Fix \(m-3\) distinct rational prefix sites with product \(H\), and set
\(\Lambda(g)=\mathcal I(Hg)\). The monic residual cubic must pay
\(\Lambda(G)=\Lambda(XG)=0\). If the two-by-two Hankel matrix
\((\Lambda(X^{i+j}))_{0\le i,j<2}\) is invertible, the exact affine
pencil is
\[
 G_\lambda=A+\lambda B,\qquad
 A=X^3+A_1X+A_0,\qquad B=X^2+B_1X+B_0.
\]
For a proposed rational root \(x\) with \(B(x)\ne0\), the forced
parameter is \(-A(x)/B(x)\). The remaining quadratic quotient must
have rational square discriminant. Use the actual cubic quotient
or the projective ordered-root curve on exceptional coordinate charts.

Retain a point only if the three residual roots are finite, distinct,
and disjoint from the prefix, and
\(\mathcal I((HG)/(X-x))\ne0\) at **every** root \(x\) of \(HG\).
These are necessary and sufficient for contributing support:
polynomial division by \(HG\) proves that the Lagrange rule pays
the first \(p\) moments, and each displayed cofactor integral divided
by \((HG)'(x)\) is that site's weight. Both signs are allowed. If
weights are allowed in a characteristic-zero extension, the first
\(m\) moments still force rational aggregate weights by Vandermonde.
To require *exactly* order \(p\), also check
\(\mathcal I(X^2HG)\ne0\). The [RK donor theorem](../quadrature-donor-realization/realization.md)
applies to any paid scalar rule, with the same contributing sites
but not the same stage count.

For a general smooth pointed-root quartic \(U^2=\mathcal D(x)\), a
rational nonbranch point \((x_0,U_0)\) gives a square-leading quartic
via \(x=x_0+1/z,\ U=z^{-2}v\); the leading coefficient is \(U_0^2\).
A simple rational branch point instead gives a nonsingular cubic
under the same substitution. A point of the Jacobian without a
rational point on the curve does not start this construction.

## When a lower rule supplies an origin

Suppose there is a rational rule of **exact order \(p-1=m+1\)
on \(m-1\) contributing sites**. Choose any \(m-3\) as prefix
and denote the other two by \(u,v\); put \(\ell=v-u\) and
\(w_i=\mu_iH(i)\) for \(i=u,v\), where \(\mu_i\) is the lower
rule's weight. These effective weights are nonzero. The lower rule
pays \(\Lambda\) through degree three on these two sites, so the
Hankel determinant is \(w_uw_v\ell^2\ne0\) and \(B=(X-u)(X-v)\).
The parameter at infinity has the three different roots \(u,v,\infty\),
giving six rational smooth orderings.

Put \(h=\Lambda(X^2B)\); it is nonzero because \(X^2HB\) is monic
of degree \(p-1\) and this is the lower rule's first unpaid moment.
Write \(A=(X+c)B+C\) with \(\deg C\le1\). Then \(\Lambda(C)=0\)
and \(\Lambda(XC)=-h\), so \(w_uC(u)=-h/(u-v)\) and
\(w_vC(v)=-h/(v-u)\). In particular \(A,B\) are coprime.
Partial fractions of \(A/B\), with \(X=u+\ell z\) and an affine
change of parameter, give the normalized fibre \(f(z)=s\):
\[
 f(z)=z+\frac a z+\frac b{z-1},\qquad
 a=-\frac h{w_u\ell^4},\quad b=-\frac h{w_v\ell^4},\qquad
 z^3-(1+s)z^2+(s+a+b)z-a=0.                         \tag{1}
\]
In particular \(ab\ne0\). The same \(h=\mathcal I(X^2HB)\) works
for every pair of unretained sites. If the seed already pays order
\(p\), then \(h=0\) and \(C=0\); the extra node of
\(G_\lambda=(X+c+\lambda)B\) then has zero weight.

For a genuine seed, zero weight at a simple residual root \(x\)
would give \(\Lambda(G/(X-x))=\Lambda(XG/(X-x))=0\) by the first
pencil equation. This forces the monic quadratic \(G/(X-x)=B\),
contradicting \(\gcd(A,B)=1\). Thus the new residual weights are
automatically nonzero. Each old prefix site cuts at most one
parameter for collision (slope \(B(h_i)\ne0\)) and one for zero
weight (slope \(\mathcal I((H/(X-h_i))B)\ne0\) by the seed).
The cubic discriminant cuts at most four finite values and exact
target order cuts at most one, with nonzero slope \(h\). Including
infinity there are at most \(K=1+4+2(m-3)+1\) bad parameters,
each with at most six ordered points.

## The normalized curve and a rank-free candidate

Dividing \(f(x)-f(y)\) by \(x-y\) gives the \((2,2)\) curve
\[
 xy(x-1)(y-1)-a(x-1)(y-1)-bxy=0.
\]
With \(L=x^2+(a+b-1)x-a\), it has the pointed double cover
\[
 U^2=\mathcal D(x)=L^2-4ax(x-1)^2,\qquad
 y=\frac{U+L}{2x(x-1)} .
\]
The third root is \(1+f(x)-x-y\). Define
\[
 \alpha=b-a-1,\qquad \beta=a(2b+1),\qquad
 g=x^2+\alpha x+\beta,\qquad
 \eta=4ab(a-b),\quad\theta=-4a^2b(b+1).
\]
Expansion gives \(\mathcal D-g^2=\eta x+\theta\). Thus, if
\((a-b)(a+1)(b+1)\ne0\), set \(x=-\theta/\eta,\ U=-g(x)\).
Substitution for \(y\) and the product of the roots in (1) give
\[
 \boxed{\quad
 \frac{a(b+1)}{a-b},\qquad
 \frac{a-b}{a+1},\qquad
 \frac{a+1}{b+1} .
 \quad}                                                        \tag{2}
\]
When distinct, these form one complete finite rational fibre.
Map them back by \(z\mapsto u+\ell z\) and test old-node
collisions and old weights; check the extra moment if exact
scalar order is wanted. The denominator condition alone does not
guarantee a contributing completion, and a failed candidate does
not exclude other rational points. No smoothness is required
for (2).

The projective \((2,2)\) curve is smooth exactly when
\(\chi=(a+b-1)^3+27ab\ne0\). At the ordered simple poles,
\(1/f\) gives a local parameter. Off the diagonal, singularity
would mean two ramification points in one degree-three fibre.
On the diagonal it is equivalent to \(f'=f''=0\), or
\(a=x^3,\ b=(1-x)^3\). This is equivalent to \(\chi=0\):
in the converse direction let \(r=(1-a-b)/3\), so \(r^3=ab\);
the two roots of \(Z^2-Z+r\) have cubes of sum \(a+b\) and
product \(ab\). In the smooth case adjunction gives genus one
(the divisor is connected by the exact sequence of the \((2,2)\)
divisor). Its monic quartic has two rational infinity points.

If \(\chi=0\) and \((a,b)\ne(-1,-1)\), then \(r\ne1\) and
the unique triple point has \(x=(a+r)/(1-r)\), using
\(x^3=(1-r)x-r\). The degree-three map has local multiplicity
three there, so the divided difference has an ordinary double
point: its initial quadratic is proportional to
\(u^2+uv+v^2\) in local coordinates. There are no other singular
points; equivalently the quartic has one double root, and dividing
that squared factor out leaves a squarefree monic quadratic.
The normalization is a conic with a rational infinity point.
If \(a=b=-1\), the triples are \(x,1/(1-x),(x-1)/x\);
the indicated fractional linear cycle preserves \(f\).
In either singular case a genuine lower seed gives infinitely
many rational completions after the finite exclusions.

## Smooth case: exact elliptic point test

In the smooth case use
\(X_E=2(U+g)\), \(Y_E=(2x+\alpha)X_E+\eta\). The same expansion gives
\[
 E:\quad Y_E^2=X_E^3+(\alpha^2-4\beta)X_E^2
                 +(2\alpha\eta-4\theta)X_E+\eta^2 .       \tag{3}
\]
For \(X_E\ne0\) the inverse is
\(x=(Y_E-\alpha X_E-\eta)/(2X_E)\), \(U=X_E/2-g(x)\).
Use the smooth projective models when \(X_E=0\). The
positive-leading quartic infinity \((\infty,1,0)\) is the
elliptic origin; the other quartic infinity is \(D=(0,-\eta)\).
Formula (2) is the generic finite point \(-D=(0,\eta)\);
division in the affine inverse must not discard it.

Cycling the three roots has no fixed point on a smooth fibre
curve, since a fixed ordering would give a triple root.
An elliptic automorphism with a nonidentity group part has a
fixed point over the algebraic closure, as \(1-\phi\) is then
a surjective endomorphism. Thus cycling acts by order-three
translation. Taking \(x=0,\ U=-a\) in (3) identifies one cycle
point with \(-T\), where \(T=(4ab,4ab)\). The involution \(U\mapsto-U\)
has fixed branch points and interchanges the two quartic infinities,
so it is \(P\mapsto D-P\). The six infinity orderings are
\(\{O,T,-T,D,D+T,D-T\}\). For \(a=b\), \(D\) is 2-torsion,
so these points alone do not prove positive rank.

The exact criterion on (3) is a rational point off the bad
parameters above. Positive rank is sufficient: \(6K+1\)
distinct multiples of a nontorsion point include a good point.
With rational 3-torsion, Mazur's theorem gives a short exact
nontorsion test for \(D\): if none of \([6]D,[9]D,[12]D\) vanishes,
\(D\) is nontorsion. A rational origin alone is not sufficient.

## Which known inputs transfer

The distinct [u/128](../rational-quadrature-four-shift/standalone-19.md)
and [radii/33](../rational-support-radii33-splice/realization.md)
rules have 19 sites at order 20, a gap of one. They are not
17-site exact-order-19 seeds for an 18-site order-20 completion.
Nor can a proper subset be reweighted to order 19: the cardinal
polynomial of any omitted old site has degree 18, integral its
nonzero old weight, and vanishes on the putative new support.

In fact no completion on 18 contributing sites can retain a
reflection-invariant 15-site prefix from either fixture. In
centered coordinates the prefix product \(H\) is odd, hence
\(M_j=\mathcal I_{\rm centered}(HY^j)\) has \(M_0=M_2=M_4=0\).
The remaining four old nodes and their nonzero effective weights
pay \(M_0,\ldots,M_3\), so \(M_1,M_3\) cannot both vanish by
Vandermonde. If \(M_1=0\), the first cubic row is impossible;
otherwise both rows give \(G=(Y+\lambda)(Y^2-M_3/M_1)\).
The linear-factor node then has zero cofactor integral by
parity, whenever distinct. This uses no reflection or positivity
of the proposed new rule. Non-invariant prefixes remain open.

A gap-one rule cannot in general even supply a rational origin.
The positive four-site rule at \(0,1,1/3,4/5\) with weights
\(5/48,1/24,27/56,125/336\) has exact order five.
The empty-prefix width-three curve has no rational point:
finite distinct roots would contradict the
[four-site bound at order five](../strict-sdirk-rational/order-five-rational-support-lean.md);
finite repeated real roots leave at most one sign change, so
orthogonality to \(1,X\) is impossible by multiplying by the
interior sign-change factor, if any. One root at infinity
would leave the degree-two Gaussian polynomial (discriminant
\(1/3\)), and more infinity roots contradict the Gram rank.

Local points alone do not provide a rational origin either.
At a split active local rule with nodal polynomial \(P\), the
derivative of \(\mathcal I(X^jP)\) in residual root \(x_i\) is
\(-\mu_i x_i^jP'(x_i)\) for \(j=0,1\), by paid exactness.
Two residual directions form an invertible scaled Vandermonde.
Thus the local implicit function theorem and weak approximation
can retain local points at finitely many tested places on one
rational-prefix fibre, but do not give a rational point on it.

Run `python3 verify-elliptic-identities.py` in this directory
([expected output](exact-check.txt)) for exact rational
factorization, group-law and degeneration tests. The fixed
normalized probes are algebra tests, not asserted lower
quadrature seeds or a search for rational support. This is a
mathematical proof, with no new Lean claim.
