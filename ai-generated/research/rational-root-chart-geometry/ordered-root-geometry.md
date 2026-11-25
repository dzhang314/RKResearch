# Geometry of the rational nodal chart: smooth, but not rationally parametrizable

## Scope and main result

Let \(p\) be quadrature order (degrees \(0,\ldots,p-1\) paid), let
\(m\) count distinct contributing sites, and put \(t=p-m\).
As in the [rational support bound](../rational-quadrature-four-shift/proof.md),
the paid characteristic-zero nodal equations are
\[
 \mathcal I(X^jP)=0 \quad (0\le j<t),\qquad
 \mathcal I(X^k)=1/(k+1),\qquad
 P(X)=\prod_{i=1}^m(X-x_i).
 \tag{1}
\]
For distinct nodes, the unique Lagrange rule pays all \(p\) moments
if and only if (1) holds: divide a degree-\(<p\) polynomial by \(P\)
and use the paid tests on its quotient. Its weights must all be
nonzero to count all sites. If the sites are rational, grouping and
the injection of \(\mathbb Q\) into the coefficient field give (1)
even with weights in an arbitrary characteristic-zero field; for
\(m\le p\), Vandermonde also forces the aggregate weights to be
rational. No positivity, ordering, or reflection is assumed. The
[donor theorem](../quadrature-donor-realization/realization.md)
transports contributing supports, not physical-stage minima.

There is a sharp geometric distinction between completing one nodal
shift and completing two or three. Compactify the **ordered roots**
in \((\mathbb P^1)^m\), keeping (1) as multihomogeneous equations.
For \(1\le t<m\) the resulting variety is a smooth, geometrically
integral complete intersection of dimension \(m-t\), with canonical
bundle
\[
             K_V=\mathcal O(t-2,\ldots,t-2)|_V.              \tag{2}
\]
It is rational for \(t=1\), but for **every \(t\ge2\)** it admits
no dominant rational-function parametrization, even geometrically.
For \(t=2\) its canonical bundle is trivial; for \(t\ge3\) it is
ample. Thus the near-boundary rational nodes are not obtained simply
by adding a rational choice of independent parameters to the
locally soluble coefficient equations. This is a global obstruction
to a *parametrization*, not to the existence of rational points.

## 1. Exact smoothness, including collisions and infinity

A weighted form makes the smoothness argument reusable. Fix
nonnegative integers \(A,B\), and define
\[
 \Lambda_{A,B}(F)=\mathcal I\bigl(X^A(1-X)^B F\bigr).
\]
Work over any characteristic-zero field (or its algebraic closure);
all integration identities here are formal on polynomials.
The square matrix
\((\Lambda_{A,B}(X^{i+j}))_{0\le i,j\le h}\)
is nonsingular for every \(h\): over the reals it is the
positive-definite Gram matrix for the positive-on-\((0,1)\) weight
\(X^A(1-X)^B\). Its entries and nonzero determinant are rational,
so it remains nonsingular over every such coefficient field.

Write each projective root as \([\alpha_i:\beta_i]\), with factor
\(\beta_i X-\alpha_i\), and set
\[
 P=\prod_{i=1}^m(\beta_iX-\alpha_i),\qquad
 F_j=\Lambda_{A,B}(X^jP),\quad 0\le j<t.
\]
Each \(F_j\) is a section of \(L=\mathcal O(1,\ldots,1)\).
At a geometric point with \(F_j=0\), use the charts
\(\beta_i=1\) for finite roots \(a_i=\alpha_i\), and
\(\alpha_i=1,\beta_i=0\) at infinity. Let \(r=\deg P\), the
number of finite roots counted with multiplicity. Then \(r\ge t\),
since a nonzero polynomial of degree \(<t\) cannot be orthogonal
to all the paid monomials by the Gram matrix.

If the Jacobian failed to have row rank \(t\), there would be
\(R\ne0\) of degree \(d<t\) such that differentiation in every
finite root direction gives
\[
         \Lambda_{A,B}\bigl(RP/(X-a_i)\bigr)=0.               \tag{3}
\]
This uses the literal derivative \(\partial P/\partial a_i
=-P/(X-a_i)\). It is valid for repeats and for a \(P\) with
constant factors at infinity; no derivatives at infinity are
needed to contradict the putative dependence.

Put \(\mu_j=\Lambda_{A,B}(X^j RP)\). Initially all moments
\(\Lambda_{A,B}(X^uP)\) with \(u\le d\) vanish by the paid tests.
Suppose inductively they vanish up to \(d+k\), so
\(\mu_0,\ldots,\mu_k=0\). Integrate the derivative of
\[
            X^{A+k+1}(1-X)^{B+1}R P .
\]
The boundary is zero. Factoring out the weight, the derivative
of \(X^{A+k+1}(1-X)^{B+1}\) gives
\(-(A+B+k+2)\mu_{k+1}\); its other term is a multiple of
\(\mu_k=0\). The \(R'\) terms give \(-d\mu_{k+1}\), since
\(X^{k+1}R'\) has degree at most \(d+k\) and
\(X^{k+2}R'-dX^{k+1}R\) has degree at most \(d+k\).
For the \(P'\) terms, use the product derivative
\(P'=\sum_i P/(X-a_i)\), summed over finite factors with
multiplicity. From polynomial division,
\[
 \frac{X^\ell}{X-a_i}
   =\sum_{j=0}^{\ell-1}a_i^{\ell-1-j}X^j
                +\frac{a_i^\ell}{X-a_i}.
\]
Equation (3) kills the last term when integrated with \(RP\);
the moments already zero kill the lower terms. Hence
\(X^{k+1}RP'\) gives zero, and \(X^{k+2}RP'\) gives
\(r\mu_{k+1}\). In total
\[
             (A+B+k+2+d+r)\,\mu_{k+1}=0.
\]
The scalar is nonzero in characteristic zero. The leading
coefficient of \(R\) then forces
\(\Lambda_{A,B}(X^{d+k+1}P)=0\), closing the induction.
Vanishing through degree \(r\) contradicts the Gram matrix
for \(P\ne0\). This proves the Jacobian row rank \(t\) at
**every** projective root point, even multiple and infinite roots.

There exist points over the algebraic closure: the moment constraints
are \(t\) independent linear conditions on degree-\(\le m\)
polynomials (restrict to degrees \(<t\) and use the Gram matrix),
and any binary form splits there, including factors at infinity.
The Jacobian computation makes the root variety a smooth complete
intersection of the claimed dimension. The argument also proves
smoothness for every endpoint-power weight \(X^A(1-X)^B\).

## 2. Why the local coefficient chart cannot be made rational

Here \(m>t\). For clarity, connectedness can be checked directly.
On \((\mathbb P^1)^m\), by the cohomology of \(\mathbb P^1\) and
Künneth, \(H^j(L^{-i})=0\) for \(j<m\) and \(i\ge1\).
In the Koszul resolution of the intersection of the \(t\)
sections, every possible contribution from a negative tensor
power of \(L\) has total cohomological degree at least
\(m-t>0\). Thus \(H^0(\mathcal O_V)=k\) over the algebraic
closure. The smooth connected intersection is geometrically
integral, since distinct components of a smooth variety cannot
meet. Adjunction now gives (2) from \(K_{(\mathbb P^1)^m}=L^{-2}\).
For \(t=2\) there is a nonzero global top form, and for \(t\ge3\)
the canonical bundle is ample (and has a nonzero global section,
as \(L\) is generated by sections). Both conclusions persist
under base extension.

A smooth projective variety of positive dimension with a nonzero
top form is not unirational in characteristic zero. Indeed a
dominant rational parametrization can be restricted to a
generically finite map from a same-dimensional projective linear
space. Separability pulls the form back nontrivially. Properness
makes the rational map defined at all codimension-one generic
points, so this differential extends as a regular top form on
the smooth projective domain. Projective space has no such form.

For \(t=1\), by contrast, take a freely varying prefix with
product \(H\). The last projective root satisfies
\(\beta\Lambda(XH)-\alpha\Lambda(H)=0\), a rational solution
on the dense open where these two moments are not both zero
(for example \(H=X^{m-1}\) shows it is a nonempty open).
This is the rational one-shift completion. The change at \(t=2\)
is a property of the whole root chart, not an anomaly of a
fixed denominator grid.

The unordered coefficient chart is still a **linear**
\(\mathbb P^{m-t}\). The product map from ordered root coordinates
to the binary-form coefficients has a finite fibre, consisting
geometrically of the distinct orderings of the root multiset.
Over the distinct locus this is the usual symmetric-group cover.
Weak approximation for the coefficients can preserve finitely many
nonempty open local splitting conditions, but does not lift a
rational coefficient point to rational roots. A proposed dominant
rational parametrization of all roots on this chart would
contradict (2).

The open part that matters arithmetically is where the nodes are
finite and distinct and the Lagrange weights are nonzero. It
is nonempty geometrically: the usual degree-\(m\) monic
uniform Gaussian polynomial has simple roots and positive
weights and pays through order \(2m\). Its existence uses only
positive-definite Gram and the sign-change argument (no fixed
higher-order witness). For a simple root \(x\), its Lagrange
weight is \(C_P(x)/P'(x)\), where
\[
 C_P(Y)=\mathcal I_X\!\left(\frac{P(X)-P(Y)}{X-Y}\right).
\]
All weights are nonzero exactly when the resultant of \(P\) and
\(C_P\) is nonzero, an open condition. If exact scalar order
\(p<2m\) is requested, remove the next-moment hyperplane;
it is a proper cut by the same Gram nonsingularity. Rational
points of this open chart, not rational coefficient points
alone, are the sought supports. The non-unirationality does not
assert this open has no rational points, or that a Hasse principle
fails for these specific varieties.

At the order-20 boundaries this gives respectively:

| \(m\) | \(t=20-m\) | dimension of ordered chart | canonical class |
|---:|---:|---:|:---|
| 18 | 2 | 16 | trivial |
| 17 | 3 | 14 | ample |

## 3. A one-extra-root chart is already a positive-genus curve

A practical completion attempt fixes \(m-t-1\) earlier sites
and frees **one extra root** in addition to the \(t\) solved by
Hankel. Let \(H\) be the prefix product; the remaining \(t+1\)
ordered roots form the curve
\[
       \mathcal I(X^j H G)=0 \quad (0\le j<t)
\]
in \((\mathbb P^1)^{t+1}\). For a nonempty Zariski-open set of
prefixes this curve is smooth. Indeed the bad Jacobian locus
on the variable-root factors is closed in the projective
family, and its projection to the prefix space is closed by
properness. At the specialization with all prefix roots zero,
\(H=X^{m-t-1}\), the weighted argument of Section 1 proves
smoothness of the **entire** residual curve. So the good open
is nonempty and intersects the dense open of distinct finite
prefix roots. Choosing this repeated prefix just certifies
generic smoothness; it is not a candidate set of contributing
sites. One could use any endpoint-power prefix for the same
purpose. The curve is geometrically integral by the same
Koszul/connectedness argument. The variation is over all
prefixes, not a scan of fixed sets of rational sites.

If \(n=t+1\), the intersection number \(L^n=n!\) in
\((\mathbb P^1)^n\) and adjunction give
\[
            g=1+\frac{(t-2)(t+1)!}{2}.
\]
So the generic good-prefix fibre is **genus one** for two
shifts and **genus 13** for three. In particular, a fixed
rational prefix in the good three-shift open admits only
finitely many rational completions by Faltings (before the
finite-node, distinctness and cofactor-weight filters).
This is qualitative and fibrewise; it gives neither a
global finiteness assertion nor an effective uniform bound.
Exceptional prefixes off the good open need separate analysis.

### Explicit rational arithmetic inside the two-shift curve

For a chosen prefix \(H\), put \(M_i=\mathcal I(X^iH)\). The
matrix \(A_t(H)=(M_{i+j})_{0\le i,j<t}\) solves for the lower
\(t\) coefficients of the residual polynomial. On the additional
generic open where it is invertible, all monic degree-\(t+1\)
residual completions form a pencil \(G_\lambda=A+\lambda B\),
with \(A\) monic of degree \(t+1\) and coefficient of \(X^t\)
zero, and \(B\) monic of degree \(t\). Both satisfy the \(t\)
shifted tests, by the indicated linear solve. This open is nonempty
(again \(H=X^{m-t-1}\) is enough). Invertibility is **not**
asserted at every signed prefix when \(t+1\) sites remain.

For \(t=2\), write \(A=X^3+A_1X+A_0\) and
\(B=X^2+B_1X+B_0\). Choosing one remaining root \(a\) with
\(B(a)\ne0\) fixes \(\lambda=-A(a)/B(a)\). Dividing by \(X-a\)
shows the other two roots are rational iff
\[
 U^2=\mathcal D(a),\qquad
 \mathcal D(a)=A(a)^2+(2a+4B_1)A(a)B(a)
                         -(3a^2+4A_1)B(a)^2.                \tag{4}
\]
Here \(\mathcal D\) is at most quartic: terms of degrees six
and five cancel. The quotient discriminant is
\(\mathcal D(a)/B(a)^2\).
In an application also require nonzero discriminant, no root
repeated with \(a\) or the prefix, and the nonzero cofactor
weights. Conversely, those checks with a rational \((a,U)\)
certify the complete contributing rule by exact arithmetic.
The genus-one proof explains why substituting that extra root
does not reduce (4) to an automatic rational square. For
three shifts the same choosing-one-root step leaves an
ordered cubic split test, inside the generic genus-13 curve.

## Consequence for the current boundary

Exact prefix completion remains a useful global search reduction,
but passing local prime tests does not give an independent-rational-
parameter chart. The geometric obstruction applies across orders, with
both signs and no reflection. It does not decide whether rational
17- or 18-site order-20 support exists; hence it does not change the
17–19 rational contributing-site interval or any physical-stage
bound. For an actual rational point, the already proved donor
construction gives the same contributing support for the three
triangular classes with zero-output helpers permitted.

## Exact arithmetic checks

Run `python3 verify-pencil-identities.py` to reproduce the
[expected output](exact-check.txt). This exact check uses the
endpoint-power prefix specializations. It verifies the pencil
branch degrees through \(p=20\) and the quartic identity (4),
not a search for rational nodes. The smoothness and genus
statements follow from the proof, not from these specializations.
No Lean certificate is claimed.
