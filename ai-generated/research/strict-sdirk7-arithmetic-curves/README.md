# Rational curves in the arithmetic-suffix SDIRK7 chart

This packet uses the
[arithmetic clock atlas](../strict-sdirk7-arithmetic-suffix/README.md)
for a nine-stage strict SDIRK method of order seven with three
initial zero weights, six distinct active clocks, a nonzero
visible cubic defect, and a distinct third ghost. The normalized
reflected clocks are \((a,b_*,c,v,u,1)\) with \(v=2u-1\),
and \(z\) is the reciprocal diagonal. Two different
one-dimensional cuts give the following exact results.

1. Fix \(c=0\), **leave \(z-2u\) free**, and consider the branch
   over the finite control \((u,z,a,b_*)=(4,8,9,15)\bmod19\).
   One explicit bidegree-\((26,21)\) curve and one rational
   square test characterize the rational clock cores on that
   branch. Neither \(u=4\) with arbitrary \(z\), nor \(z=8\)
   with arbitrary \(u\), has a rational projected point there.
   The curve is not globally excluded.
2. Instead require the visible cubic to **vanish at the
   sixth physical node**: \(W(c)=0\), leaving \(c\) free.
   This cut has only finitely many rational clock cores.
   A genus-three curve controls \((u,c)\), and over any
   allowed pair there are at most 128 ordered rational clock
   cores, including the singular Christoffel pivots.
   This finiteness proof does not enumerate the cores or assert
   that one exists.

No rational nine-stage witness or global exclusion is claimed.

## The uncentered \(c=0\) curve and a cheap exact recognition test

Use \(I(X^j)=z^j/(j+1)\), \(R_4=X(X-1)(X-u)(X-v)\),
\(Q_2=X^2-sX+p\), and \(A_j=I(X^jR_4)\).
At the chosen mod-19 point the quadrature pivot is a unit:
\(p=(sA_1-A_2)/A_0\). The quadratic \(F\) in \(s\) is the
fourth affine-over-linear read \(AN-BC\) from the atlas.
The isotropy equation is the two-by-two remainder determinant
\(\Phi\) from that atlas. The following fraction-free version is
implemented in [check-c0-curve.py](check-c0-curve.py):

- Use \(420 I\) and \(A_0Q_2\) for the polynomial moments.
  Multiply the four normalized rate ratios by the common
  scale \(2T\widehat E\). All these scales are units at the
  selected mod-19 point.
- Interpolate the cubic \(U_R\) with a common suffix Vandermonde
  denominator, and use pseudo-remainders in \(X\) modulo
  \(A_0Q_2\). This multiplies each remainder column by a
  nonzero power of \(A_0\). No elimination step divides by a
  polynomial that could vanish on the residue branch.
- In \(\mathbb Z[u,z,s]\) the resulting polynomial degrees
  \((\deg_u,\deg_z,\deg_s)\) are \((25,18,2)\) for \(F\) and
  \((75,79,6)\) for \(\Phi\). Take their exact resultant in
  \(s\). Of its 14 factors, precisely one vanishes at
  \((u,z)=(4,8)\bmod19\). It has multiplicity one,
  bidegree \((26,21)\), and 567 nonzero terms.
  [c0-projected-h.json](c0-projected-h.json) records this
  primitive polynomial \(H(u,z)\), with exponent triples
  \((i,j,0)\) and signed coefficients. Run with
  --rebuild to verify the complete integer factor product
  and the unique branch selection.

The partial derivatives \((H_u,H_z)\) are \((12,9)\bmod19\).
Thus the branch is smooth at the finite control. This agrees with
the full reduced order equations: the Jacobian minors with columns
\((z,a,b_*)\) and \((u,a,b_*)\) are 6 and 8 modulo 19 respectively
when \(c=0\). These show 19-adic local solvability with either
base parameter, not rational points.

For any rational \(u,z\) reducing to 4,8 modulo 19, first test
\(H(u,z)=0\) by integer evaluation. The remainder of \(\Phi\)
modulo \(F\) specializes to a linear polynomial in \(s\) whose
linear coefficient is a 19-adic unit; the unique residue root is
\(s=5\). Thus \(H=0\) forces both equations at the rational
linear root, and the quadrature equation gives \(p\) rationally.
The sixth clock is already \(c=0\). The last issue is exactly
whether \(\Delta=s^2-4p\) is a rational square. Its residue is
17, and a rational square root can be oriented to give
\((a,b_*)=(9,15)\bmod19\). All ghost, helper, chronological
and normalizing pivots then remain units, by the earlier
arithmetic assembly at this finite control. That assembly gives
exact order seven with the eighth bush nonzero modulo 19.
Conversely any rational tableau in this residue branch forces
\(H=0\) and the square discriminant. In particular, evaluating a
candidate needs only one univariate quadratic remainder and one
exact square test, not an additional algebraic extension
computation. The script's optional --u and --z inputs implement
these clock tests. A future positive result still needs the
literal rational tableau and full rooted replay.

There are two unbounded rational exclusions inside this cut:
\(H(4,z)\) has degree 21 and no projective root modulo 23;
\(H(u,8)\) has degree 26 and no projective root modulo 13.
The leading coefficients are nonzero at their primes, so neither
check loses rational points with a nonunit denominator. These
exclude only the stated branches, not the whole curve.
An optional height-bounded diagnostic sieves reduced \(u\)
projectively at several primes and factors each surviving
univariate integer polynomial for **all rational \(z\)**.
Its search in \(u\) remains bounded and is not used in any proof.

## A second, genuinely sparse cut: the visible cubic vanishes at \(c\)

Now leave \(c\) free, but impose \(W(c)=0\). Since the ghost is
distinct, \(D_c/\beta_c=0\), so the fourth reverse read gives
\[
 \begin{split}
 F_0(u,c)={}&6(u-2)(u-1)^2(c-1)\\
 &-3(u-3)(u-1)(2u-3)c(c-2)
 +(u-3)(u-2)^2c^2(c-3)=0 .
 \end{split}
\]
This ingress is native. Notice it is not the \(c=0\) cut:
the clock itself is unconstrained, while its visible cubic
defect vanishes.

### Geometric genus three

The bihomogeneous curve \(F_0=0\) in
\(\mathbb P^1\times\mathbb P^1\) has bidegree \((3,3)\).
Its discriminant as a cubic in \(c\) is
\(108(u-3)(u-1)^3 H_8(u)\), where \(H_8\) is squarefree of
degree eight and nonzero at \(1,2,3\).
The coefficients and exact gcd are checked in
[check-visible-zero.py](check-visible-zero.py).
At any finite \(u\ne1,2,3\) the leading coefficient is
nonzero. A simple discriminant zero only has one double root
and is a smooth point of the total curve: a singular double
root would have zero parameter derivative, giving
discriminant multiplicity at least two. A triple root would
also give multiplicity at least two. Thus no singular points
are missed there.

The special affine slices are
\(F_0(1,c)=-2c^2(c-3)\),
\(F_0(2,c)=3c(c-2)\), and
\(F_0(3,c)=24(c-1)\). At \(c=\infty\), the only possible
finite \(u\) values are 2 and 3: the coefficient of \(c^2\)
is nonzero at 2, and the leading coefficient has a simple zero
at 3, both giving smooth points. At \(u=\infty\) the
leading-in-\(u\) cubic is squarefree with nonzero leading
coefficient, so all points there are smooth. The one remaining
point \((u,c)=(1,0)\) is an ordinary cusp: in coordinates
\(u=1+x,\ c=y-x\), the quadratic part is \(6y^2\) and
the coefficient of \(x^3\) is 11. This is a unique branch
with delta invariant one.

There is no vertical component, since the only possible finite
values from the leading coefficient are 2 and 3 and neither
fiber is identically zero. The \(u=\infty\) polynomial is also
not identically zero. There is no horizontal component: the
fiber at 3 restricts any finite candidate to \(c=1\), which
fails at 2, while the leading coefficient rules out a component
at \(c=\infty\). Any two components of positive bidegrees
would intersect over the algebraic closure, giving a singular
point with more than one branch. The unique ordinary cusp has
only one branch, so the curve is geometrically irreducible.
Its arithmetic genus is \((3-1)(3-1)=4\), and its
geometric genus is \(4-1=3\).
Faltings' theorem implies only finitely many rational \((u,c)\)
on its smooth locus, which contains every allowed pair here.

### Finite fibers, even at singular Christoffel pivots

On the other five active sites the visible cubic has no zeros.
It spans the orthogonal complement to clock polynomials through
degree three there, and is isotropic. Thus their four-dimensional
polynomial Gram form is singular. The original six-site Gram
form is the invertible uniform Hilbert form by the paid order
conditions, and deleting the site \(c\) removes a rank-one
evaluation mass. The determinant lemma, or shifted Legendre
orthogonal polynomials \(L_j\), gives
\[
 \beta_c=\mathcal C(c/z)^{-1},\qquad
 \mathcal C(t)=\sum_{j=0}^3(2j+1)L_j(t)^2 .
\]
Here \(L_j(t)=P_j(2t-1)\) with \(P_j\) the usual Legendre
polynomial. In particular \(\mathcal C(0)=16\).

For any fixed allowed rational \((u,c)\) write
\(R_3=(X-1)(X-u)(X-v)\), \(J_i=I(X^iR_3)\),
\(A_i=J_{i+1}-cJ_i\), and
\[
 B_i=z^6\mathcal C(c/z) J_i-z^6 R_3(c)c^i .
\]
The quadrature and Christoffel mass equations become
\[
 A_2-sA_1+pA_0=0,\qquad B_2-sB_1+pB_0=0 .
\]
The determinant \(D=A_1B_0-A_0B_1\) has degree 14 in \(z\)
and leading coefficient \(2/75\). On \(D\ne0\), solve \(s,p\)
by Cramer's rule. Their leading terms are
\(s\sim(10/7)z\), \(p\sim(10/21)z^2\).
The mass equation gives \(K_c=O(z^2)\). For the other three
suffix sites,
\[
 K_y-K_c=(y-c)I\bigl(R_3Q_2/(X-y)\bigr)
       \sim (y-c)z^4/630.
\]
These are polynomial degree and leading-coefficient statements
for the rational functions in \(z\), not estimates used to
exclude a finite interval.

Because \(W\) has its only zero at \(c\),
the three \((y-c)/L_y\) are affine on \((1,u,v)\), where
\(L_y=r_y K_y\) as in the atlas. Hence
\[
 (1-c)L_uL_v-2(u-c)L_1L_v+(v-c)L_1L_u=0 .
\]
Clearing \(D^2\) gives a polynomial in \(z\) of degree 36.
Its leading coefficient is nonzero: up to exact nonzero
scales and the three clock gaps it contains
\[
 r_ur_v-2r_1r_v+r_1r_u
 =\frac{(u-3)(u-1)^2 M(2u^2-10u+11)}{2T}.
\]
Here \(u=1,3\) are already forbidden, \(M,T\) have no rational
roots, and a root of the last quadratic would make 3 a rational
square. Thus there are at most 36 regular \(z\)'s with at most
one \((s,p)\) each.

At any of at most 14 zeros of \(D\), the two linear equations
have at least one nonzero coefficient pivot by the atlas.
If they are consistent, the monic hulls form at most an affine
line. The map \(Q\mapsto(K_1,K_u,K_v)\) is injective on the
linear space of paid hull polynomials of degree at most two:
three zero \(K_y\)'s annihilate the moments of \((X-c)Q\)
against the three linearly independent terminal quadratics
\(R_3/(X-y)\), hence against every polynomial of degree at most
two. The paid read adds the monic cubic \(R_3\), so the first
four moments are zero. The four-by-four uniform Hilbert form
is invertible, forcing \(Q=0\).
The nonzero rate factors preserve this injectivity at a
candidate. A nonconstant monic-hull line therefore cannot map
into the reciprocal conic displayed above: the three
coefficients \(1-c,-2(u-c),v-c\) are nonzero, and at a valid
point all three coordinates are nonzero. The native relative
slope lemma proves that an identically satisfied conic would
force the two generating coefficient vectors proportional.
It follows that each exceptional \(z\) contributes at most two
\((s,p)\). Splitting the two early clocks gives at most two
physical orders, with a uniquely recovered ghost in each.
The total is at most \(2(36+2\cdot14)=128\) ordered rational
clock cores for each rational \((u,c)\). This counts cores,
not the choices of a degenerate assembly tap.

## Replay

[SDIRKSevenDirtyVisibleZero.lean](../../lean/RKCert/Research/SDIRKSevenDirtyVisibleZero.lean)
kernel-checks the raw fourth-read ingress, the uniform
Hilbert inverse, the conic-line obstruction, and the exact
rate leading factor. The bridge from the reviewed dirty
tableau, the genus and Faltings argument, and the projection
degree counting are separate mathematical proofs with
exact arithmetic receipts. The Lean gates were checked on
stock 4.36.0; see [proof-audit.lean](proof-audit.lean).

    python3 check-visible-zero.py
    python3 check-c0-curve.py --rebuild --height 200

The first command uses SymPy. The second uses SymPy 1.14.0 and
python-flint 0.8.0; rebuilding the fraction-free resultant
takes tens of seconds. The --height flag is optional and
diagnostic only. No floating point, numerical root scan, or
online solver is used.
