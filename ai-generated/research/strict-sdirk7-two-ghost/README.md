# Seven active sites and two zero weights at strict SDIRK7

This packet uses a different nine-stage mask: only physical slots
1 and 2 have zero output weight. The other seven clocks are
distinct. It gives two exact native \(\mathbb F_{19}\) controls
with regular clock/helper Jacobians, and rational exclusions
inside two explicit subcharts. There is no rational witness
or exclusion of the full two-zero mask.

## Why a seventh active site gives a virtual cubic direction

On seven nonzero-weight coordinates the weighted diagonal
bilinear form is nondegenerate. The cubic clock-polynomial
subspace has dimension four and nonsingular Hilbert Gram
matrix, by the paid bush moments. Actual cubic defects pair
to zero with each other and with those four clock powers.
Their active projection is thus totally isotropic in a
nondegenerate three-space, of dimension at most one. The
native [seven-active rank lemma](../../lean/RKCert/Research/SDIRKSevenTwoGhostScalar.lean)
verifies the corresponding dimension inequality directly with
physical row annihilators.

If an actual quadratic defect \(g\) were visible, its paid
five moments and distinct sites would force at least six
nonzero active components. Then \(g,Cg\) would be independent
on the active sites, contrary to the isotropic rank bound
since both are cubic defects. Hence quadratic defects are
hidden. In the strict rational case the first two quadratic
seed entries \(1,1+2t-t^2\) are nonzero, so the two ghosts
indeed occupy the initial slots. If \(t=0\), the first two
rows are literal duplicates; folding them gives the forbidden
eight-stage rational method with a zero weight. Otherwise
\(g,Cg\) separate the two axes. The third row cannot be
fully cubic-clean by the native Laguerre gate.

With one visible cubic and these two hidden axes, the degree
three tree space has rank seven and the degree five space is
full by the nonsingular step. The active degree-four space
has rank six: if its rank stayed five, the active degree-three
space, which contains 1, would be invariant under clock
multiplication despite seven distinct clocks. The degree-four
total rank is at most eight by the nonzero terminal entry of
\(b(CA-AC-A^2)\). Thus the same four reverse reads as the
[earlier dirty charts](../strict-sdirk7-late-ghost/README.md)
hold, with no actual third ghost. This is a graded
mathematical ingress, not a global native HasOrder wrapper.
It does not assume degree-four polynomial/defect separation.

Use normalized reflected clocks \(y=z-x\), with last three
\(v,u,1\), and let \(P(X)=\prod_i(X-y_i)\) over the seven
active sites. Define \(K_i=I(P/(X-y_i))\), \(I(X^j)=z^j/(j+1)\).
Their quadrature weights \(\beta_i=K_i/P'(y_i)\) are uniquely
determined and exact through degree six **with no extra hull
quadrature condition**. Since the second error \(D\) has five
zero moments and no ghost entries, \(D_i=W(y_i)/P'(y_i)\)
for a nonzero affine \(W\). The rows \(D,DY\) span the
degree-three annihilator.

Put \(M=u^2-4u+2,\ \theta=1/M\), and
\(f(y)=-4/3+(2\theta-2)(y-1)/3\). The reverse reads are
\[
 \beta A=\beta Y,\quad
 (\beta Y)A=\beta Y^2/2-D,\quad
 (\beta Y^2)A=\beta Y^3/3+f(Y)D,\quad
 DA=(1+\theta(1-Y))D .
\]
At \(u=2\), the row \(E=D+\beta Y/2\) satisfies \(EA=EY/2\).
Its last nonzero component would have clock 2 by the unit
diagonal, necessarily the penultimate active stage, where
\(E=0\). Thus \(D=-\beta Y/2\), in conflict with its zeroth
moment and \(z\ne0\). At \(u=3\), \(E=D+\beta/2\) satisfies
\(EA=EY\); its last nonzero component would be at the last
stage and already zero. Then \(D=-\beta/2\) is likewise
impossible. These arguments do not require a third ghost.

Represent a candidate visible cubic by \(U(y_i)/K_i\),
where \(U\) is a quadratic numerator. This identifies all
three dimensions of the complement of the cubic clock powers.
The induced form
\[
 \langle F,G\rangle=\sum_i\frac{F(y_i)G(y_i)}{K_i P'(y_i)}
\]
is nondegenerate. The two additional annihilation conditions
are orthogonality to \(W,YW\), an independent pair in this
three-space. Their orthogonal line is isotropic exactly when
the two-by-two Gram determinant of that pair is zero.
In that case it lies inside their span: the visible stage
defect has numerator \(W(\alpha+\beta Y)\) for a scalar
linear multiplier. This is the virtual cubic direction,
not an additional physical zero-weight stage. If the first
Gram entry is nonzero, one chosen multiplier is
\(-g_{01}+g_{00}Y\); the other diagonal pivot gives
\(g_{11}-g_{01}Y\). The kernel identity is native.

The terminal W graph is fixed by the first two suffix ratios;
its value at \(v\) gives one scalar condition. If \(c\) is the
fourth-from-last active clock, exact chronology gives
\(G(c)K_c+E(c)W(c)=0\), where \(G,E\) are the
[interpolated reverse functions](../strict-sdirk7-arithmetic-suffix/README.md).
The last four active rows then have a unit reverse minor on
the regular chart. The first three active rows have three
free strict taps, assigned by the
[two forward profiles](../strict-sdirk7-late-ghost/README.md):
the second row has one compatibility condition, the third
row solves a two-by-two system. Both full forward equalities
follow by testing with the four reverse rows and using that
minor. The first two helper feeds solve the two exact
quadratic stage reads. This is the same unit-pivot graded
construction, but its seven-row block consists entirely of
active sites. In particular the affine first forward clock
one gives the same affine helper recovery, not a separate
quadratic tap equation.

## A centered symmetric arithmetic chart is rationally impossible

Impose \(z=2u\), with centered arithmetic suffix
\(v=2u-1\), and a fully symmetric active node set
\[
 \{u,\ u\pm(u-1),\ u\pm r,\ u\pm s\}.
\]
Choose the sign of \(s\) so that the fourth-from-last
clock is \(c=u+s\); the other early pair and its
chronological orientation are unrestricted. All three
radii are nonzero with distinct squares. The terminal
projection identities can be checked with the centered
functional \(I_0(T^{2j})=u^{2j}/(2j+1)\), odd moments zero.

Let \(d=u-1\), \(R=r^2,\ S=s^2\), and
\(T=u^3-7u^2+10u-2,\ J=4u^3-24u^2+39u-17\).
The centered and opposite-pair divided differences are
\[
 K_d=I_0\bigl(X^2(X^2-R)(X^2-S)\bigr),\qquad
 K_0=K_d-d^2 I_0\bigl((X^2-R)(X^2-S)\bigr).
\]
Opposite nodes have the same \(K\). Affinity at the center
and the terminal ratios give
\[
 A K_d-B I_0((X^2-R)(X^2-S))=0,\qquad
 A=2MT-MJ+T,\quad B=2MTd^2 .
\]
This is linear in \(R\), with a nonzero rational pivot.
Indeed after standardizing to \([-1,1]\) it is
\(A\,\mathrm{momNum}-B'\,\mathrm{momDen}=0\) with \(B'\ne0\).
If \(A\ne0\), a vanishing affine coefficient would make
the quadratic in squared position with roots
\(S/u^2\) and \(B'/A\) annihilate its first two moments.
They would then be irrational Gaussian squares
(the squared difference has square class 30).
If \(A=0\), the two uniform moments of a linear
polynomial already give the contradiction.
This is the native centered-radius pivot.

For the affine \(W=\alpha+\beta X\) in centered coordinates,
odd inner moments vanish. With \(m_j=\langle X^j,1\rangle\),
the Gram determinant is the native parity expression
\[
 (\alpha^2m_0+\beta^2m_2)(\alpha^2m_2+\beta^2m_4)
 -4\alpha^2\beta^2m_2^2 .
\]
[check-centered.py](check-centered.py) substitutes the
linear \(R\) recovery in this and the fourth reverse read,
clearing only nonzero radius, weight, Cramer and clock
scales. The two saturated equations have bidegrees
\((12,3)\) and \((26,4)\) in \(u,s\).
Their resultant in \(s\) has rational roots only
\(u=0,3\), both forbidden. The other factors have degrees
\(7,75,3,10\) and are projectively rootless modulo
\(11,11,2,3\), respectively. This excludes the entire
centered symmetric arithmetic subclass over \(\mathbb Q\).

Nevertheless the exact [centered finite control](f19-centered-control.json)
has \(z=12,u=6,r=1,s=9,t=10\bmod19\), diagonal 8.
Its eighth-bush is not the obstruction: the failed tree is
the root with four leaf children and one size-three bush
child, residual 9. The four-equation Jacobian in
\((u,r,s,t)\) has determinant 18; the chronological reverse
and forward minors are 5 and 4 mod 19. This controls the
finite chart, not its rational existence.

## An asymmetric affine cut with a different exact rational test

Independently let \(a=z-1\) and \(c=0\) on the arithmetic
suffix, and write the other two early roots of
\(Q_2=X^2-sX+p\). Thus
\(P=H_5 Q_2,\ H_5=(X-a)X(X-1)(X-u)(X-v)\).
There is no symmetry requirement. The two linear
hull equations come from the third terminal affine read
and the fourth chronological read. With the previous
\(\widehat G,\widehat E\) scaling they are
\[
 MJ K_v-2MTK_u-TK_1=0,\quad
 2(u-1)M\widehat G(0)K_0
 -\widehat E(0)(uK_1+MK_u)=0.
\]
These solve \(s,p\) linearly with no rational Cramer
exceptions: the gcd of the two pivot-resultants has linear
roots \(1,2,3,1/2\) only and degree \(2,2,28\) factors
projectively rootless modulo \(2,3,13\).
The linear values are invalid suffixes or collisions
(at \(u=1/2\), \(v=0=c\)).
The polynomial calculation is in [check-affine.py](check-affine.py).

There is a compact isotropy test on the regular hull.
In the residue algebra of \(P\), let
\[
 W^2/K=U_4+H_5(\nu_0+\nu_1X),
\]
where \(U_4\) interpolates \(W^2/K\) at the five fixed
sites. Recover \(\nu_0,\nu_1\) by one two-by-two solve
modulo \(Q_2\). This is valid because \(K,H_5\) are
units on the two split, distinct early roots.
The Gram entries are the coefficient of \(X^6\) in
\(X^j W^2/K\bmod P\), for \(j=0,1,2\). The three
coefficients are respectively
\(\nu_1,\nu_0+s\nu_1,\ U_{4,4}+s\nu_0+(s^2-p)\nu_1\).
Thus the determinant simplifies exactly to
\[
 \nu_1 U_{4,4}-\nu_0^2-s\nu_0\nu_1-p\nu_1^2 .
\]
The final algebraic identity is native. It gives a
rational candidate test followed by splitting \(Q_2\)
and the affine helper and chronological pivots.
After removing only the documented nonzero scales,
the primitive core has bidegree \((20,18)\), in
[affine-core.json](affine-core.json).
No rational parameterization of it is asserted.

The whole \(z\)-fibers at \(u=4,9\) are excluded by
degree-18 projective tests modulo 17.
The variable-\(u\) cuts \(z=2u-12\) (the line through
the finite residue point) and \(z=u\) (an extra
reflection pair) are also exactly excluded, by
degree-38 projective tests modulo 17 and 19.
These do not exclude the broader rational chart.

The separate [affine finite control](f19-affine-zero-control.json)
has \((z,u,a,b_*,d,c,t)=(6,9,5,13,16,0,13)\bmod19\),
diagonal 16, and eighth-bush residual 15.
Its restricted \((z,b_*,d,t)\) Jacobian at fixed \(u\)
has determinant 8, forward and reverse minors 16 and 7.
Both literal controls pass all 85 order-seven trees and
their respective exact next-tree obstructions. No
rational lift is inferred from either regular point.

## Replay

    python3 check-controls.py
    python3 check-centered.py
    python3 check-affine.py

The controls use the Python standard library. The eliminations
use SymPy 1.14.0 and python-flint 0.8.0 with exact arithmetic.
An optional --rebuild on check-affine.py regenerates the larger
bivariate core and can take a few minutes.
Build
[SDIRKSevenTwoGhostF19.lean](../../lean/RKCert/Research/SDIRKSevenTwoGhostF19.lean)
and
[SDIRKSevenTwoGhostScalar.lean](../../lean/RKCert/Research/SDIRKSevenTwoGhostScalar.lean),
then run [proof-audit.lean](proof-audit.lean). We checked
stock Lean 4.36.0. The full rational subclass eliminations
are explicit mathematical arguments and arithmetic replays
in addition to the native rank, scalar and literal gates.

Two separate rational follow-ups exclude a [fully reflection-symmetric active clock set](../strict-sdirk7-two-ghost-symmetric/README.md) and [two distinct active zeros of the virtual defect](../strict-sdirk7-christoffel/README.md). Neither excludes asymmetric nine-stage tableaux in general.
