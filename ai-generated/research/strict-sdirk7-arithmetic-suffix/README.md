# Arithmetic-suffix cubic-dirty strict SDIRK7

This packet treats the distinct-ghost **arithmetic** branch of the
[necessary cubic-dirty chart](../strict-sdirk7-unpaid-head/README.md).
It assumes nine strict stages, the first three weights zero, six
distinct active clocks with nonzero weights, and a visible cubic
defect. It does not restrict the first two active clocks to a pair.

- Over \(\mathbb Q\), a two-coefficient quadratic nodal hull reduces
  the search to three base clocks, a quadratic test in one remaining
  hull coefficient, and a two-by-two isotropy test. The ghost and the
  generic helper need only rational linear recovery.
- Four centered arithmetic subfamilies are excluded over \(\mathbb Q\),
  with no restriction on the other two early clocks.
- A **separate** exact native \(\mathbb F_{19}\) tableau has a strictly
  unpaired arithmetic suffix chart, not in the reflection branch.
  A three-equation unit minor gives all-power lifts with two freely
  varying 19-adic parameters.
- At \(z=27,u=4\) the selected lift has a coefficient field of **exact
  degree 18**, with both a real place and a place in \(\mathbb Q_{19}\).
  This is not a rational tableau and does not improve the global
  rational stage bound.

## Arithmetic reverse ratios and a quadratic nodal atlas

Normalize the reciprocal strict diagonal by \(z=1/\gamma\).
In physical order the six reflected clocks are
\((a,b_*,c,v,u,1)\), with \(v=2u-1\), and \(h\) is the third
ghost's reflected clock, distinct from all six. Put
\[
 M=u^2-4u+2,\qquad T=u^3-7u^2+10u-2,\qquad
 \theta=1/M,\qquad f(y)=-4/3+(2\theta-2)(y-1)/3 .
\]
Over the rationals the already-published singular-suffix argument
excludes \(u=2,3\); distinctness excludes \(u=1\). Neither \(M\)
nor \(T\) has a rational root (both are projectively rootless
modulo 3).

Write \(r_y=D_y/\beta_y\) for the normalized second reverse error
divided by its active weight. At the last three sites these values
are
\[
 r_1=-1/2,\qquad r_u=M/2,\qquad
 r_v=M(4u^3-24u^2+39u-17)/(2T).
\]
Let \(Q=q_0+q_1X+q_2X^2\) be their interpolating quadratic:
\[
 q_0=(u-2)(u-1)^2/T,\quad
 q_1=-(u-3)(u-1)(2u-3)/T,\quad
 q_2=(u-3)(u-2)^2/(2T).
\]
The fourth chronological reverse solve has exactly three later
taps. The first three reads set their weighted clock moments; the
fourth, using \(Q\) to read these moments, is
\[
 G(c)+E(c)r_c=0,
 \quad G(y)=q_0(y-1)+q_1(y^2/2-y)+q_2(y^3/3-y^2),\quad
 E(y)=-q_1+q_2 f(y)-\theta(1-y).
\]
The numerator of \(G+EQ\) is a nonzero multiple of
\((c-u)(c-1)(c-v)(u-3)(u-2)^2(u-1)^3\); its denominator is
\(3MT^2\). Thus the actual read forces \(E(c)\ne0\) and
\(r_c=-G(c)/E(c)\), and also \(r_c\ne Q(c)\).
In particular the last four columns of the reverse matrix
with rows \(\beta,\beta Y,\beta Y^2,D\) are nonsingular.

For fixed \((z,u,c)\), set
\[
 R_4(X)=(X-1)(X-u)(X-v)(X-c),\quad
 Q_2(X)=X^2-sX+p,\quad P=R_4Q_2,\quad I(X^j)=z^j/(j+1).
\]
If \(A_j=I(X^jR_4)\), paid quadrature gives
\(A_2-s A_1+p A_0=0\). Thus either \(A_0\ne0\) and
\(p=(sA_1-A_2)/A_0\), or \(A_0=0,A_1\ne0\) and
\(s=A_2/A_1\). To see that no chart falls between them,
shift and scale to the centered uniform functional
\(I_0(X^{2j})=1/(2j+1), I_0(X^{2j+1})=0\).
An arithmetic quartic annihilating its first three moments would
have form \((X-r)(X-m)((X-m)^2-d^2)\) and be
monic Legendre-four plus a multiple of monic Legendre-three.
Its constant coefficient forces \(m\ne0\). Comparing coefficients
and putting \(k=r/m\) gives
\[
 63k^4+405k^3+1119k^2+903k+70=0.
\]
Its homogeneous reduction has no nonzero point modulo 11,
including at infinity. This is impossible for reduced rational
numerator and denominator. The shift and this entire alternative
are native, with original \(z,u,c\) and moment formulas.

At a node \(y\), put \(K_y=I(P(X)/(X-y))\), so the unique
weights are \(K_y/P'(y)\). For the four suffix sites put
\(L_y=r_y K_y\). Since \(D\) including the ghost annihilates
the first five moments on seven distinct sites, barycentric
interpolation gives
\[
 D_y=W(y)/((y-h)P'(y)),\qquad D_3=W(h)/P(h)
\]
for an affine \(W\). The ghost error is nonzero, so \(W(h)\ne0\).
At the four suffix sites this says \(W(y)=(y-h)L_y\).

Define the following affine functions of the remaining hull coefficient:
\[
 A=L_1-2L_u+L_v,\quad B=L_1-2u L_u+v L_v,\quad
 C=(u-1)L_c-(u-c)L_1-(c-1)L_u,\quad
 N=(u-1)c L_c-(u-c)L_1-(c-1)u L_u .
\]
The first three sites give \(Ah=B\), and \(A=0\) would
force \(B=0\), then \(L_1=L_u=L_v\), giving \(W(h)=0\).
Thus the ghost is \(h=B/A\). The fourth site gives
\[
 F=AN-BC=0.
\]
This polynomial in the free hull coefficient has degree at most
two. The scalar lemmas also show the four \(L_y\) must be distinct,
by injectivity of the genuine affine-over-linear function
\(W(y)/(y-h)\) away from its pole.
These statements do not rule out an identically zero specialized
quadratic; that case needs its other tests.

The visible cubic on the tail is proportional to \(W(y)/K_y\).
Its isotropy for the weighted form is
\(\sum_y W(y)^2/(K_y P'(y))=0\).
For an efficient test, let \(K\) be the divided-difference
polynomial \(I_T[(P(T)-P(X))/(T-X)]\), and
let \(U_R\) be the cubic interpolating \(W^2/K\) on the four
suffix sites. The leading coefficient of \(W^2/K\bmod P\)
at degree five must vanish. Its reduction modulo \(R_4\) is
\(U_R\), so isotropy is exactly
\[
 \det\bigl[\operatorname{rem}_{Q_2}(KR_4),\
            \operatorname{rem}_{Q_2}(W^2-KU_R)\bigr]=0
\]
in the coefficient basis \(1,X\). Here \(KR_4\) is a unit
modulo the split \(Q_2\), so its remainder is nonzero and the
test is equivalent to a scalar multiple of its first column.
The identity
\(K\bmod Q_2=(X-s)A_0+A_1\) follows directly from the divided
difference of \(R_4 Q_2\).
In the replays \(W\) is scaled by \(A\) and \(U_R\) uses the
values \((Ay-B)^2r_y^2K_y\), needing no inverse of a weight.

For a rational core the two remaining nodes are rational iff
\(s^2-4p\) is a rational square. On the usual nonzero helper
pivots, the [rational helper recovery](../strict-sdirk7-dirty-singular-cuts/README.md)
then adds no algebraic extension. In particular for \(w=z-h\)
and \(x=z-a\), the first-tail equation for
\(q(X)=(X-w)(X-\eta)\) is affine in \(\eta\).
If its projective solution is instead \(q=X-w\), the scalar
head condition with nonzero tap \(t\) forces
\(w\ne1\) and \(t=2+1/(w-1)\). The latter is a native scalar
identity, not a claim that every degenerate helper can be assembled.

## Four centered exclusions over the rationals

When \(z=2u\), with \(c=0,z,3u-2,\) or \(2-u\), no such
distinct-ghost tableau exists. The first two variants put the
sixth physical stage at a uniform endpoint; the other two
complete four equally spaced suffix sites. The other early
nodes and helper tap were not prescribed.

[check-centered-fibres.py](check-centered-fibres.py) makes
the two coefficient tests above over \(\mathbb Q(u)\).
In each case the quadrature pivot \(A_0\) and the leading
coefficient of \(F\) are nonzero at every allowed rational
\(u\), by the script's factor and projective root checks.
Reduce the isotropy determinant modulo \(F=f_2s^2+f_1s+f_0\)
to \(j_1s+j_0\). A common zero implies
\(f_2j_0^2-f_1j_0j_1+f_0j_1^2=0\), including when \(j_1=0\).
The script verifies the exact factor products, then finds a
prime for every nonlinear factor at which neither a finite
nor infinite projective root exists. The only rational roots
or poles left are \(u=0,1\) or \(u=1/2\) in the endpoint
variants. They give \(z=0\) or a clock collision. Distinctness
also protects the interpolation denominators; the other
utilized scales are \(M,T,E(c),A_0,f_2\), as checked above.
The proof does not assume that these four cuts exhaust the
arithmetic chart; in particular \(c\) may be different when
\(z=2u\).

## Separate finite control and two-parameter local family

The [literal F19 control](f19-arithmetic-control.json) has
\[
 (z,u,a,b_*,c,h)=(8,4,9,15,0,5),\qquad
 (y_7,y_8,y_9)=(7,4,1),\quad \gamma=12 .
\]
Its three early clocks have no pairs summing to \(z=8\), including
self-pairs. The suffix is arithmetic, not reflection, and the
third ghost is distinct. A native proof checks all 85 rooted
conditions through size seven and the order-eight bush payment
\(6\bmod19\), with residual 5. The third quadratic seed is
zero while the actual cubic defect on the first active stage
is nonzero. This finite point in the centered endpoint slice
is not a rational exception to the exclusion above.

In variables \((z,u,a,b_*,c)\), compute \(h=B/A\), and recover
\(W\) by its values at \(1,u\) (without scaling). The three
local equations are \(I(P)=0\),
\(W(c)-(c-h)L_c=0\), and \(\sum_y\beta_y(W(y)/K_y)^2=0\).
Their respective mod-19 differentials at the displayed point
are the rows
\[
 \begin{pmatrix}
 6&12&11&7&17\\9&14&11&16&13\\12&18&10&12&3
 \end{pmatrix}.
\]
The last three columns have determinant \(3\bmod19\).
The replay computes the differential exactly by increments
of 19 modulo \(19^2\); this is ordinary first-order expansion
of the displayed rational functions. All denominators are units:
the seven nodes differ, all six \(K_y\) and all weights are
nonzero; \(z=8,M=2,T=9\), and \(T E(c)=18\) under the script's
scaled convention. The ghost pivot is 5, the ghost error 10,
and its cubic coordinate \(v_3=5\). The quadrature pivot
\(A_0=7\), first helper coefficient 6, tap denominator 5,
tap 10, \(q(x_a)=16\), head minor 17, and last-four reverse
minor 10 are all nonzero modulo 19.

Fix arbitrary \(z,u\) in the residue classes \(8,4\) in
\(\mathbb Z_{19}\), or modulo \(19^k\). Varying the three
remaining coordinates at precision \(19^m\) changes the
residual mod \(19^{m+1}\) by their \(19^m\) digits times the
displayed invertible three-by-three minor. Induction gives
a unique lift in the chosen \((a,b_*,c)\) residue classes at
every precision and hence in \(\mathbb Z_{19}\).
In particular \(z-2u\) may be any element of \(19\mathbb Z_{19}\).
Reconstruct all matrix entries using the unchanged unit pivots.

Here is the assembly justification beyond the finite replay.
Append the ghost to \(D,v\), with \(v_y=W(y)/K_y\) and
\(v_3=-D_{\rm tail} v_{\rm tail}/D_3\), and both rows zero
on the first two axes. Barycentric interpolation gives the five
homogeneous moments for \(D\) and the four for \(\beta v\);
the isotropy equation gives \(D(Y-h)v=0\) as well as
\(\beta v^2=0\). The reverse reads for the tail block \(B_{\rm
tail}\) have rows \((\beta,\beta Y,\beta Y^2,D_{\rm tail})\)
and targets \((\beta Y,\beta Y^2/2-D_{\rm tail},
\beta Y^3/3+f(Y)D_{\rm tail},(1+\theta(1-Y))D_{\rm tail})\).
At the last three sites their compatibility is the preceding
terminal calculation. At \(c\) it is the fourth-read equation.
The first two columns solve from the last-four minor with one
tap left, which is set by the second physical-tail coordinate of
\[
 B_{\rm tail}q(x)=Jq(x)-Jq(w)v_{\rm tail}/v_3 .
\]
Here \(x=z-Y\) and \(Jq\) is the polynomial primitive from zero.
The first coordinate is the helper recovery equation.
Integration by parts and the \(D,\beta v\) moments make the four
reverse reads agree on both sides of this identity. The
last-four minor then completes the forward equality.

Use normalized head rows \((1,0,0),(t,1,0),(w-1-k,k,1)\)
with \(k=(w^2-4w+2)/(2t)\) and seed
\(g=(1,1+2t-t^2,0,\ldots,0)\). The head taps into each
active row solve its \(1,x,g\) reads. They enforce pure
quadratic stage accuracy on the tail and make the two actual
cubic defects \(A'g\), \(A'x^2-x^3/3\) proportional to \(v\)
modulo the first two axes, where \(A'=zA\). Testing on \(1,x,g\)
also extends all four reverse equalities on the three head
columns: the pure terms agree by integration by parts and the
error terms vanish by the homogeneous moments. Exactly the
[previous paid defect flag](../strict-sdirk7-unpaid-head/README.md#why-the-five-equations-suffice-over-a-unit-pivot-ring)
now applies. Its proof uses only that \(f\) and \(1+\theta(1-Y)\)
are affine, not their specific reflection values. Root attachment
and products prove the paid order-seven conditions over the
unit-pivot ring. The unchanged residue of the eighth bush is a
unit discrepancy, proving exact order after every lift.
The Hensel and flag argument is mathematical, not a native
all-powers theorem; the replay independently checks all 85 trees
at any requested finite precision.

## Exact specialization field degree and real place

Now take \(z=27,u=4\), so \(z-2u=19\). The two-by-two isotropy
and quadratic reduction work over \(\mathbb Q(c)\).
[check-degree-18.py](check-degree-18.py) computes the projection
by the two-term remainder formula above. Its primitive integral
numerator has precisely one factor \(H(c)\) vanishing at \(c=0\)
modulo 19; \(H\) has degree nine, multiplicity one, and derivative
16 there. The projection denominator, quadratic leading term,
quadrature pivot and the isotropy remainder's linear coefficient
are units at this place. Consequently the selected Hensel \(c\)
is a root of \(H\), and that linear coefficient recovers \(s\)
as an exact rational function of \(c\), followed by \(p\).
The script prints all coefficients of \(H\); a Rabin test modulo
29 proves irreducibility, so the sixth clock has degree nine.

The early discriminant \(\Delta=s^2-4p\) is nonsquare in
\(\mathbb Q(c)\): \(H\) has a simple root at 13 modulo 17
with derivative 2, where \(\Delta=5\bmod17\) is a nonsquare
unit. The induced \(17\)-adic place would otherwise contain
a square with that residue. Splitting the two early clocks
therefore doubles the degree. The tableau has exactly this
field as its coefficient field, since row sums and the known
reciprocal diagonal recover \(a,b_*,c\), and every table entry
was rationally assembled from them. The degree 18 refers to
this specialization and residue, not a rational exclusion in
other fibers.

The very same field has a real place. At the rational interval
\([2001421/1987785,\ 2950320/2930219]\), \(H\) changes sign
and exact interval Horner bounds make \(\Delta\) strictly
positive throughout. Thus its real root can be extended to
the field with the two early clocks. All identities and unit
pivots in this field are preserved at that embedding; in
particular the tableau still has exact order seven.

## Replay scope

[SDIRKSevenDirtyArithmeticAtlas.lean](../../lean/RKCert/Research/SDIRKSevenDirtyArithmeticAtlas.lean)
certifies the scalar moment and ratio pivots, the affine ghost
and quadratic read, and the projective linear-helper scalar
formula.
[SDIRKSevenDirtyArithmeticF19.lean](../../lean/RKCert/Research/SDIRKSevenDirtyArithmeticF19.lean)
kernel-checks the separate literal arithmetic control. They were
checked using stock Lean 4.36.0. Run [proof-audit.lean](proof-audit.lean)
after building the modules for checked signatures and axioms.
The arithmetic elimination, local ingress and flag assembly, and
degree/real-place checks are separate mathematical and exact
arithmetic certificates, not native Lean rational exclusions
for all strict SDIRK methods.

    python3 check-ap-lift.py --z 27 --u 4 --power 12
    python3 check-ap-lift.py --z 8 --u 23 --power 4
    for fibre in start end forward other; do
      python3 check-centered-fibres.py "$fibre"
    done
    python3 check-degree-18.py

The local lift uses the standard library only. Both elimination
scripts use SymPy 1.14.0 and python-flint 0.8.0; each command
runs in seconds with no approximate clock scans or floating point.
