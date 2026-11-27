# Exact order-seven strict SDIRK with the third ghost at slot six

This is a new constructive nine-stage mask: the output weights
vanish only at physical slots \(1,2,6\). In particular slot 3
is active and genuinely cubic-dirty. It is not the older
first-three-ghost construction.

- Three separate literal \(\mathbb F_{19}\) tableaux are
  certified natively, one on the reflection suffix, one on the
  non-reflection arithmetic suffix, and one with normalized
  first active clock exactly one. Each passes all 85 rooted
  conditions through order seven and fails its eighth bush.
- The reflection control has a nonsingular four-equation
  clock Jacobian and gives an all-powers, two-parameter
  mathematical lift with the same physical mask.
- The affine-helper condition \(x_a=1\) reduces the rational
  search to two **linear** quadratic-hull equations, one
  isotropy determinant, and one early-clock rational-square
  test. The subset with reflection terminal set
  \(\{0,1,4\}\) is exactly excluded over \(\mathbb Q\);
  the wider rational chart is unresolved.
- No resulting rational tableau, new global stage bound,
  or full exclusion of another stage mask is claimed.

## Placement from the actual dirty reverse chart

Assume exactly two initial zero weights, a third ghost of
zero quadratic seed, six distinct nonzero-weight clocks,
and a visible cubic defect; use normalized diagonal one and
reciprocal physical diagonal \(z\). For this chart the two
initial axes are paid in degree three: the actual seed
\(g=2Ax-x^2\) is quadratic-clean on the six active sites by
the [six-site purity gate](../strict-sdirk7-unpaid-head/README.md)
and supported only on those initial two axes. A nonzero
first tap and nonzero second seed separate them.

The degree-three tree space has dimension at least seven
by the four-dimensional Hilbert separation, the two axes,
and one visible cubic. The nonsingular grade step from degree
three to five then makes these dimensions exactly seven and
nine. At degree four the projection onto the six active
sites is onto, since otherwise its five-dimensional
degree-three image would be clock-invariant, contain the
constant, and so contain all clock powers. The two hidden axes
bring its rank to at least eight; the nonzero terminal
entry of \(bR\), \(R=CA-AC-A^2\), supplies the opposite bound.
This uses no claim that *all* quartic defects split off from
the scalar clock powers.

It follows, exactly as for the
[earlier dirty reverse reads](../strict-sdirk7-unpaid-head/README.md),
that the first adjoint error vanishes and \(x_{\rm last}=z-1\).
Use reflected clocks \(Y=z-x\) and the second error \(D\).
Then \(D\) annihilates the degree-four space, its entry
\(\delta\) on the third ghost is nonzero, and its entries
on the first two ghosts are zero. In fact \(\delta=0\) would
leave \(D\) supported only on the active image of that space,
which is full. The rows \(D,DY\) span the degree-three
annihilator when the last two physical rows are active.
Triangularity at those two rows with reflected clocks
\(1,u\) gives \(D_9/b_9=-1/2\) and \(D_8/b_8=M/2\),
where \(M=u^2-4u+2\). The four reverse reads on the full
tableau are
\[
 bA=bY,\quad (bY)A=bY^2/2-D,\quad
 (bY^2)A=bY^3/3+f(Y)D,\quad DA=(1+\theta(1-Y))D,
 \quad
 \theta=1/M,\quad f(y)=-4/3+(2\theta-2)(y-1)/3 .
\]
The order-to-row passage here is the graded mathematical
derivation. The raw scalar consequences below are native.

If the third ghost is penultimate, its first adjoint column
forces its only reverse tap to the last stage zero, so the
second read would give \(\delta=0\).
If it is at slot seven, write its two weighted taps to \(u,1\)
as \(p,-p\). Then
\[
 (u-1)p=-\delta,\quad (u^2-1)p=f(h)\delta,\quad
 (M+1)p/2=(1-h)\delta/M .
\]
The [native elimination](../../lean/RKCert/Research/SDIRKSevenLateGhostScalar.lean)
forces
\((u-1)(u^3-7u^2+10u-2)=0\).
Both \(u=1\) and the cubic are rationally impossible:
the first collides with the last clock and the cubic is
projectively rootless modulo three. These are placements
in the stated dirty chart, not all possible zero weights.

At slot six, there are three active successors with reflected
clocks \(v,u,1\). Their ratio quadratic
\(q_0+q_1 y+q_2y^2\) interpolates \(D_y/b_y\) there.
The three uniform weighted-tap reads have moments \(0,-\delta,
f(h)\delta\). The fourth thus becomes the native scalar
\[
 E(h):=-q_1+q_2 f(h)-\theta(1-h)=0 .
\]
On the reflection branch \(v=4-u\) the interpolation is
\(y^2/2-2y+1\), so
\[
 h=\frac{4-5M}{4-M}.
\]
If the denominator vanishes the raw read is nonzero, so this
division is valid. The arithmetic branch has \(v=2u-1\)
and the same \(E(h)=0\) with its own ratio interpolant.

## Four equations and a unit-pivot construction

Focus on the reflection branch and a third ghost clock \(h\)
distinct from the six active clocks (it may coincide with an
initial ghost). In physical active order use \(y=(a,b_*,c,v,u,1)\)
and let \(P(X)=\prod_i(X-y_i)\), \(I(X^j)=z^j/(j+1)\).
Define \(K_i=I(P(X)/(X-y_i))\), \(s_i=1/P'(y_i)\),
and \(\beta_i=s_iK_i\).
The first equation is \(I(P)=0\).
Fix the affine \(W\) from
\(W(u)=(u-h) M K_u/2\) and \(W(1)=-(1-h)K_1/2\);
the second equation is \(W(v)=(v-h)M K_v/2\).
Set \(D_i=s_iW(y_i)/(y_i-h)\),
\(\delta=W(h)/P(h)\), \(V_i=W(y_i)/K_i\), and
\(V_h=-\sum D_i V_i/\delta\).
The third equation is isotropy \(\sum\beta_i V_i^2=0\).
The extending zero coordinates at the first two ghost axes
are always understood. Barycentric interpolation gives
\(D Y^j=0\) through degree four, \(\beta Y^j V=0\)
through degree three, and \(DV=DYV=0\).

Let the first helper tap be \(t\), and use two polynomials
\[
 q_g(X)=(2-t)X+t-1,\qquad q_H(X)=(X-1)(X-1-t).
\]
The first equals the quadratic seed at the first two
head clocks \(1,1+t\), the second vanishes there.
For \(p=q_g,q_H\) put \(F_p=Jp-p\), where \(J\) integrates
from zero. Write \(x_a=z-a,\ x_b=z-b_*\),
and \(r=V_b/V_a\).
The fourth equation is
\[
 q_H(x_a)\big(F_{q_g}(x_b)-rF_{q_g}(x_a)\big)
 -q_g(x_a)\big(F_{q_H}(x_b)-rF_{q_H}(x_a)\big)=0 .
\]
It is at most quadratic in \(t\), and is the compatibility
of the two forward reads in the second active row.

For the actual assembly, the seven-by-seven block \(B\)
is on slots \(3,4,5,6,7,8,9\), so \(h\) is **inside** it.
Use the four reverse rows and corresponding targets from
above. The final three active columns solve chronologically
on their suffix, with their terminal scalar branch. In the
ghost column, three active taps satisfy the fourth condition
by \(E(h)=0\). At active \(c\) there are four later rows
\(h,v,u,1\), with a unit reverse minor, so in contrast to the
first-three-ghost architecture no fourth-ratio constraint is
imposed on \(c\). The first two active columns leave three
free taps inside the first three active rows.

On this block impose both forward reads
\(Bp(x)=Jp(x)-F_p(x_a)V/V_a\).
They hold on the first active slot automatically. The second
slot sets the first free tap via \(q_g(x_a)\), and the fourth
scalar equation ensures the other profile agrees there.
The third slot sets the two remaining free taps using the
two-profile determinant on \(x_a,x_b\).
For either profile the four reverse reads on the two sides
agree by integration by parts and the displayed \(D,V\)
moments. The last-four minor therefore makes the forward
equalities exact on all other rows.

Feed from the first two slots into each later row by exact
\(A1=x,\ Ax=x^2/2\); its two-by-two determinant is \(t\).
Then \(A g\) and \(A x^2-x^3/3\) are proportional to \(V\)
modulo the two initial axes (use the two forward polynomials).
The four reverse equalities extend to the initial two
columns by testing them on \(1,x\): all targets match by
quadrature and integration by parts, and their head minor
is a unit. Finally the paid flag is the span of \(g\) at
grade two, the span of the two axes and \(V\) at grade
three, the joint kernel of \(b,bY,bY^2,D\) at grade four,
the kernel of \(b,bY\) at grade five, and the kernel of \(b\)
at grade six. Those reverse reads make \(A\) and \(C\)
advance the flag, products involving \(g\) stay on the two
axes, and the grade-three square is paid by isotropy.
The remaining monomial primitive errors are paid by the
same reads against exact uniform moments. Root attachment
and multiplication therefore prove every order-seven
condition over the unit-pivot ring. This is a mathematical
assembly, not a native all-powers theorem.

## Finite controls and Jacobian

The principal [literal control](f19-reflection-late.json)
is
\[
 (z,u,v,h,a,b_*,c,t)=(1,0,4,16,7,6,9,3)\pmod {19},
\]
with diagonal 1, slot-three cubic defect nonzero, and eighth-bush
residual 1. The native witness also certifies the sixth axis
is not a grade-four paid defect. The four scalar equations
in variables \((z,u,a,b_*,c,t)\) have Jacobian
\[
 \begin{pmatrix}
 0&1&9&11&11&0\\16&13&8&11&14&0\\
 6&6&13&2&8&0\\15&7&7&5&9&8
 \end{pmatrix}\pmod {19}.
\]
The last four columns have determinant 13. The two-profile
forward minor is 18; the last-four reverse minor is 6.
The ghost residue \(\delta\) is 2, \(V_a=17\), and
\(q_g(x_a)=8\). All nodal differences, active weights,
\(M,4-M,u-1,t,z\) and small denominators are units.
Fix arbitrary \(z=1\bmod19,u=0\bmod19\); ordinary
first-order unit Hensel lifting gives a unique choice of
\(a,b_*,c,t\) in the residues above modulo every \(19^k\)
and in \(\mathbb Z_{19}\). The unchanged eighth-bush
residual is a unit. The exact script reconstructs the
tableau and independently checks all 85 trees at any
requested power; both power 12 and changed \(z,u\)
were replayed.

The separate [arithmetic control](f19-arithmetic-late.json)
has \((z,u,v,h)=(8,4,7,11)\), not the reflection relation,
and eighth-bush residual 1. The [affine control](f19-affine-late.json)
has \((z,u,a,b_*,c,t)=(10,0,9,8,12,3)\) and residual 6.
Both have the same weight mask and independent native
literal proofs. The all-powers claim above refers to
the principal reflection control, not an unverified
extension of the arithmetic control.

## A lower-degree rational chart, and its exact thin exclusion

Set \(x_a=1\), hence \(a=z-1\), and write the other two
early roots as those of \(X^2-sX+p\).
This is a rational design restriction, not a consequence
of the order conditions. At \(x_a=1\),
\(q_g(x_a)=1,\ q_H(x_a)=0\), so the fourth scalar equation
is affine in the helper tap. Put
\(U(X)=X^3/3-2X^2+3X-1\),
\(V(X)=X^2/2-2X+1\) (these are scalar polynomials, not the
visible stage vector). The native identity gives
\[
 t=\frac{U(x_b)-r/3}{V(x_b)+r/2}
 \quad\text{if the denominator is nonzero}.
\]
In addition the first two clock equations are linear
in \(s,p\): write \(I_j=I(X^jL)\) for
\(L=(X-a)(X^2-sX+p)\). Clearing the nonzero terminal
scales gives
\[
 I_3-5I_2+(6-M)I_1-(2-M)I_0=0,\qquad
 (M+4)I_0-(M+12)I_1+4I_2=0.
\]
Thus on two linear pivots the residual rational tasks
are a single isotropy determinant in \(z,u\), and a
rational square root of \(s^2-4p\), with either admissible
ordering. At the affine finite control the hull determinant
is 6, the tap pivot is 17, and the restricted Jacobian
in \((z,b_*,c,t)\) has determinant 5, all modulo 19.
This is a genuine lower-degree elimination, not a proof
of rational points.

For \(u=0\) or \(4\) the reflection suffix is the unordered
set \(\{0,1,4\}\) with \(h=-3\). The two linear hull
equations have no rational determinant zero except \(z=0\):
the remaining sextic is projectively rootless modulo 13.
Use the [two-remainder isotropy identity](../strict-sdirk7-arithmetic-suffix/README.md)
with \(R_4=(X-a)(X-1)(X-u)(X-v)\) and \(Q_2=X^2-sX+p\).
Here \(W(0)=3K_0\) and \(W(1)=-2K_1\); identical for either
ordered terminal pair by the third read.
After inserting the linear solution the numerator factors,
besides \(z\), have degrees \(6,8,8,8,12\) and no
projective roots modulo \(17,11,11,31,11\) respectively.
[check-late-affine.py](check-late-affine.py) verifies the
complete exact factor products. Additional denominators come
only from distinct-site gaps and nonzero active masses.
Thus this **particular** rational affine fiber is impossible,
even before the splitting or helper test. Arbitrary rational
\(u\) is not covered.

## Replay

    python3 check-late-lift.py --power 12
    python3 check-late-lift.py --z 20 --u 19 --power 4
    python3 check-late-affine.py

The lift and all finite literal checks use only the standard
library. The affine elimination uses SymPy 1.14.0 and
python-flint 0.8.0. Build
[SDIRKSevenLateGhostScalar.lean](../../lean/RKCert/Research/SDIRKSevenLateGhostScalar.lean)
and
[SDIRKSevenLateGhostF19.lean](../../lean/RKCert/Research/SDIRKSevenLateGhostF19.lean),
then run [proof-audit.lean](proof-audit.lean). Both are checked
with stock Lean 4.36.0. The Jacobian/Hensel and graded assembly
remain mathematical proofs with exact replay.
