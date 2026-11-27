# The canonical opener quartic and the rational double read

This is a packet of exact **local** gates for strict SDIRK7.
It does not exclude the general nine-stage four-zero-weight
mask. In particular, at order seven the grade-four defect
space does **not** automatically split off from the five
clock powers, and cubic visibility and quartic visibility
are different hypotheses.

## Actual rank-two opening

Scale the nonzero common diagonal to one, put \(x=A1\),
\(C=\operatorname{diag}(x)\),
\(R=CA-AC-A^2\), and \(g=-R1=2Ax-x^2\).
Suppose the cubic defect space restricted to the first three
rows has rank two, and \(t=A_{21}\ne0\).
The two vectors \(g,(A-I)g\) are independent on the first
two rows, where their entries are \((1,\kappa(t))\) and
\((0,t)\), with \(\kappa(t)=1+2t-t^2\).
Consequently \((C-I)g=\kappa(t)(A-I)g\) on these rows and
on the third. Also \([A,R]1\) is cubic-pure and has first
two entries zero, so vanishes on the third. Writing
\(x_3=1+w\) and \(r=A_{32}\) gives
\[
 rt(2t-w)=0,\qquad
 w(\kappa(w)+2rt)=\kappa(t)(w+r(\kappa(t)-1)).
\]
If \(r=0\), then \(w=0,t,\) or \(2-t\).
The first two are literal duplicates (the third row has
only the first parent); the last is the reflected/star
branch. If \(r\ne0\), then \(w=2t\) and
\[
 (t^3-4t^2-t+2)r=-2t(3t-2).
\]
This denominator cannot vanish on the branch: it would
give \(t=2/3\), at which it is \(-4/27\).
The scalar classification and arithmetic seed interpolation
are native.

For the reflected/star branch with three distinct clocks,
the seed is interpolated by \(q(X)=-X^2+4X-2\).
Its first clean forward read \(Jq(a)=q(a)\) is already
rationally impossible, by the
[earlier Laguerre modulo-five receipt](../strict-sdirk7-paired-clean/README.md#other-rational-heads-and-a-direct-witness-attempt).
Here \(J\) denotes the primitive from zero.

On the arithmetic branch, after multiplication by the
nonzero denominator, the quadratic seed interpolant is
\[
 q(X)=\alpha X^2+\beta X+\chi,\qquad
 \alpha=-(t-2)(t-1)^2,\quad
 \beta=2t(t-2)(2t-1),\quad
 \chi=-2t^2(t-1).
\]
For a three-helper clean opening, \(Jq(a)=q(a)\) has
numerator proportional to
\[
 \begin{split}
 F(t,a)={}&(t^3-4t^2+5t-2)a^3\\
 &+(-9t^3+27t^2-21t+6)a^2
 +(18t^3-36t^2+12t)a-6t^3+6t^2 .
 \end{split}
\]
The Möbius tangent \(a=2t/(3t-2)\) gives
\(2t^3(t-2)(t-1)(31t-22)/(3t-2)^3\), recovering the
known nontrivial rational opener \((22/31,11)\).
This is an opening pair, not a nine-stage tableau.

## Canonical plane quartic; no rational quadratic elliptic quotient

The bi-projective model \(F(t,a)=0\) is precisely the
[genus-three cuspidal curve](../strict-sdirk7-arithmetic-curves/README.md#geometric-genus-three)
after \(u=t+1,c=a\).
On its normalization the sections \(t,a,ta\) of the
\((1,1)\) adjoint bundle vanish to order at least two at
the cusp; the canonical map is \([A:B:C]=[t:a:ta]\).
The inverse on the dense chart is \(t=C/B,a=C/A\).
Equivalently, the birational model follows directly from
this substitution and cancellation of \(C^2\). The equation is
\[
\begin{split}
 G={}&6A^3B-6A^3C+12A^2B^2-36A^2BC+18A^2C^2\\
 &+6AB^3-21AB^2C+27ABC^2-9AC^3\\
 &-2B^3C+5B^2C^2-4BC^3+C^4=0 .
\end{split}
\]
[check-opener-quartic.py](check-opener-quartic.py) checks
the birational identity and that the quartic has good
reduction modulo 5. Smoothness is checked over the
algebraic closure by exact polynomial ideals of the
three partial derivatives on all three affine patches.
Thus this is a smooth plane quartic model, not an
elliptic or rational parametrization.

In characteristic different from two, a projective
involution of a smooth plane quartic has an isolated
center \(p\) and a fixed line. For this finite field the
eigenspaces are defined over the field: if the square
of a matrix representative is a scalar, its determinant
in odd dimension makes that scalar a square.
The polynomial must be even in the center direction
(anti-invariance would make the whole axis a component).
Smoothness then forces \(G(p)\ne0\).
The fixed line is \(\nabla G(p)\cdot v=0\) from the
vanishing center-cubic coefficient; on that line the
center-linear coefficient also forces
\(\nabla G(v)\cdot p=0\).
The independent exact finite test and
[its Lean receipt](../../lean/RKCert/Research/SDIRKSevenOpenerQuartic.lean)
reject every mod-five center.

For completeness, the specialization of a rational
projective involution is justified here directly.
Write a projective matrix over \(\mathbb Q_5\) in Smith
form with exponents \(0\le a_2\le a_3\) after a common
scaling. The two integral unit base changes preserve
smooth reduction. If \(G_1(5^{a_i}X_i)\) is a scalar of
valuation \(e\) times \(G_2(X)\), smoothness of \(G_1\) at
the smallest exponent coordinate implies \(e\le a_3\):
either its fourth-power coefficient is a unit, or one
of the degree-three-by-degree-one coefficients is a unit.
If \(a_3>0\), the largest exponent coordinate has all its
value and first-derivative coefficients divisible by 5 in
\(G_2\), a contradiction. Hence the automorphism has an
integral unit matrix representative. An order-two
representative cannot reduce to a scalar: normalize it to
square one by lifting that scalar square root at 5; then
its sum with the identity is invertible if it reduces to
the identity, forcing the matrix itself to be the identity.
As a smooth genus-three plane quartic is canonically
embedded, every automorphism acts projectively on it.
Thus a rational degree-two elliptic quotient, which
would have a rational deck involution, is impossible.
No claim about higher-degree elliptic maps or a complete
enumeration of the rational points is made.

## The double primitive read

Some stronger clean-tail charts need both
\[
 Jq(w)=q(w),\qquad J(Xq)(w)=wq(w).
\]
For example these read the seed and its clock multiple
at the first active site if the relevant cubic and
quartic defects genuinely vanish there and the head
seed is the same quadratic polynomial on its donors.
The second equality is **not** assumed from order
seven alone.

The first equation is \(P=0\) with
\[
 P=2\alpha(w^3-3w^2)+3\beta(w^2-2w)+6\chi(w-1).
\]
For \(w\ne0\), subtracting the second primitive from
\(w\) times the first forces
\(Q=\alpha w^2+2\beta w+6\chi=0\).
The exact resultant in \(w\) is
\[
 48t^4(t-2)^2(t-1)^3
 (t^6-19t^5+112t^4-218t^3+41t^2+121t-54).
\]
The sextic is projectively rootless modulo 5.
The checked Lean Bézout identity removes the artificial
powers without cancelling any suspected zero pivot.
A literal check at \(t=1,2\), and direct substitution
at \(w=0\), leave **only \(t=1,w=0\)** when \(t\ne0\).

Two useful downstream scalar checks are kernel-verified:
a zero clock at this opening with only three prior
clocks \(1,2,3\) cannot meet all four pure primitive
moments (the last three kill its three strict taps);
and the next active clock of a clean linear-seed tail
would have to satisfy both \(x=x^2/2\) and \(x^2=x^3/3\),
forcing \(x=0\) and colliding with the first active clock.
These are conditional chronological checks, not a
claim that all grade-four differences are hidden.

A literal partial rational tableau explains the gap.
Take four unit-diagonal Euler rows with normalized
clocks \(1,2,3,4\); append the normalized row
\((-4,6,-4,1,1)\) at clock zero. These taps are negative
Lagrange weights for evaluation at zero on the four
donors. The fifth row really is quartic-clean at the
zero clock: [check-double-opening.py](check-double-opening.py)
independently evaluates all 17 stage trees through
size five, giving one at the leaf and zero otherwise.
There are no output weights or full order claim for
this partial tableau.

## Replay

    python3 check-opener-quartic.py
    python3 check-double-opening.py

The independent arithmetic scripts use SymPy 1.14.0.
Build [SDIRKSevenFourZerosScalar.lean](../../lean/RKCert/Research/SDIRKSevenFourZerosScalar.lean)
and
[SDIRKSevenOpenerQuartic.lean](../../lean/RKCert/Research/SDIRKSevenOpenerQuartic.lean),
then run [proof-audit.lean](proof-audit.lean).
We checked stock Lean 4.36.0. The geometry, specialization
and tableau ingress above are explicitly separate from
these scalar Lean gates.
