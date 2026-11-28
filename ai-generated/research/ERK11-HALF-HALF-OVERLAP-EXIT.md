# Excluding the nonzero-mass half-half calibration overlap

**Scope.** Continue the characteristic-zero
[nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md),
now with \(h=e\), i.e. the left and right half-plateaus have a common
physical clock. This excludes the entire half-half overlap in that atlas
over a characteristic-zero field. It leaves the four-distinct
calibration case and all other ordinary ERK11 charts open. It uses
neither ordering nor ordinary reverse order eleven.

## 1. Exact calibration census

Use \(a,h=a/2\) for the left plateau and half, \(d=1-b,e=1-b/2\)
for the right, so now \(b=2-a,\ d=a-1,\ h=e\).
The eight-clock endpoint theorem gives \(a\ne0,1,2\), and the distinct
calibrations \(a,h,d\) are paid actual clocks. Call the three other
active clock labels free. There is one active triple and all other
active groups are pairs. Each front contains its two plateau rows,
one half-plateau row, and two distinct extras.

If no opposite plateau is chosen as an extra, each front chooses a
two-subset of the three free labels. For **the same extras** the
shared labels are the two chosen free labels and \(h\). At most
one is the triple, so there are at least two crossing pairs. When
\(h\) is the triple the two free labels cross. Otherwise \(h\)
and at least one free label cross. For **different extras** they
share one free label \(t\) and \(h\); write the left-only and
right-only extras \(u,v\). There are two crossings unless the
triple clock is \(h\) or \(t\), in which case exactly one pair
crosses and the inner clocks are \(\{h,u,v\}\) or \(\{t,u,v\}\)
respectively.

If an opposite plateau is chosen, that label has three front
occurrences and is the triple. Thus at most one such choice
exists; reflect to put the extra \(a\) on the right. The right's
other extra is a free label \(t\). The common half \(h\) is now a
crossing pair. If \(t\) also belongs to the left extras, \(t\)
crosses as well. Otherwise the left extras are the other two
free labels \(u,v\), and the inner clocks are \(\{u,v,t\}\).
Reflection here only exchanges the two scalar anchored read
systems. In particular these four cases exhaust the chart,
and there is always a crossing pair.

## 2. Eliminate at least two crossings by exact norm gcds

As usual write
\[
 H_6=(X-a)(X-a/2)(X-d)Q(X),\qquad Q=X^3+q_2X^2+q_1X+q_0 .
\]
The cubic fit is unique from the actual weighted Hankel pivot. The
moment determinant is
\[
 -\frac{(a-1)^3 E(a)}{1524096000},\qquad
 E=126a^6-756a^5+1752a^4-1968a^3+1113a^2-306a+34 .
\]
The exact replay builds the rational moment matrix, evaluates this
determinant, and clears the unique solution to \(q_j=r_j/M\),
where \(M\) is \(1848\) times the integer numerator of the determinant.
Thus \(M,E\) are nonzero on every actual layout.

For all four diagrams use the paid first contact \(\Psi=0\),
the inverse Gram pairing of rows 7 and 11. Construct its
clock-only norm over the free roots: take the monic cubic
for the selected root \(W=Mw\), and the monic quadratic
for a second selected root \(U\) with sum \(-r_2-W\) and
product \(Mr_1+W(r_2+W)\). The actual selected roots
evaluate this tower. On each diagram multiply the four \(\ell,r\)
coefficients of the contact by \(M^2\), so the evaluated
contact is \(M^4\Psi\). For the same extras, the contact already
depends only on the omitted free root and the pair sum and
product, so use the cubic norm alone. For opposite plateau
with disjoint extras, use the cubic norm in the right free
root \(t\) alone, because the left choice is its full complement.
For the two other diagrams take the quadratic norm first,
then the cubic norm. All norms vanish when the actual
contact does.

Use the independent pair equality \(\Xi(x)=\Xi(y)\) for any
two crossing pairs, with
\[
 \Xi(y)=\mathcal J(y)y(1-y)(a-y)(y-d),\qquad
 \mathcal J(y)=\int_0^1 X(X-1)
          \frac{H_6(X)-H_6(y)}{X-y}\,dX .
\]
This was derived in the [mixed-overlap two-cross proof](ERK11-MIXED-OVERLAP-TWO-CROSS-EXIT.md)
from \(\mu_x=k/H_6'(x)\), the actual two response readings,
and paid degree-seven scalar Lagrange quadrature; it did not
use the specific mixed overlap. All relevant clocks remain
distinct nonendpoints and none is a plateau.
The comparison of \(h\) with a free crossing root is a vanishing
cubic norm in that root; evaluate the cleared \(\Xi\) at
\(Mh\) and at the root \(W\). The comparison of two free
crossing roots is a vanishing cubic norm in the omitted root:
reduce the scaled \(\Xi\) modulo the monic complementary
quadratic and use its linear remainder coefficient, since the
two roots differ. As in that earlier receipt, the polynomial
for these computations is \(1680M^{10}\Xi(Y/M)\) with
integer coefficients; its exact construction uses the
integer polynomial \(2M H_6\) and its divided difference.

Strip from each integer norm only its integer content and
powers of \(a,a-1,a-2,E(a)\); every stripped factor is
proved nonzero. The residual contact norm degrees for the
same extras, different extras, opposite plateau with a shared
free clock, and opposite plateau disjoint are \(54,108,96,48\),
respectively. The crossover residual degrees are 42 (one
half, one free) and 20 (two free). Exact rational gcd
of the same-extras norm with each crossover norm is 1;
gcd of the different-extras and opposite-plateau-shared norms
with the half/free crossover norm is also 1. This excludes
all cases with two or three crossing pairs, without an ordering
argument.

## 3. One crossing: exact extra contact gates and chronology

The remaining differing-extras case has triple \(p=h\) or \(p=t\).
The earliest middle clock \(w=c_8\) is one of \(p,u,v\).
There are two choices of the left sixth, two of the reflected sixth,
and six orders of the three inner labels, for 24 schedules per
triple choice. If \(w=p\) or \(w=u\), it repeats a left label.
If \(w=v\) but \(c_{10}=p\), there is a reverse repeated label.
The other case is \(c_8=v,c_{10}=u\), with neither repetition.
For the opposite-plateau disjoint case the same 24 diagrams have
\(w\in\{u,v,t\}\): if \(w=u,v\) the left repeats, otherwise
use the two nonrepeat contacts.

Use the literal grade-five primitives and the adjusted
functionals \(\Phi,D_w,E_w\) of the
[mixed-overlap one-cross proof](ERK11-MIXED-OVERLAP-ONE-CROSS-EXIT.md).
The left actual row 7 is a nonzero multiple of \(\Phi_L\),
and row 8 belongs to \(\operatorname{span}(D_w,E_w)\);
the analogous statements hold at physical 11 and 10.
All primitive payments are through grade five and physical
rows 7 and 8 (or their reflected counterparts).

At a repeated left clock the adjusted row has expression
\(D_w/a^5+F_iT(w)\) both at the earlier physical \(i\in\{3,6,7\}\)
and at row 8. This holds also when the repeated clock is the
triple. If the two responses were equal, the anchored readings
would agree: row 8 would be zero for earlier row 3 or 6, or
duplicate row 7. Each contradicts the invertible mixed middle
read matrix. Thus the response difference is nonzero without
assuming that the local pool is an ordinary pair. Solving the
two readings shows \(D_w\) belongs to the span of rows 7 and 8,
so \(\langle D_w,\Phi_R\rangle=0\) by the exact off-diagonal
inverse Gram. In the reverse repeated case apply the same
reasoning to rows 10 and 11 and use
\(\langle\Phi_L,D^R_{1-c_{10}}\rangle=0\).
In the remaining schedules the 3-by-3 matrix of pairings of
\((\Phi_L,D_w,E_w)\) with its reverse counterpart has determinant
zero, since two independent actual rows on each side are
orthogonal. These are the independent second contact gates.

## 4. Finite free exclusion of every one-cross schedule

For the different-extras case the just-computed degree-108 contact
norm gives a scalar parameter polynomial \(N(a)\). For disjoint
opposite-plateau use its degree-48 contact norm. Their leading
coefficients retain degree modulo 101 and \(M\) is a unit modulo
each monic scalar modulus, checked by exact polynomial Euclid.
Thus the monic scalar algebra over \(\mathbb Z_{(101)}\) is finite
free, of rank 108 or 48, and multiplication by \(M\) is invertible
there. Its unscaled cubic \(Q\), followed by the complementary monic
quadratic, gives a rank-648 or rank-288 coefficient algebra over
\(\mathbb Z_{(101)}\).

Work first in its mod-101 specialization. For different extras
the first contact is \(A(t)+B(t)u\); its quadratic norm reduces
to a polynomial \(\nu(t)\) of degree at most two modulo \(Q\).
For disjoint opposite plateau the first contact already depends
only on \(t\); use its degree-at-most-two remainder \(\nu(t)\).
A zero of the contact always makes \(\nu(t)=0\). Exact Euclidean
division of \(Q\) and \(\nu\) with unit leading pivots yields
a linear polynomial with unit leading coefficient, so it fixes
\(t\) as a residue of the scalar parameter. The different-extras
case then fixes \(u\) by the live coefficient \(B(t)\) and trace
fixes \(v\). In the disjoint case leave \(u,v\) in their monic
quadratic algebra over the scalar residue ring, and check a unit
by the norm to that ring. This handles all specialized components
whether or not the scalar polynomial or quadratic splits.

The exact unit tests show that, for each different-extras triple
choice, all 16 left repeat pairings, four right repeat pairings,
and four remaining determinants are units modulo the first
contact. For the opposite-plateau disjoint chart, all 16 left
repeat pairings and eight remaining determinants are units. Thus
for any fixed chronology the first and second contacts generate
the unit ideal mod 101. The map \((x,y)\mapsto \Psi x+\Omega y\)
in fixed finite free bases therefore has a full-size minor that
is a unit in \(\mathbb Z_{(101)}\). It is surjective in
characteristic zero as well. An evaluation at a genuine tableau
would set both contacts to zero, impossible. As in earlier packets
this argument reduces a finite free coefficient algebra, not the
entries of an unknown tableau.

The [standalone Python replay](erk11-half-half-overlap-exit/replay_halfhalf.py) gives the exact norms, gcds and
all 72 unit checks without floating point. A separate Lean replay
of this larger coefficient computation is not claimed.
