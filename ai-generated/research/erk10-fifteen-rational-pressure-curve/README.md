# The exceptional width-15 pressure curve: simplification and rational cuts

This concerns the precise five scalar geometry equations in
[the 17-power ERK10 construction](../erk10-fifteen-17-power/README.md).
There is a \(17\)-adic point, so the equations are not inconsistent
over all fields. Here are an exact simpler elimination and three
rational subcase obstructions. They do not decide the rational
points on the remaining regular curve or the existence of an
arbitrary 15-stage rational tableau.

The later [guarded two-pair closure](../erk10-fifteen-two-pair-rational-closure/README.md)
forces the zero-donor branch for both actual tableau heads.

## Equivalent simplified scalar geometry

Use all labels \(0,1,a,b=2a,c,d,e,f,g\) distinct, and
nonzero cardinal integrals where required by the constructed
reverse chart. Set
\[
  V(Y)=(Y-f)(Y-g)=Y^2+mY+n,\quad
  U(Y)=(Y-1)V(Y),\quad \nu(Y)=(Y-e)U(Y),
\]
and \(M(Y)=Y^2(Y-b)^2,\ G(Y)=Y(Y-a)(Y-b)(Y-c)\).
The formal primitive from 0 is \(J\), and \(I\) is integral
from 0 to 1. In the notation of the lifted construction,
\(E_4=\nu,\ E_3=-U,\ Q=JM/4\).
The scalar nodal identity and the early \(c\)-site identity
are exactly \(I(\nu(Y-d)G)=I(\nu(Y-d)M)=0\):
indeed
\[
 M-G=Y(Y-b)((c-a)Y-ac)
\]
and the early cardinal integral
\(c(c-b)\mu_c+a^2\mu_a\) is
\((c-a)I(\nu(Y-d)(M-G))\). Distinctness pays \(c-a\).
The two blind tests are \(I(\nu JG)=I(\nu JM)=0\).

Using these nodal and early equations further simplifies the
first extra donor numerator. Put \(G_1=Y(Y-a)(Y-b)\).
Then \(\mu_c=I(\nu(Y-d)G_1)\) and
\(\mu_d=I(\nu(Y-c)G_1)=I(\nu G)\).
Using the early equation,
\[
 Z_d^*=d(d-b)\big[c(c-b)\mu_c-d(d-b)\mu_d\big].
\]
The bracket is
\((c-d)I(\nu G_1[(c+d-b)Y-cd])\).
The nodal \(G\)-equation makes this integral
\(I(\nu G_1 Y(Y-b))=I(\nu M(Y-a))\).
The nodal \(M\)-equation replaces \(Y-a\) by \(d-a\)
in that integral, so
\[
                         Z_d^*=-G(d)I(\nu M).
\]
As \(G(d)\ne0\), the fifth equation is now
\[
            I(\nu G) I(U JM)-I(\nu M)I(U JG)=0 .
\]
Thus the two time parameters \(c,d\) only occur linearly
in the moment rows that solve for them.

To eliminate them without dropping degeneracies, let
\(G_0=YG_1\), so \(G=G_0-cG_1\), and
\(j_i=I(\nu JG_i)\) for \(i=0,1\).
Use \(j_1 c=j_0\).
For \(F\in\{G_0,G_1,M\}\) form the three scalar readouts
\(V(F)=I(\nu F),\ T(F)=I(\nu YF),\ R(F)=I(U JF)\).
In each read use the signed combination
\(F^\star=j_1G_0-j_0G_1\), without dividing by \(j_1\).
The two exact necessary pressures are
\[
 V(F^\star)T(M)-V(M)T(F^\star)=0,\qquad
 V(F^\star)R(M)-V(M)R(F^\star)=0 .
\]
The first cancels \(d\), the second is the simplified
fifth equation. If \(j_1=0\), these are still necessary;
one must also retain the actual equation \(j_1 c=j_0\).

Write \(D\) for the coefficient of \(n\) in \(I(\nu JM)\).
On \(D\ne0\), solving the latter equation linearly for \(n\)
leaves two cubics in \(m\). Their exact resultant in \(m\),
after removing the forbidden \(a=0\) factors in the rows,
has factors of bidegree \((2,1),(3,3),(6,3),(24,12)\)
in \(a,e\). This is an exact elimination target, not a claim
that all four factors support solutions. The conditions for
actual \(c,d\), both rational roots of \(V\), and the equation
denominators remain required.

## Three exact rational exclusions

**The distinguished last-three row \(e=1/2\).**
Here \(D\) is proportional to \(-28a^2+18a-3\),
whose discriminant is \(-12\); thus the chosen blind pivot
does not vanish for rational \(a\).
The resultant of the two exact cubics above has only one
nonzero rational base root, \(a=1/6\).
The other nonlinear factors are projectively rootless modulo
the primes recorded in the [exact replay](exact-audit.txt).
At \(a=1/6\), their only rational common \(m\) is
\(-67/40\) and \(n=7/10\). In fact the tail roots \(4/5\)
and \(7/8\) are rational, but the actual degree-four blind
equation is \(0\cdot c=-1/345600\), impossible. No extension
of the denominator chart is being assumed at this slice.

**The alternate blind pivot \(D=0\).**
In this chart \(e=(112a^2-60a+9)/(12(14a^2-7a+1))\).
The quadratic denominator is nonzero over \(\mathbb Q\).
Now \(I(\nu JM)\) determines \(m\) instead of \(n\):
its coefficient of \(m\) has the quartic numerator
\[
                  B(a)=896a^4-840a^3+300a^2-48a+3 ,
\]
which has no projective root mod 19. Thus no rational
linear pivot is missed here. The same two pressures give
cubics in \(n\); their resultant has only nonzero rational
base root \(a=1/4\), by the exact projective factor checks.
At that root the only candidate is \(e=2/3,\ m=-6/5,\ n=2/5\).
The tail quadratic discriminant is \(-4/25\), so there
are no two rational final ordinates in this alternative chart.
No nonzero \(j_1\) was assumed to exclude this point.

**Zero first additional donor response \(Z_d=0\).**
This is an interesting near-residue choice since it occurs in
the base finite-field witness, but not on the rational curve.
Since \(G(d)\) and \(\mu_d\) are nonzero, the exact formula
for \(Z_d^*\) gives \(I(\nu M)=0\), and the nodal equation
then gives \(I(\nu YM)=0\).
The fifth equation and \(I(\nu JM)=0\) now give
\[
                         I(U JM)=I(YU JM)=0 .
\]
These are two linear equations in the two coefficients of
\(V\); their determinant is \(-B(a)/6350400\) up to the
specified column order. It is nonzero for rational \(a\).
After the exact two-by-two solve, set \(s_i=I(UY^iM)\).
The first two \(M\)-equations mean \(s_1=e s_0,\ s_2=e s_1\),
so \(s_0s_2-s_1^2=0\) without any division by \(s_0\).
The replay factors this as \(-a^2 N(a)/(39690000 B(a)^2)\),
where the explicit degree-nine numerator \(N\) has nonzero
leading coefficient and no affine root modulo 11.
This projective certificate excludes every rational \(a\)
(including with 11 in the denominator); \(a=0\) is forbidden.

## Reproduce

    python3 -B audit.py --all
    sha256sum -c sha256.txt

The script independently integrates, eliminates, checks the full
listed factor sets by projective congruences, and verifies the
remaining singular pivots. Its optional full resultant prints
only the factor bidegrees. The portable Lean Core module checks
the two projective root exclusions for \(B,N\) on all four
releases. The elimination/chronology bridge and other resultant
factor computations are exact mathematical audits, not a native
all-tableau no-rational theorem.
