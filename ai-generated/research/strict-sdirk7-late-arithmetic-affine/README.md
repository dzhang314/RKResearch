# Arithmetic suffix with the first active clock one

This is the reflection-breaking arithmetic branch of the
[late-third-ghost chart](../strict-sdirk7-late-ghost/README.md):
slots \(1,2,6\) carry zero output weight, and the six active
reflected clocks are distinct. The sixth ghost clock is
distinct from the active clocks. In normalized time the
first active forward clock is one, so its reflected clock
is \(a=z-1\). Neither the earlier first-three-ghost chart
nor the reflection suffix is imposed.

- A new native \(\mathbb F_{19}\) control has this entire
  architecture, including the affine helper and a genuinely
  arithmetic terminal block. All 85 order-seven trees pass;
  the eighth bush has residual 8.
- Over \(\mathbb Q\) the two linear hull equations have **no
  singular Cramer cases**. The ghost pin and actual affine
  helper pivot also cannot be singular. The reduced rational
  test consists of one primitive bidegree-\((17,12)\) equation
  and a quadratic-hull square test, followed by chronological
  assembly checks.
- Seven fixed-\(u\) slices and five variable-\(u\) cuts are
  exactly excluded, without a height restriction. These
  include the natural added reflection pair, the line through
  the finite control, and zero or centered forward ghost cuts.
  The general rational curve remains open. No rational
  nine-stage tableau was found.

## Ghost and terminal linear moment

Write \(u,v,1\) for the actual last three reflected clocks,
\(v=2u-1\), and
\[
 M=u^2-4u+2,\quad T=u^3-7u^2+10u-2,\quad
 R=4u^3-24u^2+39u-17.
\]
Use the prior raw slot-six four-row read. At the arithmetic
suffix its scaled ghost condition simplifies exactly to
\(4(J-Eh)=0\), where
\[
 \begin{split}
 E(u)&=u^5-11u^4+42u^3-62u^2+34u-6,\\
 J(u)&=5u^5-46u^4+148u^3-191u^2+90u-12 .
 \end{split}
\]
The projective test modulo five makes \(E\) nonzero over
\(\mathbb Q\), so \(h=J/E\).
At \(u=2,3\) the resulting \(h\) aliases an active terminal
clock, and \(u=1\) is an active collision. These exclusions
are within the distinct-ghost chart. The last three second
reverse ratios in order \(1,u,v\) are
\(-1/2,M/2,MR/(2T)\).

Let \(L=(X-a)(X^2-sX+p)\), \(I_j=I(X^j L)\),
\(I(X^j)=z^j/(j+1)\). The condition that the three
\(W(y)=(y-h)(D_y/\beta_y)K_y\) terminal values lie on
one affine graph simplifies to
\[
 S_0 I_0+S_1 I_1+S_2 I_2=0 ,
 \quad
 \begin{cases}
 S_0=(u-2)(2u^4-11u^3+11u^2+6u-6),\\
 S_1=-(2u^5-12u^4-u^3+105u^2-178u+78),\\
 S_2=3(u-3)(u-1)(u^2-6u+7).
 \end{cases}
\]
The common factor canceled in the raw affine test scaled
by \(2TE\) is \(2T(u-1)^3M\); the identity is native.
Both \(M,T\) are projectively rootless modulo three, and
\(u-1\) is an actual distinct-site gap.

Set \(R_4=(X-a)(X-1)(X-u)(X-v)\), \(S(X)=S_0+S_1X+S_2X^2\),
and
\[
 A_j=I(X^j R_4),\qquad B_j=I\bigl(X^j(X-a)S(X)\bigr).
\]
The paid quadrature and the terminal affine condition are
\(A_2-sA_1+pA_0=0\) and \(B_2-sB_1+pB_0=0\).
Let \(D=A_1B_0-A_0B_1\) and
\(N_s=A_2B_0-A_0B_2,\ N_p=A_2B_1-A_1B_2\).
The native scalar Cramer lemma shows that if \(D=0\) for
an actual solution, both numerators vanish.

[check-arithmetic-affine.py](check-arithmetic-affine.py)
removes the evident \(z^2,z^3,z^4\) from \(D,N_s,N_p\)
respectively after scaling \(I\) by 420.
It computes the two \(z\)-resultants with the pivot and
takes their gcd in \(u\). Its exact factor product contains
only \(u-1,u-3\), three quadratics rootless projectively
modulo \(3,5,3\), and a degree-thirty factor rootless
projectively modulo 17. The first two are forbidden clocks.
This applies even on specializations that lower the degree
of a resultant input: a literal common root still forces
each resultant to vanish. Thus \(D\ne0\) everywhere on
the actual rational chart and \(s=N_s/D,p=N_p/D\).

## Saturated intrinsic projection and affine tap

For these recovered coefficients put \(Q_2=X^2-sX+p\),
\(P=R_4Q_2\), and \(K_y=I(P(X)/(X-y))\).
Use the four-site cubic interpolating \(W(y)^2/K_y\)
on the fixed sites \(a,v,u,1\), and the
[two-by-two remainder criterion](../strict-sdirk7-arithmetic-suffix/README.md)
for the weighted isotropy of \(W/K\).
The fraction-free script uses \(D Q_2\), a common
terminal Vandermonde scale, and the product of the four
fixed \(K_y\)'s; both remainder columns are computed
with multiplication by amounts that are powers of \(D\).
The intrinsic polynomial remains after canceling only
nonzero chart scales: \(z\), suffix gaps, \(M,T,E,D\),
nonzero \(K_y\)'s, distinct-site evaluations \(Q_2(y)\),
the nonzero quadratic discriminant, and \(W(h)\ne0\).
Not all listed scales actually divide the eliminant.
The final exact integer polynomial \(H(u,z)\) has
bidegree \((17,12)\) and 231 terms, in
[projected-curve.json](projected-curve.json).
On the distinct active, nonzero-pivot chart its vanishing
is equivalent to the isotropy determinant. In particular
the four extra octics in a generic fixed-\(u\) raw
projection are collision factors, not further solutions.

For a rational candidate \((u,z)\) on this curve, check
\(s^2-4p\) is a nonzero rational square and recover
the two early roots in either physically admissible
ordering. At the first forward clock one the second
forward read recovers \(t\) as in the previous
late-ghost affine-helper formula. In this chart the
nominal tap pole is never compatible over \(\mathbb Q\):
a zero denominator together with the same read gives
\[
 3U(x_b)+2V(x_b)=(x_b-1)(x_b^2-4x_b+1)=0.
\]
Here \(x_b=1\) is an active collision, and the other
possibility would make 3 a rational square. This
nonzero-pivot claim is native. The remaining
chronological minor, nonzero weights, and chosen
eighth-tree exactness must still be checked for
any proposed rational tableau. No such candidate
was found in this packet.

## Exact rational exclusions

The following are consequences of \(H\) and the preceding
global pivot proof, not bounded scans. For each univariate
polynomial the replay checks all residues and the leading
coefficient modulo its indicated prime, so coordinates with
a nonunit denominator are also covered.

- \(u=-1,0,4,5,7,9,11\), with \(z\) arbitrary, are
  excluded respectively modulo \(43,31,43,17,47,31,41\).
- \(z=3u-1\) adds a reflection pair between \(u\) and \(v\)
  and completes a four-term arithmetic grid with \(a\).
  Its degree-27 specialization is projectively rootless
  modulo 29.
- \(z=3-u\) is the other four-grid endpoint, with
  \(a=2-u\); degree 27, modulo 31.
- \(z=2u-5\), the literal line through the finite
  control, is excluded at degree 27 modulo 41.
- \(z=h(u)\) gives normalized ghost clock zero;
  \(z=2h(u)\) centers the ghost. After clearing the
  nonzero \(E^{12}\), their degree-77 specializations
  are projectively rootless modulo 23 and 11.

The optional bounded diagnostic checks all rational \(z\)
for every reduced \(u\) of the chosen height, first using
projective modular sieves and then exact linear factors.
At height 400 there were 194,708 eligible \(u\)'s and 54
surviving specializations to factor, with no rational
projected pair. This is not a proof outside the stated
height or a global rational obstruction.

## A separate nondegenerate finite control

The actual [literal tableau](f19-arithmetic-affine.json)
has
\[
 (z,u,v,h,a,b_*,c,t)=(13,9,17,3,12,5,18,8)\pmod {19},
\]
common diagonal 3 and output mask \(1,2,6\).
The first active forward clock is one and its cubic
defect is nonzero. Its suffix is not reflection.
The eighth bush has payment 9, residual 8.

With \(a=z-1\) imposed, the four scalar equations from
the earlier late-ghost construction have an invertible
Jacobian in \((z,b_*,c,t)\) at fixed \(u\): determinant
10 modulo 19. The two-profile forward determinant is
12, the last-four reverse minor 4, the ghost error 1,
and \(V_a=1\). This ensures a genuine unit-pivot local
chart, not a degenerate appearance of \(H\) at the
finite point. The independent arithmetic replay checks
these numbers, all 85 trees, and the eighth bush.
This note does not infer a rational lift from the
finite or local calculation.

## Replay

    python3 check-arithmetic-affine.py --rebuild
    python3 check-arithmetic-affine.py --height 400
    python3 check-control.py

The first two scripts use SymPy 1.14.0 and python-flint
0.8.0, and the literal/Jacobian check uses the standard
library. No floating-point factorization is used.
Build
[SDIRKSevenLateArithmeticAffine.lean](../../lean/RKCert/Research/SDIRKSevenLateArithmeticAffine.lean)
and
[SDIRKSevenLateArithmeticAffineF19.lean](../../lean/RKCert/Research/SDIRKSevenLateArithmeticAffineF19.lean),
then run [proof-audit.lean](proof-audit.lean).
Both modules are checked in stock Lean 4.36.0.
The Cramer resultants, the core projection and their
rootlessness tests are mathematical consequences with
exact arithmetic replay, separate from the native
scalar gates and literal tableau.
