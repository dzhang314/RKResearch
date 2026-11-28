# No constant ghost cubic in the normalized invisible six-clock DIRK11/13 chart

**Result.** The entire constant-\(U\) no-late-ghost subcase of normalized
invisible \(r=0,d=z_{\mathrm{count}}=6\) DIRK11 on thirteen physical stages
is impossible. The [forward mask](../dirk11-thirteen-invisible-six-prefix/README.md)
excludes \(\alpha=0\); this proof excludes the remaining \(\alpha=1,2\)
together, irrespective of \(\beta,\gamma\). It does not exclude additional
count profiles for *nonconstant* \(U\). The unrestricted real interval
stays **13–14**.

The actual rooted normal form is the same as in the preceding packets:
literal lower triangle, order 11, forward \(C(2)\), genuine reflected
\(D(1),D(2)\), grade-six surplus, and the signed invisible-six skeleton.
There are six unweighted ghosts at distinct dirty clocks, with genuine
forward cubic \(g\) identically one nonzero scalar \(U\) on them. Seven
distinct clean sites include the literal endpoints, and the ordinary
non-endpoint weights are live. Once the signed skeleton and true paid
ranks are obtained, this proof applies over every characteristic-zero
field. No ordering or real specialization is used.

## 1. Actual grade-seven head and two forward clean samples

Let \(E_j,F_j\) be the actual tree and zero-profile spaces and
\(C=\operatorname{diag}(c)\). The clean-supported \(\phi=U-g\) has grade
three. Write \(H_T(X)=30b_T X J_4(X)\) for the true terminal profile.
In this section \(b,a\) denote the first two nonorigin clean **forward**
clocks in chronological order. By the no-late cut, no ghost has an
earlier positive-power clean forward donor outside \(b,a\).

The true grade-seven zero-profile space is
\[
 F_7=g\mathcal P_4(c)+(e_T-H_T(c))\mathcal P_1(c).
\]
The five \(g\)-polynomial columns are independent on the six distinct dirty
labels. The other two columns are genuine by multiplication by \(c\)
from \(F_6\) and independent modulo the first five: \(H_T\) is nonzero
at the five distinct non-endpoint clean sites by the established
clean barycentric identity and \(J_4(1-s)=J_4(s)\). For the upper
dimension, all \(F_7\) vanish at the true origin and annihilate the
four paid ordinary probes \(b_i c_i^k,\ k=0,1,2,3\). These five
functionals on \(E_7\) are independent: test a putative dependence
on \(X\mathcal P_3(c)\), where the rational Gram matrix for weight
\(X\) is positive definite over the reals, hence has nonzero rational
determinant in any characteristic-zero coefficient field. Then
test 1 to remove the origin coefficient. Since \(\dim E_7=12\),
this proves the exact dimension seven.

Take the actual grade-six input \(\psi=C(C-a)(C-b)\phi\). It is zero
at every ghost, the origin, and \(a,b\). Thus \(A\psi\) vanishes at
every ghost and at \(a,b\) by the inclusive DIRK cut. The actual
masked-primitive budget gives \(A\psi-F(c)\in F_7\), where
\(F=U I[X(X-a)(X-b)]\), and \(I\) is the formal zero-constant primitive.
Let \(S_6\) be the monic hull of the six nonterminal clean forward
labels, and \(S\) their sum. In the true
\(E_6=\mathcal P_5+g\mathcal P_3+K e_T\) decomposition of \(S_6(c)\),
the polynomial piece vanishes by the six clean zeros. Consequently
the ghost hull is \(R_6=S_6-UQ_3\) with \(\deg Q_3\le3\).

Write the \(F_7\) affine terminal-head coefficient of \(A\psi-F(c)\)
as \(L=l_0+l_1X\). Since \(A\psi=0\) on all six ghosts,
\(F+UQ_4-H_T L\) is a scalar multiple of \(R_6\).
The terms \(F,UQ_4\) have degree at most four. Substitute the
six-ghost hull and compare degrees six and five, using the
two top coefficients \(h_5,-2h_5\) of \(H_T\), with \(h_5\ne0\).
This gives \(l_0=(2-S)l_1\), i.e. \(L=l_1(X-\xi)\), \(\xi=S-2\).
The comparison allows \(l_1=0\). At \(a,b\) the exact samples
are \(F(a)=H_T(a)L(a)\) and \(F(b)=H_T(b)L(b)\).

## 2. Symmetric pair and exact rank-144 clock reconstruction

The five non-endpoint forward labels are roots of the ordinary
Jacobi pencil \(J_5+\lambda J_4\), with
\[
 \begin{split}
 J_3(X)&=(2X-1)(7X^2-7X+1),\\
 J_4(X)&=42X^4-84X^3+56X^2-14X+1,\\
 J_5(X)&=(2X-1)(66X^4-132X^3+84X^2-18X+1).
 \end{split}
\]
Including the zero origin does not change their sum
\(S=5/2-7\lambda/22\). The exact recurrence
\(7J_5=22(X-1/2)J_4-4J_3\) gives
\((x-\xi)J_4(x)=(2/11)J_3(x)\) at each pencil root.
This replacement makes no division by \(x-\xi\), \(J_3(x)\),
or \(J_4(x)\): their possible common zeros at that gate are
retained. Likewise \(F(a)=U a^3(2b-a)/12\),
\(F(b)=U b^3(2a-b)/12\); neither \(2b-a\) nor \(2a-b\) is
divided by. Cross-multiply the two head equations.

With \(S_2=a+b,\ P_2=ab\), the following two exact symmetric
polynomials must vanish:
\[
 \begin{split}
 F_{\rm pair}(S_2,P_2)&=
 \frac{J_5(a)J_4(b)-J_5(b)J_4(a)}{a-b},\\
 G_{\rm pair}(S_2,P_2)&=
 \frac{a^2(2b-a)J_3(b)-b^2(2a-b)J_3(a)}{a-b}\\
 &=-28P_2^2 S_2+63P_2^2-9P_2 S_2-3P_2+S_2^2 .
 \end{split}
\]
Only \(U,a,b,a-b\) and paid rational constants were canceled;
the two clean clocks are distinct from either endpoint.
The source expands the polynomial identities before elimination.
As polynomials in \(P_2\), \(F_{\rm pair}\) has degree four
with fixed leading coefficient \(5544\); \(G_{\rm pair}\) has
degree two unless \(S_2=9/4\). Their resultant has primitive
degree twelve in \(S_2\). Its exact evaluation at \(9/4\) is
nonzero, guarding that possible degree change. The leader of
the linear subresultant is a unit in the entire degree-twelve
quotient, so it recovers \(P_2\). No irreducibility assumption
is needed.

The finite-free reconstruction over \(\mathbb Z_{(101)}\) is:

1. Normalize the primitive degree-twelve resultant to monic
   by its checked unit leader and adjoin \(S_2\). Recover
   \(P_2\) by the unit-guarded linear subresultant.
2. Adjoin \(a\) by the monic \(X^2-S_2X+P_2\), preserving both
   physical orders, and put \(b=S_2-a\). Obtain
   \(\lambda=-J_5(a)/J_4(a)\) by its checked unit guard.
   Normalize the quintic by 132 and synthetically deflate
   by \(a,b\) for the remaining monic cubic.
3. Adjoin the forward form of the first reverse ordinary
   clock \(v\) by that cubic, deflate, and adjoin the forward
   form of \(u\) by the monic quadratic. The third root is
   obtained by the sum of cubic roots. Reflect all three.

This constructs ranks \(12,24,72,144\) and retains all orders.
The monic coefficient deflations specialize to legitimate
deflations at any candidate because the actual sites are roots.
The proof does not require that all formal quotient points are
realized.

## 3. Genuine first-ghost obstruction, not a repeated clock guess

Let \(N=A^\mathsf{T}\) in literal reverse chronology, \(Y\) the
reflected diagonal, and \(G=NW(X^2)-W(X^3/3)\) the genuine
cubic, \(W(P)=bP(y)\). Since the constant-\(U\), \(\alpha=0\)
branch is separately impossible, take the **first literal
ghost** after the clean \(w\), before the next clean row.
Its clock \(z\) is unknown, \(G_z\ne0\), and its only possible
nonzero weighted positive-power donors are \(v,u,w\).

The reciprocal clean head supplies \(k_s=G_s/b_s=
h(s)v^3/(6h(v))\), \(h(s)=sJ_4(s)\), the scale fixed by the
actual \(G_v/b_v=v^3/6\). The genuine paid profiles
\[
 G_4=L_1(Y)G,\quad NG=\Lambda(Y)G,\quad
 G_5=Q_2(Y)G,\quad N(YG)=M_2(Y)G
\]
have degrees at most \(1,1,2,2\) since they annihilate
\(E_6,E_6,E_5,E_5\). Fit the affine profiles at the actual
\(v,u\), the quadratic ones at \(v,u,w\). The ordinary taps
at \(u\) are fixed by scalar powers 1 and 2; at \(w\) use
1 through 3, with targets \(s^2/2,\ s^3/3+k_s,\
s^4/4+L_1(s)k_s\). The other fits are the actual fourth-power
and marked reads on these solved taps. The ordinary-clock,
clock-difference, weight-normalization and Jacobi denominators
used by this read system are units in the replay.

At the first ghost normalize the three weighted taps by
\(G_z\), not its zero weight. Their first three moments are
\(0,1,L_1(z)\); hence these taps \(T_r(z)\) are affine in \(z\).
The actual fourth moment and the read of \(N(YG)-zNG\) give
two quadratics or lower:
\[
 \sum_r r^4T_r(z)-Q_2(z)=0,\qquad
 \sum_r(r-z)k_rT_r(z)-M_2(z)+z\Lambda(z)=0 .
\]
There is no earlier ghost, and the ghost's own contribution
to the second mark cancels regardless of its diagonal.
This divides by no difference involving \(z\), and allows
numeric ghost-clean coincidences. A common finite root forces
the cleared Sylvester determinant to vanish even when a
quadratic leading coefficient vanishes.

That determinant is a unit throughout the complete rank-144
quotient modulo 101. This is the **new independent obstruction**:
the earlier third-clean condition only gave a finite set and
is not used as a contradiction here. The replay computes
inverse certificates at each level, using Euclidean inversion
for the rank-twelve residue algebra and the adjugate of the
degree-two or degree-three multiplication matrix at successive
levels. It multiplies every distinct residue inverse back to
one and caches it within its ring. The total of 75 counts
the base scalars, all nonrepeated recursive norm inverses, and
the final determinant inverse; it is not a candidate count.

Unit lifting is purely in the clock algebra: over
\(\mathbb Z_{(101)}\), a multiplication operator whose reduction
is invertible has unit determinant and an inverse by its
adjugate. Apply this to each guard before the ensuing monic
adjunction, and to the final Sylvester determinant. Any
characteristic-zero candidate supplies an evaluation
homomorphism from these prescribed clock algebras, where the
final unit would have to vanish. No step reduces any unknown
tableau, ghost clock, or weight modulo 101.

## Reproduction and Lean scope

Run \(\texttt{python3 replay.py}\) with SymPy for the exact
resultant and unit tests. Other good reductions can be checked with
\(\texttt{--prime 109}\) or \(\texttt{--prime 127}\). The companion
Lean module verifies the affine head comparison, Jacobi recurrence,
both symmetric pair identities and the guarded pair implication.
The reviewed quadratic Sylvester implication and actual
masked-primitive budget are separate native modules. The full
finite coefficient and true F7 chronology argument above is
an exact source proof, not an end-to-end Lean endpoint theorem.
