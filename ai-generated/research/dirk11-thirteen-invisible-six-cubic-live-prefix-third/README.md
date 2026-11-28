# Actual prefix inverses, a third-gap locator, and divided fixed-clock tests for DIRK11/13

**Result.** Within the normalized invisible-six cubic
DIRK11/13 chart with \(\alpha=0,\tau\ne0\), the five-prefix
carrier equation has an actual affine inverse and a live
location pivot; the four-prefix case has a separate
coefficient gate. With three reverse-gap ghosts, the true
quintic crossing determines the third ghost and the paired
commutator determines its diagonal. Polynomial divided
differences of the two earlier crossings exclude the
additional whole local ordinary-clock class \(B\equiv4
\bmod29\) even when \(z,w\) coincide after reduction.
The unrestricted real interval stays **13–14**; no global
closure of the remaining regular clock set is claimed.

Use the actual rooted-order, chronology and signed-rank
hypotheses of the [live fourth-clean](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md)
and [fixed-gap](../dirk11-thirteen-invisible-six-cubic-live-fixed-gap/README.md)
proofs, and the [only-\(F_3\)](../dirk11-thirteen-invisible-six-cubic-live-f3/README.md)
ordinary reconstruction. In particular \(U\) is cubic and
live at all nonterminal clean sites and all six ghosts,
and \(A_{aa}=0\). Write \(B,V\) for the fifth/fourth regular
reverse clocks, \(R_3\) for the old regular triple hull,
\(X=1-Y\), and \(I\) for the zero-constant primitive.
Write \(U_{\rm rev}\) for any fixed nonzero multiple of
\(U(1-Y)\), and \(S_6,R_6\) for the forward monic hulls of the
six nonterminal clean and the six dirty clocks, respectively.
All field arguments hold over characteristic zero once the
genuine ranked hypotheses have been established.

## 1. The two live monic hull multipliers

The true \(E_6\) decomposition of \(S_6(c)\) gives a single
polynomial \(Q_3\) of degree at most three such that
\[
 S_6-UQ_3=\omega R_6 .
\]
Indeed the pure degree-five component vanishes at the six
nonterminal clean sites and is zero; at the ghosts \(g=U\)
in the chosen scale, giving the six distinct zeros.
Degree at most six and monicity of \(R_6\) give the displayed
identity for some scalar \(\omega\). This scalar is nonzero:
otherwise \(U\mid S_6\) despite \(U\) being live at every
one of the distinct roots of the split \(S_6\).
It also follows that \(S_6\) is a unit in \(K[X]/U\).

Let \(\phi=U(c)-g\) be the true grade-three clean mask.
Through every initial forward ghost before \(b\),
\(A(C\phi)=0\) by the inclusive DIRK cut: the only
available clean coordinate is the origin with clock zero
and every ghost has zero \(\phi\). The grade-five paid
error is \(g\mathcal P_2\); hence the polynomial
\[
 T=I(XU)+UQ_2
\]
vanishes at all \(\gamma\) initial ghost clocks for one
quadratic-or-lower \(Q_2\). It cannot be identically zero.
As \(U(0)\ne0\), an identity \(U\mid I(XU)\) would give
a quotient of degree and valuation both two; the coefficients
from the constant and leading terms of \(U\) would then
require simultaneously \(1/2\) and \(1/5\).

When \(\gamma=5\), \(T=\eta R_5\) for the monic initial
hull \(R_5\) and a nonzero \(\eta\), by degree and root count.
Let \(\xi\) be the one other forward ghost. With
\(J=I(XU)\bmod U\), multiplication by \(X-\xi\) and
reduction modulo \(U\) give
\[
 (X-\xi)J=(\eta/\omega)S_6 \quad\text{in }K[X]/U.
\]
**Both** scalar monic hull multipliers \(\eta,\omega\)
are live by the preceding actual-row arguments. The
right side is a unit, so \(J\) and \(X-\xi\) are units
over this commutative quotient algebra. Hence
\[
 T_{\rm inv}=S_6/J=(\omega/\eta)(X-\xi)
\]
has degree one in its cubic quotient basis and a live
linear coefficient. Equivalently let
\(Q=\operatorname{adj}(M_J)S_6\), where \(M_J\) multiplies
by \(J\) in the cubic carrier quotient. Its degree-two
coefficient is zero, its linear coefficient \(Q_1\ne0\),
and the necessary cleared location is
\(\xi Q_1+Q_0=0\).
The first reverse gap clock \(z=1-\xi\) therefore
satisfies \(zQ_1=Q_1+Q_0\). The first-gap cubic can be
evaluated homogeneously at this location without ever
inverting a numerical residue. This is a smaller
actual-profile version of the previous three
coefficient-minor location identities.

When \(\gamma=4\), the same nonzero \(T\) is the
monic initial four-ghost hull times a polynomial
\(L\) of degree at most one. If \(\xi_1,\xi_2\)
are the two other forward ghost clocks, then
multiplication by their true monic pair and the
live \(\omega\) give
\[
 \left[X^2\right]\left(
     (X-\xi_1)(X-\xi_2) J/S_6\bmod U\right)=0 .
\]
This is a genuinely paid extra coefficient test;
it needs only the clean-hull inverse, not the
five-prefix inverse of \(J\). It can also be evaluated
using the polynomial adjugate of multiplication by
\(S_6\).

## 2. The actual third gap clock and its diagonal

Suppose three ghosts lie between \(V\) and \(B\)
in reverse order, with distinct clocks \(z,w,u\).
Let \(q_z(Y)=r_1^*(Y)-z r_0^*(Y)\) for the earlier
true corrected fits. By the fixed-gap proof
\(d_w=0\), and the quadratic coefficient \(c\) of
\(q_z\) is genuinely nonzero. Thus
\(q_z(Y)=c(Y-z)(Y-w)\).

The genuine quintic weighted input
\(P_5=(Y-V)Y R_3=YQ_4\), with \(Q_4=(Y-V)R_3\),
gives the effective clean cubic \(Q_{\rm eff}\)
by the four live samples \(IP_5/k\).
All three ghosts are roots of
\[
 S(Y)=U_{\rm rev}(z)Q_{\rm eff}(Y)-Q_{\rm eff}(z)U_{\rm rev}(Y).
\]
To show this is not the zero polynomial, use the true ordinary
Jacobi pencil. The \(Y^3\) coefficient of
\[
 I(YQ_4)/(YJ_4)\pmod {Q_4}
\]
is exactly \((B-1)^2/(6J_4(B))\), as checked by
`check-quintic.py`. The polynomial factors \(Y\)
are canceled as polynomials, not as numerical clock inverses.
The inverse of \(J_4\) uses its rational Bézout relation
with \(J_5\) at the true pencil; all coefficient
denominators divide a power of the live \(J_4(B)\).
The displayed coefficient is live because the ordinary
\(B\ne1\). If \(S\) were identically zero, \(Q_{\rm eff}\)
would be proportional to \(U_{\rm rev}\), since the
actual ghost \(U_{\rm rev}(z)\ne0\). At the four
ordinary sites the exact reciprocal relation would then
make \(IP_5/(YJ_4)\) constant, contradicting the live
cubic coefficient. Therefore \(S\) is nonzero, and with
three distinct roots it has full degree three.
Its Vieta third location gives
\[
 S_3 u=-S_2-(z+w) S_3 ,
\]
with actual \(S_3\ne0\). This gives no further
ghost adjunction once the first two are determined.

Let \(M\) be the actual transpose tap matrix on this
gap block, conjugated entrywise by the live \(G\)
coordinates. Then \(M1=r_0^*(Y),MY=r_1^*(Y)\).
The earlier paired commutator kills the input \(Y-z\)
on the whole gap, and its \(M\)-image equals \(q_z\),
with first two coordinates zero. Put \(d=d_u\) and let
\(e=M_{u,w}\) be the third row's normalized tap to \(w\).
At the third row the true \(M\) and paired commutator
equations are
\[
 (w-z)e+(u-z)d=q_z(u),\qquad
 (u-w)(w-z)e=d\,q_z(u).
\]
Eliminate \(e\); since \(u-z,u-w\ne0\), this yields
\[
 (1+c)d=c(u-w),\qquad
 (1+c)(w-z)e=c^2(u-z)(u-w).
\]
In particular \(1+c,d\ne0\) in an actual case.
These are true literal third-row consequences, with
no unknown third tap left after division of the live
coefficients.

For a further fixed-clock test, put
\(A_x=r_0^*(x), B_x=r_1^*(x)\), \(d_z=A_z\), and
\(D=(w-z)(1+c)\).
Retaining the unmarked commutator at \(u\) gives
\[
\begin{split}
0={}&U_{\rm rev}(z)\bigl[
 D(-u A_u+B_u+d_z A_u)
 +c^2(u-z)(u-w)(A_w-d_z)\\
 &\hspace{42mm}+(w-z)c(u-w)(A_u-d_z)\bigr]
 -U_{\rm rev}(u)d_z^2D .
\end{split}
\]
Indeed \(M r_0^*(u)=A_ud_z+e(A_w-d_z)+d(A_u-d_z)\),
while the same retained row at \(z\) gives the
carrier multiplier \(d_z^2/U_{\rm rev}(z)\).
Multiply by \(D\) and substitute the two exact
third-row reads. This is at most cubic in \(u\);
its Vieta location can be substituted homogeneously,
maintaining every zero specialized residue pivot.

## 3. Divided crossing tests preserve distinct actual ghosts

In either two-gap or three-gap chronology the actual first
two ghost clocks satisfy \(w-z\ne0\), but their residues
may coincide. For any polynomial \(F\), use the
polynomial divided difference
\[
 [F]_1(z,w)=\sum_{i\ge1}F_i
                  \sum_{j=0}^{i-1}w^{i-1-j}z^j,
\]
so \(F(w)-F(z)=(w-z)[F]_1(z,w)\) identically.
Let \(d_z=r_0^*(z)\).
Both the old quintic crossing and the retained
unmarked commutator are multiples of \(w-z\).
Cancel that factor **only as an actual characteristic-zero
polynomial equality**, and preserve their necessary divided
versions
\[
 U_{\rm rev}(z)[Q_{\rm eff}]_1-
        Q_{\rm eff}(z)[U_{\rm rev}]_1=0,
\qquad
 U_{\rm rev}(z)r_0^*(w)-U_{\rm rev}(z)d_z[r_0^*]_1+
        d_z^2[U_{\rm rev}]_1=0.
\]
Both formulas are evaluable at \(z=w\) after reduction:
no numerical division by \(w-z\) is used.

At \(B\equiv4\bmod29\) the full ordinary-to-gap
monic tower has the verified live inversions of the
previous fixed-clock proof, in ranks 12 and 36.
The old undivided pair has a nonunit sum there,
but the sum of their two **divided** versions is a
unit of the entire rank-36 algebra. The five-prefix
case is independently excluded by the homogeneous
first-gap joint prefix unit in rank 12.
The replay checks both factor identities at residue
level as an arithmetic audit, then the joint units.
The monic-algebra lift over the localization of
\(\mathbb Z_{(29)}[B]\) at \((29,B-4)\)
gives the exact characteristic-zero local exclusion
for any \(B\) admitting this specialization.
No assumption of tableau integrality or distinct
residue ghosts is used.

Run `python3 check-quintic.py` for the exact
coefficient proof and `python3 replay.py` for
the finite-free local check. The four optional
sibling-source overrides are the same as in the
fixed-gap packet. The companion Lean checks the
unit prefix, denominator-cleared location, third
scalar taps and polynomial divided-difference
implications. Their genuine rooted ingress,
field normal form, and exact arithmetic transfer
are the separate source proof above.
