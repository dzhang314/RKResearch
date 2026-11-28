# Asymmetric half-at-9: both affine and vertical dropouts are impossible

**Scope.** Continue the [canonical h-at-9 asymmetric edge](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-FINITE.md):
left extras \(\{e,t\}\), right extras \(\{t,s\}\), and
genuine nine-site separation with physical \(c_8=z\) dormant,
\(c_9=h,c_{10}=s\). This proves that the actual affine
slope is live and that every retained width pair has at most
six dormant choices, with unique free labels at each candidate.
It applies to this edge order and its actual reflection over
characteristic zero. It is not a full exclusion of the regular
clock candidates.

## 1. The actual zero slope is excluded without using it

The paid middle equation is \(E(z)s=N(z)\), where
\[
                 E(z)=A_0z+C_0,\qquad N(z)=-(B_0z+D_0).
\]
A zero slope at the actual \(z\) forces both \(E=N=0\)
and \(A_0D_0-B_0C_0=0\). By the checked width identity
\[
   633719116800000(A_0D_0-B_0C_0)
             =-a^2b^2J_0R_{33},
\]
the actual widths satisfy \(J_0=0\) or \(R_{33}=0\).
This disjunction is unordered and permits both factors to
vanish. We do not divide by \(A_0,B_0,H,J_0,R_{33}\)
or either affine coefficient.

Use the genuine shifted \(\Delta,\Sigma,\Pi\) from the four
calibrations and the true \(z\), not the regular affine
reconstruction. The normalized right derivative row is
symmetric in its two free extras:
\[
                     R_0=d^2\Delta-d\Sigma+\Pi,\qquad
                     R_1=-\Delta+\Sigma-\Pi.
\]
The left derivative row depends affinely on \(t\).
Thus the [same first-contact norm and dormant port](ERK11-NINE-SITE-ASYMMETRIC-EDGE-DROPOUT.md)
give \(F=G=0\) irrespective of the position of \(h\) among
the two active rows. Likewise the
[actual support equation](ERK11-NINE-SITE-ASYMMETRIC-DORMANT-SUPPORT.md)
still gives the affine row in \(Y=\Delta t\);
its compatibility with the first contact and its quadratic
norm give \(S=T=0\), with exactly the definitions in the
[half-at-10 proof](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H10-EXIT.md).
Those definitions used only the underlying site sets or
physical row-8 port, not the inner active order.

There is also a mark specific to the actual half label \(h\)
at physical 9. The repeated left half contact gives
\[
 \sigma_h\langle D_h,\Phi_R\rangle_N+
   30P_9\langle\ell_a,\Phi_R\rangle_N=0,\qquad
 (V_L)_9=\sigma_h V_a(h),\quad P_9=(AV_L)_9 .
\]
The earlier half calibration has zero actual primitive and
the repeated live pair has distinct responses.
Products with \((C-z)V_L,A^\star V_R\) and with
\(AV_L,A^\star V_R\) isolate physical 9 and give
\(C_2-zH=b_9(h-z)(V_L)_9Q_9\) and \(J_0=b_9P_9Q_9\).
Multiply the actual repeat equation by
\(b_9(h-z)Q_9V_a(h)\) and extract only \(h(a-h)\).
The necessary mark is
\[
 L=a(C_2-zH)\bigl(R_0K_0(h)+R_1K_1(h)\bigr)
       +30h(a-h)(h-z)J_0\langle\ell_a,\Phi_R\rangle_N=0.
\]
This remains valid when a mixed primitive vanishes;
there is no division by \(P_9,Q_9\).

In the rational replay remove exact divisors only of the
basic live calibration, shifted pivots and distinct-clock
guards. In particular no removed factor assumes a nonzero
affine coefficient, determinant rank or \(J_0\).
Take the \(z\)-resultants of each of \(E,N\) with
\(G,L,F,S,T\). Those needed for the exact final test
have width bidegrees \((b,a)\)
\[
 \begin{array}{c|rrrrrr}
          &EG&EL&EF&ES&ET&NG\\ \hline
 \text{degree}&(27,23)&(21,21)&(44,42)&(39,38)&(46,46)&(27,23).
 \end{array}
\]
On either width locus \(J_0=0\) or \(R_{33}=0\), project
the listed width polynomials against that locus by \(b\)-resultants.
On the first locus their exact \(a\)-degrees are
\(100,-\infty,172,154,184,90\) (the second is zero),
and on the second they are \(150,126,258,231,276,150\).
The common gcd is 1 in both cases. A finite actual \(z,b\)
would force all those equations, even at specialized
degree drops. It follows that the actual \(E\) cannot vanish.

## 2. No vertical dropout and finite full tuples

In the proved-live \(E\) chart use the two exact width
polynomials GQ and GF from the preceding finite-width proof.
They have no common component. The test \(E(e)=A_0e+C_0=0\)
is purely a width equation. Its two exact \(b\)-resultants
against GQ, GF have \(a\)-degrees \(656,783\) and common
gcd 1. Independently \(H=0\) also gives unit gcd, with
degrees \(292,350\); no ordered positivity is needed.

Thus \(E(e)\) is genuinely live in every retained width pair.
The earlier degree-six dormant support polynomial evaluated
at \(z=e\) is nonzero, so there are at most six \(z\) values
per width. The two free labels are then fixed by their
actual affine/shifted Cramer formulas. This proves finiteness
of the entire specified clock chart, without leaving a
vertical affine fiber or assuming that it has no valid tuples.

The replay is exact rational arithmetic, not a modular
elimination. Existing Lean gates cover the scalar identities
but not this entire resultant proof.
