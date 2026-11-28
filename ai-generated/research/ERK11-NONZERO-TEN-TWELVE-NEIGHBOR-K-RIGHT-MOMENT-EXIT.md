# The neighboring singular cross block has no right fixed-moment loss

**Scope.** In the [neighboring singleton original right-loss chart](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-RIGHT-SLOPE.md), the sole dormant physical row 9 shares \(s=c_8\notin\{0,1,a,d\}\), with the fixed full-pair ordered ERK11 chronology and \(q=10,n=12\). Assume \(K_0(a,b)=0\), where \(b=1-d\). Retain original \(R_9\) for the left fit and use actual \(L_9\) for the rotated right fit. The rotated first right slope and the left fixed moment inverse are [already live](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-LEFT-MOMENT-EXIT.md). This note excludes the **right fixed three-by-three moment loss on this particular curve**. The right affine and regular masks and all branches away from \(K_0=0\) remain separate. The reflected neighboring coincidence has the reflected result.

## Width equation for the actual rotated right mask

Use the live width data
\[
 u=-\frac{\alpha'}{H^3\beta'},\qquad v=\frac{J_0 B_N S}{H^3 U},\qquad
 \rho=\frac{J_0}{uv}=-\frac{H^6 U\beta'}{\alpha' B_N S},
\]
as in the original right-loss note. In particular both \(\alpha'\) and \(\beta'\) are live by the diagonal-pole exit and \(u\ne0\). The polynomial row
\[
 \widehat L:=\beta' L^\circ-30\alpha'\ell_a
\]
is \(H^3a^5\beta'\) times \(L_*\), thus a live scalar multiple of actual \(L_9\). Pair \(\widehat L\) against the true right derivatives \(D_R^1,D_R^d\). The first slope is live. One can divide both polynomials by their exact common gcd, because otherwise the live first slope would vanish. This is only a common scaling of the two hull coefficients \(t_0,t_1\), not a second width premise.

Work in the reflected coordinate \(Y=1-X\), with \(w=b,\ c=1-a,\ h=w/2,\ \sigma=1-s=(H-C_2)/H\). The calibrated right singleton hull and fixed columns are
\[
 \begin{split}
 B_0&=Y(Y-w)(Y-h),\qquad B_1=(Y-h)[w t_0-(t_0-t_1)Y],\\
 B&=B_0+t B_1,\qquad \phi=Y^2(w-Y),\\
 (C_0,C_1,C_2)&=(\phi,YB_0,YB_1).
 \end{split}
\]
Rescaling the two slopes just rescales the third fixed column and the reciprocal product parameter. Set \(\omega_R=Y(1-Y)(Y-w)(Y-c)\). Let \(M^0\) be the three rows \(\int Y^j\omega_R\, C_\bullet\), \(0\le j\le2\). The measured right moment rows are \(M^0_j-\rho\,\sigma^j C_\bullet(\sigma)\). Since correction rows are proportional, their determinant equals
\[
 \det M^0-\rho\sum_{j=0}^2
  \sigma^j\det\bigl(M^0\text{ with row }j\text{ replaced by }C_\bullet(\sigma)\bigr).
\]
Each summand has \(\sigma\)-degree at most six. Multiply by \(\alpha' B_N S\), substitute \(\sigma=(H-C_2)/H\), and use \(H^6\) from \(\rho\) to homogenize the sum. All width clearings and the reduced first slope are live. This is an actual moment-loss equation for the rotated right fit, irrespective of any of its other pivots.

The exact polynomial has raw bidegree \((49,51)\), live-deflated bidegree \((44,41)\), and its \(b\)-resultant with \(K_0\) has degree 255 in \(a\). The exact irreducible degrees with multiplicity are \(3,3,12^2,12^3,87,102\). At \(165a^3-180a^2+54a-4=0\) the whole joint exact \(b\)-gcd is \(b\), forbidden. The other cubic \(30a^3-36a^2+12a-1\) has unit exact \(b\)-gcd (no finite root). Both degree-twelve fields have exact linear whole joint \(b\)-gcd whose root forces \(U=0\), forbidden.

## Actual temporal restoration and the independent profile transfer

For the degree-87 factor use the simple place \((p,a,b)=(29,9,19)\); for degree 102 use \((19,17,16)\). The replay checks the full \(a\)-degree and simple residue of the monic exact \(a\)-factor. Under these embeddings the polynomial \(K_0\) retains \(b\)-degree three and the whole joint residue \(b\)-gcd is linear, so all candidate \(b\) are integral and reduce to the displayed values. All needed width guards are units. This concerns the width field, not a reduction of unknown tableau entries.

The sparse fit uses
\[
 Q=U_f\phi+W_f YB_0+T_f YB_1+A_f(B_0+t B_1),\qquad
 P=w[U_f+(T_f/t-W_f)(Y-h)].
\]
The three corrected moment rows and the actual fourth outer row act linearly on these coefficient coordinates, with the last column affine in \(t\). If their first three columns have rank three, the true nonzero profile kernel has \(A_f\ne0\). One can set it to 1; the full four-row determinant is still the raw affine equation. This does not invert a vanished fixed moment determinant.

* At degree 87 the ordinary left fixed pivot is a unit. On the rotated right use the two lowest moment rows and the **actual** right temporal row \([L_9,R_{10}]=0\). Its first-three-column pivot is a unit; both full affine slopes and actual products are units. The reconstructed oriented first-pool lines are \((14,12),(9,24)\). Since the latter line is in \(Y=1-X\), the necessary physical projectivity determinant is \(14\cdot24+12(9+24)=7\bmod29\), impossible. No evaluation of the reconstructed lines at a right residue clock is divided by; whichever of those evaluations happens to vanish modulo 29 is immaterial.
* At degree 102 the original left fit is guarded; the right raw affine slope need not be a unit. Reflect the known left \(P,Q\), calibrating their relative scale at the actual right half-clock \(h\) to make \(Q(h)=P(h)Y^2(w-Y)/w|_{Y=h}\). This uses the active half-clock and its nonzero evaluations. Put \(y=1-z\), the true physical row-10 clock in reflected coordinates. The **actual rotated right temporal contact**, not the right fit inverse, gives
\[
 k_0+t k_1=0,\qquad
 k_0=Q(y)S_0(y),\quad
 k_1=P(y)y(y-w)E(y)B_1(0)+Q(y)S_1(y),
\]
where \(E\) is the calibrated outer polynomial, \(S_0=-w E(0)(Y-w)(Y-h)\), and \(S_1=w(E B_1(0)-E(0)B_1)/Y\). In fact the true contact before replacing its response is \(y(y-w)E(y)tB_1(0)+F_R(y)(S_0(y)+tS_1(y))=0\), and \(F_R=Q/P\) on the right after calibration. At the selected place \((k_0,k_1)=(18,6)\), so \(t=16\). The actual three right calibrated singleton clocks must give the monic divisibility \(B_0+tB_1\mid Q-PY^2(w-Y)/w\). The monic remainder commutes with reduction, even if labels coalesce there. It is \(13Y^2+11Y+11\), nonzero.

This excludes both remaining factors and hence the whole right fixed moment loss on \(K_0=0\). The new standalone exact replay uses python-flint 0.9.0 and no external data (reference wall time 1.479 seconds). The companion core Lean covers the terminal scalar computations, not the actual tableau and field-place bridge.
