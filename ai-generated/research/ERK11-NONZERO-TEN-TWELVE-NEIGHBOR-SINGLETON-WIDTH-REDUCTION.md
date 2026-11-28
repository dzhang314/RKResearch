# The neighboring singleton coincidence has a width-only regular gate and a finite diagonal pole

**Scope.** Use the [fixed full-pair chronology](ERK11-NONZERO-TEN-TWELVE-CENTRAL-FOUR-ALIASES-CLOSED.md) of order eleven at seventeen stages, with \(q=10,n=12\), both full plateau pairs and sole dormant physical 9. This packet treats the literal coincidence
\[
 s=c_9=c_8,\qquad s\notin\{0,1,a,d\},
\]
with physical 8 active at a singleton label of the response pools. The reflected consequence treats \(c_9=c_{10}\); no ordinary reverse order eleven is assumed. It gives new necessary width equations and a finite width projection for the diagonal pole, **not** an exclusion of every width of the neighboring coincidence. A collision with a different active stage is not covered. The main width geometry is earned over ordered fields; the field arithmetic is characteristic zero with its live guards.

## 1. Measure the two clocks and one center primitive

Use \(W,V,\mathscr P,\mathscr Q,H,C_1,C_2,J_0,I_j,p,r,A_s,B_s,u,v\) as in the [nonalias quadratic](ERK11-NONZERO-TEN-TWELVE-NONALIASED-CENTER-QUADRATIC.md). The two sites \(s,z=c_{10}\) are distinct because the active outer stages 8 and 10 are singleton labels. Actual \(V_Lr\) is supported at physical 8 and 9, now both at \(s\), so its shifted payoffs force \(Hs=C_2\). Actual \(V_LV_R\) is supported in those two distinct clock labels, hence
\[
 s=C_2/H,\qquad
 z=\frac{I_2-sI_1}{I_1-sI_0}.
\]
The denominator is live by the two-node identity and strict variance. In particular \(T_s=\int (X-s)^2WV=(z-s)(I_1-sI_0)>0\). The actual centered \(pV_R\) contact determines the nonzero \(\alpha_9=b_9 p_9 B_s^2=(C_1-zH)/(s-z)\) since \(p_9,B_s,b_9\ne0\). Then the one-row product \(J_0=b_9p_9r_9\) measures the actual reverse primitive
\[
 v=r_9/B_s=\frac{J_0 B_s(s-z)}{C_1-zH}\ne0 .
\]
Thus \(s,z,v\) are functions of the two widths before any outer-response fit. These formulas do not separate the two ordinary scalar weights at \(s\).

The normalized actual \(R_*\) in the nonalias note is now measured by widths. In the normalized true \(9,9\) diagonal
\[
 [L_*,R_*]-uv/J_0=\alpha+\beta u=0
\]
the two coefficients depend only on these widths; explicitly
\[
 \alpha=\left[\frac{\ell_s-\mathscr P(s)\ell_a/\mathscr P(a)}{A_s},R_*\right],
 \qquad \beta=\left[\frac{\ell_a}{\mathscr P(a)},R_*\right]-v/J_0 .
\]
When \(\beta\ne0\) this fixes \(u=-\alpha/\beta\) and \(b_9=J_0/(A_sB_suv)\), including the actual weight of the dormant copy. No new division by a numerical stage weight was used to obtain those measurements.

## 2. A genuine diagonal pole has two compact moment equations

If \(\beta=0\) then \(\alpha=0\) as well. Pair the left adjusted row \(\mathscr P(a)\ell_y-\mathscr P(y)\ell_a\) against \(R_*\) and write the resulting polynomial as \(y(y-a)E(y)\). Its degree-five response correction is \(F\,S(y)\), with \(S\) quadratic. Indeed the adjusted representative has zero primitive share at physical 8, and the exact left calibrated hits \(h,c_6,c_7\) are its three zero conditions against this opposing central row. As in the [sparse actual outer formula](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md#1-use-both-calibrated-extras-without-paying-for-an-extra-grade), with \(B_L\) the monic hull of these three distinct hits,
\[
 E(y)-yS(y)/a=E(0)B_L(y)/B_L(0).
\]
This identity uses the true calibrated roots and \(B_L(0)\ne0\), not a division by an initial derivative slope. At the actual outer clock \(s=c_8\), \(\alpha=0\) gives \(E(s)=0\). Actual \([L_8,R_9]=0\) then gives \(F_8 S(s)=0\). Here \(F_8\ne0\) and \(B_L(s)\ne0\) because this is a singleton active clock different from every calibrated flank hit. Hence \(S(s)=0\) forces \(E(0)=0\), which is exactly the zero initial slope \([D_L^0,R_*]=0\) up to live factors. The actual left seventh-row relation forces the other derivative slope zero too. This keeps slope loss explicit instead of using an undefined projective direction at the pole.

Let \(k(X)=[\ell_X,R_*]\) be the primal polynomial representing the actual right functional: \(\int k\,g=R_*[g]\) for every right anchored model \(g\). Its vanishing left endpoint derivatives put it in \(\operatorname{span}\{W,XW,\mathscr P\}\). The actual \(\alpha=\beta=0\) give \(k(a)=v\mathscr P(a)/J_0\) and \(k(s)=v\mathscr P(s)/J_0\). Since \(s\notin\{0,a\}\), this means
\[
 k=\frac{v}{J_0}\mathscr P+\eta(X-s)W .
\]
Apply the right functional to \((X-s)V\). Its two point supports at \(s,d\) both give zero, while \(\int (X-s)\mathscr P V=C_1-sH=J_0\). Thus \(\eta=-v/T_s\). This proves the exact forced polynomial
\[
 k=v\left(\frac{\mathscr P}{J_0}-\frac{(X-s)W}{T_s}\right).
\]

In particular \(R_*\) annihilates \((1-X)(X-s)(X-d)X^j\) for \(j=0,1,2\). Substitute the forced representation and clear the live \(v,J_0,T_s\). The genuine pole must satisfy
\[
 T_s\int \mathscr P(1-X)(X-s)(X-d)X^j
   -J_0\int W(1-X)(X-s)^2(X-d)X^j=0 .
\]
The equation for \(j=2\) is the \((1+d)\) and \(-d\) combination of the equations for \(j=1,0\): the corresponding polynomial test is the already used \((X-s)V\). Put \(s=C_2/H\) and multiply through by \(H^3\). The two remaining equations have exact bidegrees \((10,9)\) in \((a,b)\), \(b=1-d\), and each has coefficient gcd 1 as a polynomial in \(b\). Their exact \(b\)-resultant has degree 176 in \(a\), with irreducible degrees and powers \(1^8,2^2,2^2,8,8,8^9,12,60\). There is no vertical pole fiber: the coefficient-gcd check ensures some nonzero \(b\)-polynomial at every exact \(a\), including leading drops. Consequently the **diagonal-pole widths are finite**. A full exclusion of these finitely many fields, including the degree-sixty component, is not asserted.

## 3. The regular width-only fit is a genuine necessary cut

If \(\beta\ne0\), use the measured \(u,v\) and use \(R_9\) as the actual opposing row of the left fit. When its first left derivative slope is live, actual \([L_7,R_9]=0\) measures actual \(L_7\); use this \(L_7\) as the opposing row on the right. Thus the actual outer contacts for these chosen directions are \([L_8,R_9]=0\) and \([L_7,R_{10}]=0\). Use the genuine same-clock weight correction in the three scalar moment rows:
\[
 \int X^j\omega Q-\frac{J_0}{uv}s^j Q(s)=0,\qquad j=0,1,2.
\]
On the right use the reflected variable and \(1-s\) in the point correction. This is a fixed rank-one change of the prior sparse moment blocks; the literal temporal rows and unordered cubic hull formulation are unchanged. With both selected initial slopes, fixed moment determinants and raw affine slopes live, the original affine-product and projective algebra therefore recover both true first-pool lines from the **widths alone**. A nonzero constant component in the profile normalizes the fit as before; keep every earlier pivot loss as a separate branch.

The two oriented first-pool lines must be proportional after physical reflection. Their projective determinant is a rational function of \(a,d\) on the guarded chart. Its numerator is **not** the zero polynomial: at \((a,d)=(1/5,2/5)\) the exact replay keeps all reconstructive guards live and finds residue 38 modulo 101. Thus a true regular neighboring coincidence lies on a proper algebraic width curve. This coefficient witness excludes that exact width pair under the same fit, not every point on the curve or guard zeros. It does not count a second-pool proportionality condition as an additional independent mark.

## 4. The ordinary ghost remainder when the repeated clock is an active singleton

There is a concrete further necessary condition at this same-clock copy. Write \(D_s\) for the monic hull of the eight active singleton clock labels, and \(\Omega=X(X-1)(X-a)(X-d)=-\omega\). Since \(s\) is an active singleton label, \(D_s/(X-s)\) is a polynomial. On an actual candidate the [ordinary divided-difference argument](ERK11-NONZERO-TEN-TWELVE-ACTIVE-TWO-PAIR-GATES.md#2-a-ghost-remainder-without-a-simple-root-or-live-weight-condition) gives
\[
 D_s M_{\Omega Q}+P^2 X(X-1)
       +b_9\Omega(s)Q(s)\frac{D_s}{X-s}\equiv0\pmod Q ,
\]
where \(M_R(Z)=\int [R(Y)-R(Z)]/(Y-Z)\). Indeed the active singleton contributions still give the usual partial fraction term from \(P^2 X(X-1)/D_s\), and the dormant copy contributes the additional fraction \(b_9\Omega(s)Q(s)/(s-Z)\). The support of the ordinary scalar measure is contained in the roots of \(\Omega D_s\) after the carrier cancellation. Multiplication by \(D_s\) keeps the extra contribution exactly as displayed. This does not divide by \(Q(s)\) and does not require simple roots of \(Q\). Here \(Q(s)\ne0\) in fact follows from the true active singleton at physical 8 and \(Q(s)=P(s)F_8\); the same-clock correction is not an invisible ghost. One still has \(b_9\Omega(s)=-J_0/(uv)\). This is a separate necessary equation for pursuing the proper width curve, not yet a proved independent resultant or a full neighboring-coincidence exclusion.

The standalone python-flint 0.9.0 replay checks the compact exact projection and guarded nonzero coefficient witness (reference wall time 0.172 seconds). The adjacent core Lean checks the local divided support and primitive-split scalar identities; the physical and quotient-model proofs are mathematical.

Run the [standalone exact replay](erk11-neighbor-singleton-width-reduction/replay_erk11_neighbor_singleton_width_reduction.py). The [Lean scalar companion](../lean/RKCert/ReviewedNative/ERK11NeighborSingletonWidthGate.lean) was checked on all four supported releases.
