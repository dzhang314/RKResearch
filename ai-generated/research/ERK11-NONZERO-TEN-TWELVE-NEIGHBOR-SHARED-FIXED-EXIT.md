# Both shared fixed-moment curves are impossible with their own endpoint read live

**Scope.** Ordered-field, all-live, ordinary \(17\)-stage order-eleven chart with the two half-clock carriers, both seventh-front boundaries genuinely new, \(q=10,n=12\), full plateau pairs at \(a,d=1-b\), and lone dormant physical \(9\) sharing the active singleton at physical \(8\), \(s=c_8=c_9\notin\{0,1,a,d\}\). Use the measured diagonal and the full rank-three corrected moment operator on the live cross block \(K_0\ne0\). The exact shared fixed-moment/affine factors \(E_L\) and \(E_R\) are ruled out, respectively when the true \(Q(0)\ne0\) or \(Q(1)\ne0\). In particular this closes **both shared factors in the both-endpoints-live chart**, including every sparse determinant, temporal coefficient and degree drop on those factors. The complete earlier single-endpoint exits therefore make both factors empty within this chart. The two nonshared fixed factors, residual raw-affine intersections and fully pivotable finite widths are separate. The proof is characteristic-zero field algebra after the inherited actual ordered-field gates. It is not an unrestricted stage-count theorem.

References to the relative packet names below are to the fixed neighboring-singleton topology, not to the independent ordinary-reversal branch.

## 1. The common moment kernel is spanned by one cubic and its shift

Write \(\omega=X(1-X)(X-a)(X-d)\), \(\rho=b_9\omega(s)\), and
\[
 \mathcal L_j(u)=\int_0^1 X^j\omega(X)u(X)\,dX-\rho s^j u(s).
\]
The true second-pool polynomial \(Q\), of degree at most four, lies in \(K_3=\ker(\mathcal L_0,\mathcal L_1,\mathcal L_2)\) inside \(\mathbb F[X]_{\le4}\), and \(\dim K_3=2\) by the full moment rank theorem. The inverse anchored pairing on the five mixed rows has \([L_i,R_j]=\delta_{ij}/b_i\). In particular the two actual row-9 functionals have the point-supported forms
\[
 L_9=\ell_s+\epsilon\ell_a,\qquad R_9=r_s^{\rm ev}+\eta r_d^{\rm ev},
\]
on \(X\mathbb F[X]_{\le4}\) and \((1-X)\mathbb F[X]_{\le4}\), respectively. The shared factors are exact, after removing only width factors already live:
\[
 E_L=0\iff [\ell_a,R_9]=0,\qquad
 E_R=0\iff [L_9,r_d^{\rm ev}]=0.
\]
These are width statements, **not** implications that the actual \(Q\) vanishes at either endpoint.

On \(E_L=0\), the primal representative \(k(X)=[\ell_X,R_9]\) has the factorization \(k=X(X-a)r\), \(\deg r\le3\), with \(r\ne0\). Indeed \(k(s)=1/b_9\), since \([L_9,R_9]=1/b_9\) and the plateau term vanishes. For \(0\le j\le3\), the opposite anchored polynomial \((1-X)(X-d)X^j\) has degree at most five. Duality and the actual two supports of \(R_9\) give
\[
 \int_0^1 X^j\omega r
   =R_9\big((1-X)(X-d)X^j\big)
   =(1-s)(s-d)s^j
   =\rho r(s)s^j.
\]
The last equality is exactly \(b_9 k(s)=1\). Thus both \(r\) and \(Xr\) lie in \(K_3\). They are independent because \(r\ne0\) and the coefficient ring here is a field. Consequently
\[
 Q(X)=r(X)\Lambda(X),\qquad \Lambda(X)=\lambda_0+\lambda_1X.
\]
This does not assume \(r\) has degree three or \(\Lambda\) has degree one.

For \(E_R=0\) use the actual \(L_9\) and the primal representative \(k_R(X)=[L_9,r_X^{\rm ev}]=(1-X)(X-d)r_R(X)\). The equality \(k_R(s)=1/b_9\) follows from \(R_9=r_s^{\rm ev}+\eta r_d^{\rm ev}\). Against \(X(X-a)X^j\), \(0\le j\le3\), the same pairing gives \(\int X^j\omega r_R=s(s-a)s^j=\rho r_R(s)s^j\). Thus \(Q=r_R\Lambda_R\). In the own variable \(Y=1-X\), take \(w=b\) and \(r(Y)=-r_R(1-Y)\) so that the primal representer reads \(k(Y)=Y(Y-w)r(Y)\), and absorb the sign into the reflected \(\Lambda\). This works in the **same** \(s=c_8\) chronology, without assuming \(c_{10}=c_9\), or an independent ordinary reverse order-eleven tableau.

## 2. The actual sparse fit makes the first pool proportional to the affine factor

Use the own coordinate \(Y\), width \(w=a\) or \(b\), and \(h=w/2\). Use the actual opposite row \(R_9\) on the left or \(L_9\) on the right, even if the earlier right regular fit used \(L_7\). The paired derivative slopes are
\[
 \ell_0=k'(0)=-w r(0),\qquad
 \ell_1=k'(w)=w r(w).
\]
The own endpoint read \(Q(0)\) in this coordinate is live, so \(r(0)\ne0\) and \(\lambda_0\ne0\). Hence \(\ell_0\ne0\). The actual seventh-boundary off-diagonal with this opposite row is \([L_7,R_9]=0\) on the left or \([L_9,R_{11}]=0\) on the right. If \(u,v\) are the two genuine extras in the own front, it reads
\[
 (w-u)(w-v)\ell_0-uv\ell_1=0.
\]
The extras are nonzero and different from \(w\). Thus \(\ell_1\ne0\) as well. These are actual seventh-row conditions; in particular the rotated right slopes were not presumed live.

Put
\[
 B_0=Y(Y-w)(Y-h),\quad
 B_1=(Y-h)[w\ell_0-(\ell_0-\ell_1)Y],\quad
 \phi=Y^2(w-Y).
\]
The genuine extras and the actual half-clock have monic hull \(B_0+tB_1\) with \(t=uv/(w\ell_0)\ne0\). At its three calibrated sites the second pool is \(P(Y)\phi(Y)/w\), where \(P\) is the actual affine first-pool polynomial in this orientation (on the right it is reflected and multiplied by a live constant). Thus the exact sparse coefficient identity is
\[
 Q=U\phi +(WY+A)B_0 +(TY+B)B_1,\qquad
 B=tA,\qquad
 P=w\big[U+(T/t-W)(Y-h)\big].
\]
This follows by dividing \(Q-P\phi/w\) by the monic hull and using \((Y-h)\phi+Y B_0=0\). It assumes no inverse moment or temporal pivot.

The derivative formulas give \(B_1(0)=w^3r(0)/2\) and \(B_1(w)=w^3r(w)/2\), both live. Therefore
\[
 r-\tfrac{2}{w^3}B_1=Y(Y-w)g,\qquad \deg g\le1.
\]
Evaluating the sparse identity at the same two distinct points gives \(TY+B=(2/w^3)\Lambda\). Subtract that contribution and cancel the nonzero polynomial \(Y(Y-w)\):
\[
 \Lambda(Y)g(Y)=-UY+(WY+A)(Y-h).
\]
Write \(g(Y)=g_0+g_1Y\). Evaluating at \(0,h\) and comparing the quadratic coefficient give
\[
 hA=-\lambda_0g_0,\qquad hU=-\Lambda(h)g(h),\qquad W=\lambda_1g_1.
\]
Also \(\lambda_0(T/t)=\lambda_1 A\) by \(TY+B=(2/w^3)\Lambda\) and \(B=tA\). Since \(h,\lambda_0\ne0\), it follows that \(T/t-W=-\lambda_1g(h)/h\), and hence
\[
                 P=-\frac{w g(h)}h\,\Lambda.
\]
The actual first-pool line is nonzero, so \(g(h)\ne0\). No ratios of the two temporal coefficients, no projections in the width variable, and no leading coefficient assumptions were made. In particular the simultaneous temporal-coefficient-zero fiber is covered by the same identity.

## 3. The degree-eight active-singleton identity is incompatible

In physical coordinates the true profile obeys
\[
                    P\,\mathcal B_\tau-Q^2=\lambda D_s,
 \qquad\lambda\ne0,\qquad \deg\mathcal B_\tau\le7,
\]
where \(D_s\) is the monic degree-eight hull of the eight distinct active singleton clock labels. The factor \(\lambda\) is live by the two distinct active states at a true plateau pair. Every root of \(D_s\) is an actual active singleton and has live \(P(c)\). These facts are the [two-pair pooled identity](ERK11-NONZERO-TEN-TWELVE-ACTIVE-TWO-PAIR-GATES.md), not a normalization of the temporal fit.

The preceding proportionality implies \(P\mid Q\); that divisibility in the right-oriented coordinate transfers back by \(Y=1-X\) and the live first-pool scale. If \(P\) is nonconstant then it is linear, so it divides \(D_s\), contradicting its live read at every root. If \(P\) is constant, then \(\Lambda\) is constant, \(\deg Q\le3\), and \(P\mathcal B_\tau-Q^2\) has degree at most seven, impossible since \(\deg(\lambda D_s)=8\).

That closes both shared factors on their own-live scope. Combined with the earlier [left-endpoint exit](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-LEFT-ENDPOINT-EXIT.md), [right-endpoint exit](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-RIGHT-ENDPOINT-EXIT.md), and double-endpoint contradiction, there are no remaining endpoint masks on either factor. The corrected rank and shared-factor identifications are the [full moment theorem](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-FULL-MOMENT-RANK.md) and [individual mask proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-INDIVIDUAL-MASK-FINITENESS.md).

The adjacent small core Lean file checks the cleared scalar sparse-factor manipulation over an arbitrary commutative ring. The actual anchored grade spaces, width-factor ingress, and polynomial degree argument above remain mathematical. No finite-root computation is needed for this packet.
