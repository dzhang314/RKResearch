# Regular corrected ordinary hole5, star front and star rear, actual silent stage 6 or 7

In the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md), exclude early rank two, star front, and ordinarily weighted true star rear with actual extra ordinarily silent but reverse-live physical row \(\zeta=6\) or \(7\). There are ten strict SDIRK8 stages over a characteristic-zero field, only first quadratic defect, with the first stage ordinarily and reversely silent. Eight ordinarily weighted physical clocks are distinct. The common affine/quintic root is the ordinary fifth \(r=c_5\), with true \(h_5=0\) but \(H(r)\ne0\) for the continued quartic \(H=(S/T)/\gamma^3\). The extra silent clock \(z=c_\zeta\) is a ninth separate site. No ordering is used. This proof does not exchange stages 6 and 7 or equate their amplitudes.

## Actual ordinary clock census and centered nodal polynomial

Let \(a,b,q\) be the actual ordinary clocks of stages 2, 3, 4, and \(d,c,x\) those of 8, 9, 10, respectively. All six are nonhole. If \(\zeta=6\), the remaining ordinary nonhole clock \(n\) is **actual stage 7**; if \(\zeta=7\), it is **actual stage 6**. In both cases \(D_7=(X-n)E_6\), where \(E_6\) is the monic nodal polynomial of \(a,b,q,d,c,x\). Neither \(z\) nor \(r\) is an \(E_6\) root. In particular, the same six pegs pay the same necessary conditions in both true chronologies without a virtual fifth, sixth, or seventh amplitude.

Write \(Y=r/\gamma,\ s=q/\gamma\), \(H_N=\Delta H=\alpha_N L_4+\beta_NK_3\). The known true fourth and zero fifth still impose
\[
 J(\gamma,Y,s)=\frac{\Delta H_4(s)-H_N(\gamma s)}{(s-A)(s-B)}=0,\qquad
 (Y^3-9Y^2+18Y-6)(3s-2Y-1)=0.
\]
Use the [actual star rear](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-literal-closed/README.md), now using only its \(z\)-independent relation \(F(w)=F_0+F_1w=0\). Set \(v=u-1,\ w=v^2,\ X_0=x-\gamma,\ c=X_0-\gamma v,\ d=X_0+\gamma v\), and \(h_j=[X^j]H_N\). The true nonzero \(K=F_1=140\alpha_N\gamma^4=2\gamma^4 h_4\). The useful symmetric form is
\[
 E=K E_6 = (X-a)(X-b)(X-q)(X-x)\bigl(K(X-X_0)^2+\gamma^2F_0\bigr).
\]
No division by a coefficient of \(E\), any signed moment, or \(w\) is used in forming this polynomial. Its leading coefficient is \(K\), and write \(e_5=[X^5]E\).

## Two genuinely paid signed coefficient cuts

Use the signed functional \(\Lambda=H_N(r)I-\beta_N \mathrm{ev}_r\), where \(I(X^j)=1/(j+1)\). Define \(m_j=\Lambda(X^jE)\), \(\nu_j=\Lambda(X^jH_N)\). The standard signed Bézout identity on \(D_7\) is the [nonhole signed identity](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs). Scaling \(D_7\) by \(K\) preserves it. Specifically, for \(D=(X-n)E\), the polynomial
\[
  \mathcal B(D)=H_N W_D^\Lambda-D W_{H_N}^\Lambda,\qquad
  W_G^\Lambda(X)=\Lambda_Z((G(X)-G(Z))/(X-Z)),
\]
is constant. Since \(\nu_0,\ldots,\nu_3=0\), the nonconstant coefficients in degrees 3,2,1 give respectively
\[
\begin{aligned}
 m_1-nm_0&=0,\\
 m_2-nm_1&=2\gamma^4\nu_4,\\
 (e_5-Kn)\nu_4+K\nu_5-2\gamma^4h_3\nu_4-h_4(m_3-nm_2)&=0 .
\end{aligned}
\]
For direct coefficient checking, put \(\eta_j=\Lambda(X^jD)=m_{j+1}-n m_j\). The \([X^3]\) coefficient is \(-h_4\eta_0\); \([X^2]\) is \(K\nu_4-h_3\eta_0-h_4\eta_1\); \([X]\) is \((e_5-Kn)\nu_4+K\nu_5-h_2\eta_0-h_3\eta_1-h_4\eta_2\). The functional is defined symbolically on the high powers in \(m_j,\nu_j\); this does **not** assume ordinary quadrature precision above seven.

Multiply the last two by \(m_0\) and use only the first as a polynomial identity. The two cuts are
\[
\begin{aligned}
 C&=m_0m_2-m_1^2-2\gamma^4\nu_4m_0=0,\\
 N&=(e_5\nu_4+K\nu_5-2\gamma^4h_3\nu_4)m_0-K\nu_4m_1-h_4(m_0m_3-m_1m_2)=0 .
\end{aligned}
\]
Both remain necessary at \(m_0=0\); the full later test includes all coefficient/terminal rank constraints. The source also reconstructs both low-degree cuts directly from the signed polynomial columns as identities independent of these formulas.

## Exact diagonal and full rank-drop fibers

Both cuts have the true factor \(\gamma^6[H_N(r)/\gamma]\), removed by exact division. For the affine-fourth branch \(s=(2Y+1)/3\), specialize both cuts and \(J\) first. Their exact padded \(Y\)-resultants after guard factors \(\gamma^{56}\beta_N^9,\gamma^{68}\beta_N^{12}\), respectively, have degrees 186 and 207. Each has an exact double factor \(L(\gamma)=120\gamma^3-60\gamma^2+12\gamma-1\). Keep that entire leading-drop cubic separately: specialize the full three \(Y\)-polynomials at \(L=0\) into degrees 4, 13, 16. There is no common \(Y\) in that complete fiber. Outside \(L=0\), the remaining degree-180 and degree-201 projections have an exact **rational** monic gcd of degree 30.

For the monic fifth cubic \(D(Y)=Y^3-9Y^2+18Y-6=0\), eliminate \(s\) separately against \(J\) with exact padded resultants. Work modulo the **whole monic cubic**. Both specialized polynomials admit exact removal of \(\gamma^4\) and then \(H_N(r)/\gamma\) in the cubic quotient. The second also admits one exact \(\alpha_N\) removal there. Each quotient is verified by polynomial remultiplication modulo \(D(Y)\), not a diagonal norm cancellation or rejection of modular factors. The output gives two exact rational diagonal polynomials of degrees 243 and 261 whose full monic gcd has degree 54. The guards are true: \(\gamma\ne0,\ \beta_N=\Delta b_rH(r)\ne0,\ \alpha_N\ne0\), and \(H_N(r)=\Delta H(r)\ne0\).

At \((1129,t=203)\) retain every degree-preserving component of the degree-30, cubic, and degree-54 diagonal polynomials with multiplicities, including the complete common \(Y\)-gcd. A full leading unit is checked for at least one defining \(Y\)-polynomial, and likewise in \(s\) on the cubic-\(Y\) branch. Reconstruct \(w=-F_0/F_1\) using a checked unit and the whole double cover \(v^2-w\). The three nonconstant signed coefficient rows for \(E_6,XE_6\) and actual terminal equality \(b_9=b_{10}\) give four rows annihilating coefficients \((-n,1)\). The terminal row is \((H_N(c)E_6'(c)-H_N(x)E_6'(x),\, cH_N(c)E_6'(c)-xH_N(x)E_6'(x))\). All six \(2\times2\) minors are tested, with any remaining front residuals. This detects an inconsistent zero-\(m_0\) branch without treating zero as a pivot, while preserving both physical tail orientations. All **3+1+7** full components pass. This finite localization argument does not assume that an unknown tableau has good reduction.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole5_star_star_middle.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared siblings. Three [native scalar no-pivot statements](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarMiddle.lean) passed Lean/Mathlib 4.36.0; the exact finite proof is source-level. The arithmetic rear, actual silent eighth, arithmetic front, and other ordinary holes are separate. The overall **10–11** bound is unchanged.
