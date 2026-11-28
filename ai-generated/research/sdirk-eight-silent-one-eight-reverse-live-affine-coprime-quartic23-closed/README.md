# Affine coprime quartic, actual reverse-live silent row 2 or 3

This excludes eight literal orientations of the strict ten-stage SDIRK8 chart over **characteristic-zero fields**. Physical row one is the sole nonzero quadratic-defect row, with ordinary and reverse weight both zero. Eight ordinary physical rows have pairwise distinct clocks, and the remaining silent row \(\zeta\) has actual nonzero reverse weight at a distinct ninth clock \(z\). Assume the nine-site reverse numerator \(T\) is truly affine, the mixed numerator \(S\) has degree at most four, and \(\gcd(S,T)=1\). Here \(\zeta=2\) or \(3\); both actual literal front phases and both **ordinarily weighted eighth** rear phases are covered independently. No ordering is used. Literal row 4, physical 5–8, \(S\) quintic, quadratic \(T\), and other support charts are not covered. The unrestricted **10–11** interval remains unchanged.

## Exact chronology and profile

Use the [deflation and actual chronology](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md#1-deflate-only-the-actual-extra-reverse-clock). For the monic ordinary nodal polynomial \(D_8\) and \(D_9=(X-z)D_8\), on each actual site \(T(c_i)=D_9'(c_i)w_i\), \(S(c_i)=T(c_i)h_i\). At an ordinary site,
\[
 D_8'(c_i)b_i h_i=\mu T(c_i),\qquad \mu\ne0.
\]
Consequently no actual site is a pole of \(S/T\); otherwise \(S,T\) would share that root. Every ordinary amplitude is nonzero. For \(0\le j\le3\), integrating \(X^jS\) uses only ordinary scalar precision seven. On the ordinary nodes this polynomial equals \(c_i^j T(c_i)h_i\), supported by the paid mixed ordinary reads \(b^\mathsf{T}C^l\boldsymbol h=0\) for \(0\le l\le4\). Thus \(I(X^jS)=0\). These four independent rational moments leave \(S=\sigma L_4\), \(\sigma\ne0\), where \(L_4=70X^4-140X^3+90X^2-20X+1\). The moment matrix on degree at most three is the rational Hilbert matrix, with nonzero determinant in characteristic zero. No moments of degree eight or nine are used.

In normalized clock \(Y\) and amplitude \(H(\gamma Y)=h/\gamma^3\), the actual early clocks are \(a=\gamma A,b=\gamma B\). Their actual normalized amplitudes \(H_a,H_b\) are nonzero, including the literally silent early row. The two front phases set \(v=1+2t,\ 2t^2=1\), \(A=1+v,\ B=1+w\), with \((w,m)=(2-v,0)\) or \((2v,3v/2-1)\). They give \(H_a=(A-1)/2,\ H_b=(B-1-m)/2\) and the actual fourth amplitude polynomial \(H_4(s)\). Write \(L_a=L_4(a),L_b=L_4(b)\), \(\Delta=(B-A)H_aH_b\), and
\[
 q_0=B H_b L_a-A H_a L_b,\quad q_1=H_a L_b-H_b L_a,\qquad Q(X)=\gamma q_0+q_1 X.
\]
The two actual early reads determine the affine denominator: \(H(X)=\gamma\Delta L_4(X)/Q(X)\) at every actual site. In particular \(q_1,L_a,L_b\ne0\) and \(Q\) and \(L_4\) are coprime. The actual fourth equation is \(H_4(s)(q_0+q_1s)-\Delta L_4(\gamma s)=0\). Its exact quotient \(J\) by \((s-A)(s-B)\) has degree at most two. At a real tableau or a tableau over any characteristic-zero field the two removed factors are nonzero from the distinct ninth sites, not from an assumed stronger restriction on physical row one.

## Two exact rear comparisons

Put \(x=1-\gamma,\ c=x-\gamma u,\ k=1+2u-u^2\), with \(u,k\ne0\) as in the cited chronology. Here \(z=a\) if \(\zeta=2\), \(z=b\) if \(\zeta=3\). The actual third rear ordinary clock \(d\) is \(x-\gamma(2-u)\) in the star rear and \(x-2\gamma u\) in the arithmetic rear. The two necessary profile comparisons are
\[
 (x-z)H(c)-k(c-z)H(x)=0,
 \quad
 \begin{cases}
 (2-u)H(c)-uH(d)+(2u-2)kH(x)=0 &\text{star},\\
 H_{\rm r}H(d)+2J_{\rm r}H(c)-kJ_{\rm r}H(x)=0 &\text{arithmetic},
 \end{cases}
\]
with \(H_{\rm r}=-2+u+4u^2-u^3\), \(J_{\rm r}=2+3u-12u^2+4u^3\). These are actual comparisons, not equality of an ordinarily silent stage with a virtual transported amplitude. No division by \(H_{\rm r}\) or \(J_{\rm r}\) occurs.

Clear the evaluated \(Q\) factors, and divide only \(u\) from the first comparison \(G\), \(u(u-1)(u-2)\) from the star shape \(F\), or \(u^2\) from the arithmetic shape \(F\). These are exact polynomial divisions; \(u=1,2\) describe forbidden literal \(d=c,x\) only in the star rear. The exact bidegrees in \((u,\gamma)\) are \((3,10)\) for \(G\) and \((2,14)\) or \((5,14)\) for \(F\). The two orientations \(\zeta=2,3\) are independently constructed; no literal exchange is needed. The exact Sylvester resultant \(\operatorname{Res}_u(F,G)\) has \(\gamma\)-degree 62 or 92. Its bounded split-prime CRT computation uses the reviewed small resultant helper. It vanishes at any true solution even if both gap polynomials drop degree at that \(\gamma\).

Divide out the exact factors \(\gamma^{6}\) or \(\gamma^7,\ L_aL_b,\ Q(x)^2,\ R_{12}\). The degree-12 polynomial \(R_{12}\) is the quotient of \(q_1^4 L_4(-\gamma q_0/q_1)\) by its exact factors \(L_a,L_b\). It is an actual nonzero guard: \(\gamma\ne0\), \(L_a,L_b\ne0\) from the two nonzero early reads, \(Q(x)\ne0\) from actual terminal interpolation, and \(\gcd(Q,L_4)=1\) excludes the remaining factor. The exact retained monic diagonal \(M\) has degree **26** or **55**, including multiplicities.

## Full finite fibers and actual fifth

For \(W_F(X)=I_Y((F(X)-F(Y))/(X-Y))\), the ordinary deflation gives
\[
 L_4 W_{D_8}-D_8 W_{L_4}=\lambda Q^2,\qquad \lambda\ne0 .
\]
Indeed the normalized joined divided difference \((D_8(X)L_4(Y)-L_4(X)D_8(Y))/(X-Y)\) has \(Y\)-degree at most seven. Inserting the eight actual ordinary weights reduces its integral to the cardinal interpolant of \(b_iD_8'(c_i)L_4(c_i)=\lambda Q(c_i)^2\). This proves the identity without an extra ordinary scalar moment. Taking it modulo \(L_4\), set \(Z=Q^2W_{L_4}^{-1}\bmod L_4\), whose rational fixed inverse exists by gcd one. Then \(70D_8=L_4(X)(X^4+U_3(X))+\rho Z\) with \(\deg U_3\le3\). The five true ordinary pegs are the **other** literal early clock, physical fourth, and physical 8, 9, 10. The exact five-row Cramer system uses columns \(L_4(v),vL_4(v),v^2L_4(v),v^3L_4(v),Z(v)\), with right-hand side \(-v^4 L_4(v)\). Its determinant is checked as a unit on the complete localized finite algebra below, not presumed from distinct clocks alone. The missing factor is monic cubic and includes the actual ordinary fifth clock.

The [actual rows 2–5 fifth determinant](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md#3-full-quartic-exclusion-and-conditional-pure-quintic-control) uses the four columns \(\boldsymbol h,C\boldsymbol h,A\boldsymbol h,\boldsymbol\tau_4\), including the literal silent row itself. As a function of its prospective \(h\) at \(Y\), it is \(D_0(Y)+hD_1(Y)\) by row linearity with the preceding actual amplitudes fixed. Evaluate it by computing at \(h=0,1\), multiplying \(D_0\) by \(Q(\gamma Y)\), and adding \(\gamma\Delta L_4(\gamma Y)D_1\). The only subsequent division is by the three actual forbidden padded roots \((Y-A)(Y-B)(Y-s)\). The resulting degree-at-most-two polynomial must share the actual fifth root with the normalized missing cubic. The determinant of multiplication by this polynomial on the missing cubic is a unit in all reduced fibers, excluding the shared root.

For exactness of the finite arithmetic, localize \(\mathbb Z_{(1129)}[t]/(2t^2-1)\) at the residue \(t=203\); either characteristic-zero early orientation is an embedding of \(\mathbb Q(t)\). The monic \(M\) preserves its full degree. In every reduced diagonal component the leading coefficients of \(F,G,J\) retain their full degrees. After inverting the checked leading units, one can adjoin the monic gap \(F\) and the monic fourth factor \(J\), and impose \(G=0\), to obtain a finite integral algebra over this local base. The replay checks the full factor product of the reduction of \(M\), with exponents. At each reduced factor it uses the complete gcd of \(F,G\), not a selected gap root, and the full quadratic \(J\), not a selected fourth root. Testing all maximal-ideal components suffices for invertibility even with repeated factors. The Cramer determinant and the later literal predecessor denominators are units there, then so is the missing-cubic multiplication determinant. A finite algebra over this local base has every maximal ideal above its maximal ideal, so the units lift before passing to characteristic zero. This is not a hypothesis that an unobserved tableau has good reduction. No reduced collision or vanishing-leading branch is deleted.

## Replay and Lean

Install `sympy==1.14.0` and `python-flint==0.9.0`. Run `python3 check_eight_reverse_live_affine_coprime_quartic23.py` in this folder, with the sibling folders listed in the entry point. It checks all **28 reduced diagonal components** across the eight orientations and the entire gap/fourth fibers. The [native Lean packet](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineQuarticLiteral.lean) checks affine recovery, nonpole deflation, exact quartic padding including degree drop, both homogeneous rear clearings and literal fifth clearing on Lean/Mathlib 4.36.0. The saturation-to-chronology proof, exact CRT, and finite fiber replay are source-level, not end-to-end Lean. The [shared-root companion](../sdirk-eight-silent-one-eight-reverse-live-affine-quartic-shared-gauss-closed/README.md) is separate and treats the affine-quartic \(Q,L_4\) common-root charts.
