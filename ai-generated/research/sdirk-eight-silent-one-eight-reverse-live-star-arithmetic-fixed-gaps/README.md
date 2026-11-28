# Two singular backward pivots, with an ordinary arithmetic rear

This closes the following subchart of strict ten-stage SDIRK8 over every characteristic-zero field. Physical first is the sole nonzero quadratic-defect row, ordinarily silent. Eight ordinary active clocks are distinct, and the additionally ordinarily silent physical row \(\zeta\in\{5,6,7\}\) has an actual nonzero reverse read at a distinct ninth site. The nine-site reverse numerator is constant nonzero, the profile is a regular genuine mixed quintic with both early quartic values nonzero, the literal front is star, and the ordinary rear is arithmetic. The two normalized penultimate gaps \(u=1,2\) are both excluded. The general arithmetic-rear chart and unrestricted **10–11** gap remain open here.

## Tail pivot and literal clocks

Write \(x=1-\gamma\), \(c=x-\gamma u\), \(d=x-2\gamma u\) for actual physical 10, 9 and 8, and \(z=c_\zeta\) for the actual ordinarily silent clock. Put
\[
 k=1+2u-u^2,\quad H_{\rm r}=-2+u+4u^2-u^3,\quad
 J_{\rm r}=2+3u-12u^2+4u^3 .
\]
The [existing arithmetic tail](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md#rear-arithmetic-exact-nested-resultant-projections) pays \(H_{\rm r} H_*(d)+2J_{\rm r}H_*(c)-kJ_{\rm r}H_*(x)=0\). The actual affine relation is \((x-z)H_*(c)=k(c-z)H_*(x)\). Neither \(k\) nor \(H_*(x)\) nor \(x-z\) vanishes. If \(H_{\rm r}=0\), then \(J_{\rm r}\ne0\) by the polynomial Bézout identity
\[
(-676u^2+1604u+493)H_{\rm r}+(-169u^2+570u+525)J_{\rm r}=64 .
\]
The tail plus affine relation would give \(z=2c-x=d\), a collision of distinct reverse sites. Likewise \(J_{\rm r}=0\) would force \(H_{\rm r}=0\) since \(H_*(d)\ne0\). The actual ratios \(\rho_i=w_i/(\gamma^2 b_i)\) of ordinary tail rows, with \(\boldsymbol w=2\boldsymbol b^{\mathsf T}C A-\boldsymbol b^{\mathsf T}(I-C^2)\), satisfy \(\rho_{10}=-1,\rho_9=-k\). The constant-numerator identity gives
\[
 H_*(d)=-\rho_8 H_*(x)\frac{d-z}{x-z},
 \qquad
 2H_*(c)-kH_*(x)=kH_*(x)\frac{d-z}{x-z}.
\]
Thus \(\rho_8=kJ_{\rm r}/H_{\rm r}\). In the normalized coordinates \(Y_i=c_i/\gamma\), the three backward rows have suffix block with columns \(b_i(1,Y_i,\rho_i)^{\mathsf T}\) on the *physical* rows \(i=8,9,10\). Its determinant is
\[
 b_8b_9b_{10}\,u(\rho_8+2k-1)
 = -\frac{2b_8b_9b_{10}\,u^3(u-1)^2(u-2)}{H_{\rm r}} .
\]
All displayed unit assumptions here hold at an actual candidate. As \(u\ne0\), this pivot can fail exactly at the two fixed gaps addressed below, not at an arbitrary root encountered in reduction. The [native Lean gate](../../lean/RKCert/ReviewedNative/SDIRK8OrdinaryArithmeticRearGaps.lean) checks the normalized determinant and its cleared factorization on Lean/Mathlib 4.36.0.

## Full exact fixed-gap projection

The four fixed pegs \(a=\gamma A_0,b=\gamma B_0,q=\gamma s,x\) are all ordinary and distinct for each listed physical silence. Use the [known-peg proof](../sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed/README.md#fixed-known-peg-pivot-not-a-residue-assumption) derived at ordinary scalar precision **seven**. The five-peg determinant \(N(v)\) for a prospective ordinary peg \(x-\gamma v\), after its known regular exact factor divisions, is the true missing quartic up to nonzero scalar. In particular \([v^4]N\ne0\) at the actual tableau. Since both \(c,d\) are ordinary, \(N(u)=N(2u)=0\). No actual fifth-stage equation is used, so this also covers silent physical fifth and makes no assignment of either of the two other ordinary unknowns.

For either fixed \(u\), take the two exact fourth-clock resultants from \(N(u),N(2u)\), and \(N(u),T\) where \(T=H_{\rm r}H_*(d)+2J_{\rm r}H_*(c)-kJ_{\rm r}H_*(x)\). The literal front swap makes these equations rational. Remove only powers of strict-diagonal guards \(\gamma,L_4(a)L_4(b),(x-a)(x-b),(c-a)(c-b),(d-a)(d-b)\). The first three rear clocks really are distinct from both literal front clocks; no fourth-clock or unnoticed contact is removed by these univariate guards. The two surviving diagonal polynomials have monic gcd \(M^2\), where \(M\) is the exact degree-21 exceptional fourth projection of the [literal-front model](../sdirk-eight-silent-one-eight-reverse-live-exceptional/README.md). Only \(M(\gamma)=0\) is inferred: this alone does **not** identify a true candidate's fourth clock as exceptional.

In the exact monic diagonal algebra \(\mathbb Q[\Gamma]/(M)\) (the arithmetic implementation permits the equivalent quadratic base), the fourth-clock polynomial gcd of \(N(u),N(2u),T\) is monic linear. It divides \([v^4]N\) there. Specializing the Euclidean identities at any actual \(\gamma\) gives a proof that the true fourth clock would make the known-peg leading coefficient vanish. The exact coefficient inverses used by the Euclidean routine are checked units in the diagonal algebra, and \(M\) need not be assumed irreducible. This excludes the complete two fixed-gap fibres without inferring any characteristic-zero statement from count or sample residue data.

## Replay

Install **sympy==1.14.0** and **python-flint==0.9.0**, then run **python3 check_star_arithmetic_fixed_gaps.py** with the declared sibling source folders. This arithmetic replay uses only exact rational operations. The native scalar gate is separate from the source-level exact diagonal and fourth-clock arithmetic.
