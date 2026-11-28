# Genuine quintic with affine shared root absent from ordinary clocks

This excludes **all actual silent placements 2–8** in one strict ten-stage SDIRK8 chart over characteristic-zero fields. Physical one is the sole nonzero quadratic-defect row and has zero ordinary and reverse contribution. Eight ordinarily weighted physical rows have pairwise distinct clocks, and one other ordinarily silent row \(\zeta\) has a genuine nonzero reverse read at a separate ninth clock \(z\). Let \(T\) and \(S\) interpolate the actual reverse and reverse mixed numerators on those nine sites. Here \(\deg T=1,\deg S=5,\gcd(S,T)\ne1\), and the unique root \(r\) of \(T\) is **not an ordinary clock**. The first physical clock need not be distinct from those nine. No ordering is used. A shared root at an actual ordinary clock and coprime quintic profiles remain separate. The unrestricted strict SDIRK8 interval remains **10–11**.

## Exact quartic amplitudes but a genuinely affine residual

The common root gives the degree-four polynomial \(S/T\). The ordinarily silent clock \(z\) is also not \(r\), since \(T(z)=D_9'(z)w_\zeta\ne0\). Thus \(H=(S/T)/\gamma^3\) is the actual normalized cubic-defect profile on **all nine** sites. For \(0\le j\le3\), ordinary scalar precision seven integrates \(X^jH\) using the eight ordinary weights. Its weighted sum vanishes by the paid \(b^\mathsf T C^j\boldsymbol h\) moment. The inverse four-by-four Hilbert matrix therefore gives \(H=\alpha L_4\) with \(\alpha\ne0\). The [native quartic-moment lemma](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticNoHole.lean) checks those four coefficient implications without ordering or positivity.

This does **not** give the constant reverse numerator identity. Let \(L=L_4/70\) be monic. At an ordinary site the same paid nodewise deflation gives \(D_8'(c_i)b_i L(c_i)=\nu T(c_i)\) with \(\nu\ne0\), including the true affine scale. Write \(W_F(X)=I_Y((F(X)-F(Y))/(X-Y))\). Its joined divided difference for \(L W_{D_8}-D_8 W_L\) has \(Y\)-degree at most seven. The ordinary weights therefore integrate it to the cardinal interpolant of \(\nu T\) on the ordinary nodes. Thus
\[
 L W_{D_8}-D_8 W_L=\nu T,
\]
with a **linear**, not constant, right side. The reconstruction below retains both affine coefficients.

## Compact complete scalar model

The two literal early amplitudes are known nonzero even if one physical row is ordinarily silent. For unnormalized literal clocks \(a=\gamma A,b=\gamma B\), their ratio gives \(H_a L_4(b)=H_b L_4(a)\). The exact monic diagonal equation has degree four in each front. Given \(\gamma\), the amplitude scale uses the actual nonzero \(L_4(a)\). The actual fourth satisfies the literal \(H_4(s)=\alpha L_4(\gamma s)\), with only the exact forbidden \(s-A,s-B\) pads removed, leaving degree at most two. True penultimate \(c=x-\gamma u,\ x=1-\gamma,\ k=1+2u-u^2\), and the two ordinary-eighth rear shapes or actual silent-eighth shape are those of the [polynomial quartic chronology](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md). These shape formulas depend on the actual profile \(H\), **not** on the degree of the reverse numerator. In the star and arithmetic ordinary eighth the gap has degrees two or five, respectively; for actual silent eighth it has degree four. Use only \(u(u-1)(u-2)\), \(u^2\), or \(u\) pads, respectively, as licensed by actual physical clock distinctness.

For \(\zeta=2,3,4\), the actual ordinary-silent clock \(z\) is \(a,b,q=\gamma s\) respectively. The actual penultimate read forces
\[
 (x-z)L_4(c)-k(c-z)L_4(x)=0 .
\]
That equation is already a unit obstruction on every complete reduced factor. For \(\zeta=5\), the penultimate read gives the actual silent fifth coordinate
\[
 Y=\frac{x+\gamma u k L_4(x)/(L_4(c)-kL_4(x))}{\gamma}.
\]
The inner denominator is truly nonzero because the actual affine comparison makes \((x-z)(L_4(c)-kL_4(x))=-\gamma u k L_4(x)\) with nonzero right side. Do not assign any ordinary fifth weight or missing ordinary root in this placement. The actual rows 2–5 determinant uses the polynomial profile, with only the exact literal pads \(Y-A,Y-B,Y-s\) removed; it is of degree at most two. Its value at this actual \(Y\) is a unit in all four phase pairs.

## Six true ordinary pegs and a paid terminal weight test

For \(\zeta=6\) and for \(\zeta=7\), the six actual ordinary pegs are \(a,b,q,x,c,d=c_8\). Their later ordinary assignments differ, but the following cut precedes any assignment. For \(\zeta=8\) there is no ordinary eighth peg. The actual ordinarily weighted fifth is drawn from the **whole** literal fifth quadratic, using no silent-root formula for physical fifth. In that full algebra the six pegs instead are \(a,b,q,x,c,\gamma Y\).

Let \(V_0=W_L^{-1}\bmod L\) and \(V_1=XV_0\bmod L\); the fixed inverse exists exactly. The affine Bézout polynomial implies
\[
 D_8=L U_4+\lambda_0 V_0+\lambda_1 V_1
\]
with \(U_4\) monic of degree four and **both** scalars unknown. Interpolate the two functions \(V_j/L\) on the six known ordinary pegs into polynomials \(P_j\) of degree at most five. The linear combination \(-\lambda_0P_0-\lambda_1P_1\) is \(U_4\), since both agree at the six nodes. Set \(A_j=[X^5]P_j,\ B_j=[X^4]P_j\). The equations
\[
 A_0\lambda_0+A_1\lambda_1=0,\qquad
 B_0\lambda_0+B_1\lambda_1=-1
\]
recover the two true affine coefficients after the pivot \(A_0B_1-A_1B_0\) is checked a unit. This check holds in every full algebra used, as do the required six nodal and profile denominators. It does not assume a generic Cramer pivot.

At actual penultimate the first paid backward row of \(A'=A/\gamma\) has just the diagonal and the actual terminal predecessor tap \(u\), so \(b_9+b_{10}u=b_9(1+u)\). Since \(u\ne0,\ b_9=b_{10}\). This forces the exact division-free gate
\[
 W_{D_8}(c)D_8'(x)-W_{D_8}(x)D_8'(c)=0 .
\]
Its value is a unit on every full reduced component for \(\zeta=6,7,8\), including both possible actual fifth roots for \(\zeta=8\). No unmeasured sixth/seventh assignment, extra weight equality, or higher paid moment is needed.

## Domain, replay and Lean

Use the complete monic diagonal degree four at \((1129,t=203)\); for each literal front the two early orientations are embeddings of the same \(\mathbb Q(t)\) with \(2t^2=1\). Both reduced diagonal factors for star (degrees 1 and 3) and the single arithmetic factor (degree 4) are kept, with their entire monic fourth and rear fibers. The shape leading coefficients are checked as units before monic division, and for \(\zeta=8\) the full fifth quadratic leading unit is checked as well. Nothing is discarded at a coincident residue or a degree drop. Units lift by the finite integral model over the localized coefficient ring, as in the literal 2/3 companion. This does not require that an actual unknown tableau was independently integral at the residue.

With `sympy==1.14.0` and `python-flint==0.9.0`, run `python3 check_eight_reverse_live_affine_shared_quintic_nohole.py`. This covers all **26** physical-placement/front/rear orientations; the 6 and 7 cases share a test using only their common ordinary pegs. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticNoHole.lean) checks the quartic moment rigidity, genuine two-column affine residual identity and pivot, paid terminal weight equality, and cardinal gate on Lean/Mathlib 4.36.0. The tableau saturation bridge and exact finite arithmetic are source-level.
