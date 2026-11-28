# Actual ordinarily silent second: regular arithmetic front and ordinary arithmetic rear

This excludes strict ten-stage SDIRK8 over every characteristic-zero field in the following chart. Physical first is ordinarily silent and is the sole nonzero quadratic-defect row. There are eight ordinary active clocks, all distinct. The other ordinarily silent physical row is **second**, with its own nonzero reverse read at a distinct ninth clock. The [nine-site reverse numerator is constant nonzero](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md); the profile is a genuine mixed quintic with both early quartic evaluations and the regular fourth-anchor factor nonzero. The literal front and the ordinary rear are both arithmetic. Physical third/fourth/fifth and the unrestricted **10–11** stage interval are separate.

## Literal second cannot be exchanged with third

Put \(2t^2=1\), \(a=\gamma(2+2t)\), \(b=\gamma(3+4t)\), \(q=\gamma s\), \(x=1-\gamma\), \(c=x-\gamma u\), \(d=x-2\gamma u\). The actual silent clock is \(z=a\). Unlike the star front, the actual normalized coupling \(A'_{32}=(1+6t)/2\) cannot vanish: \((1+6t)(1-6t)=-17\). The exchange of physical stages 2 and 3 inverts that nonzero coupling and fails strict lower triangularity. Conjugating \(t\) is only a field orientation and swaps no physical stage. The [native scalar module](../../lean/RKCert/ReviewedNative/SDIRK8ArithmeticLiteralSecondGates.lean) checks nonvanishing over characteristic-zero commutative rings separately from the full chart.

Let \(H\) denote the mixed quintic in homogeneous form, a nonzero actual multiple of the cubic-defect profile. Write
\[
 k=1+2u-u^2,\qquad H_{\rm r}=-2+u+4u^2-u^3,\qquad
 J_{\rm r}=2+3u-12u^2+4u^3.
\]
The [regular arithmetic rear and affine reads](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md#rear-arithmetic-exact-nested-resultant-projections) imply
\[
 H_{\rm r}H(d)+2J_{\rm r}H(c)-kJ_{\rm r}H(x)=0,\qquad
 (x-z)H(c)-k(c-z)H(x)=0 .
\]
Their exactly normalized polynomials \(F(u),G(u)\) have degree six and four, respectively. The only divisions here are \(u^2\) and \(u\), respectively, and one copy each of \(\gamma,L_4(a),L_4(b)\); \(\gamma\ne0\) is strictness and \(u\ne0\) is distinct ordinary tail sites. No \(u-1\) or \(u-2\) guard is used.

The five true ordinary pegs for the raw nodal determinant are \(b,q,x,c,d\), **not** \(z\). The exact model divides its homogeneous determinant by \(\gamma^5 L_4(a)^4 L_4(b)^4 V_0\), where \(V_0\ne0\) is the normalized regular fourth anchor. The result is \(N(u)\), of degree eight. After taking \(\operatorname{Res}_u(F,G)\) and \(\operatorname{Res}_u(G,N)\), the exact arithmetic divides only \(\gamma^{14}\) and the normalized leading quintic coefficient in the first, and \(\gamma^{25}V_0\), three copies of that same coefficient and four copies of the normalized terminal value \(H(x)\) in the second. The leading coefficient is nonzero by genuine quintic degree, and \(H(x)\ne0\) follows because \(x\) is an ordinary site of the nonzero constant-numerator chart. All factors are removed in characteristic zero, not by observing their residues. The resulting necessary polynomials \(D,E\) have bidegrees \((s,\gamma)=(27,96),(45,136)\).

## Exact projection and guarded factor cover

The full coefficient \(\operatorname{Res}_s(D,E)\) in the integral basis \(1,2t\), with \((2t)^2=2\), has cap **7992**, exact degree **7992**, and exact common strict-diagonal valuation **1284**. A coefficient norm using \(\lvert a\rvert+2\lvert b\rvert\) gives a 27896-bit determinant coefficient bound. All **465** split CRT primes preserve the input \(s\)-degrees; at the first prime both geometric images are independently checked with the complete ordinary interpolation. A separate split prime at \(p=65537\) verifies the oriented image. Removing the strict-diagonal power and common content gives \(C+2tD_0\), of degree 6708, whose rational norm \(C^2-2D_0^2\) has degree 13416.

Proposals are obtained from the exact leading supports and the three smaller guard resultants (regular anchor, quintic leading coefficient, terminal \(H(x)\)). Those are **not** extra equations imposed on the actual fourth clock. The complete rational norm is verified as the product of ten selected rational powers and an integer quotient of degree **8142**. The code does not materialize a huge rational norm square. It reconstructs that quotient from the full numerator's modular polynomial divisions with zero remainder and retained product degree. If \(P\) is the whole proposed product, \(Q\) the reconstructed quotient and \(M\) the full CRT modulus, the whole coefficient identity is certified by
\[
 M>\|C\|_1^2+2\|D_0\|_1^2+
      \bigl(\prod_i\|P_i\|_1^{e_i}\bigr)\|Q\|_1 .
\]
Here 799 complete modular divisions give a 47941-bit modulus compared with a 47896-bit coefficient difference bound. Every difference coefficient is zero modulo \(M\) and has absolute value less than \(M\). No partial quotient or sample-root count is used.

| Norm factor degree | Power | Checked oriented degree | Exact fourth support removed | Complete residue outcome |
|---:|---:|---:|:---|:---|
| 2 | 130 | 1 | none | actual literal clock collision |
| 6 | 8 | 3 | quintic leading, degree 1 | 3 no fourth |
| 2 | 6 | 1 | none | actual literal clock collision |
| 2 | 7 | 1 | anchor, degree 3 | 1 no fourth |
| 2 | 3 | 1 | none | 2 no gap |
| 8 | 4 | 4 | anchor, degree 3 | 3 no fourth |
| 20 | 3 | 10 | anchor, degree 3 | 2 no fourth |
| 42 | 108 | 21 | anchor, degree 9 | 4 no fourth |
| 92 | 3 | 46 | terminal value, degree 3 | 3 no fourth |
| 10 | 3 | 5 | terminal value, degree 3 | 3 no fourth |

For a rational piece, the proposed oriented factor must divide that piece exactly over \(\mathbb Q(t)\); its full monic complement is checked coprime to the actual oriented resultant at the chosen split place, with its entire leading degree retained. A removed fourth factor must divide an exact necessary fourth equation and a power of an actual nonzero guard. Any candidate in an exact oriented algebra therefore satisfies the remaining fourth equation. The two exact collision tests give vanishing of the product of actual nonzero \(\gamma,L_4(a),L_4(b),x-a,x-b\) there. These checks do not turn an accidental residue-leading drop into nonexistence.

## Three true pegs retain the actual ordinary fifth

Only ordinary moment precision **seven** is used. Write \(W_P(X)=I_Y((P(X)-P(Y))/(X-Y))\), where \(I_Y(Y^j)=1/(j+1)\). The monic ordinary nodal \(D_8\) satisfies \(H W_{D_8}-D_8W_H=\lambda\ne0\). In particular \(\gcd(H,W_H)=1\) and \(H\) is nonzero at every ordinary site. The three fixed ordinary pegs are \(E_3=(X-b)(X-q)(X-x)\), and the three paid \(H\)-moments give \(W_{H E_3}=E_3 W_H\).

For \(F'=E_3 R'\) of degree at most seven, its read \(H W_{F'}-F'W_H\) has degree at most four. Indeed, in the moment Laurent expansion, the negative part of \(H\sum_j I_Y(Y^j)X^{-j-1}\) starts at \(X^{-4}\), and the negative part for \(F'\) starts at \(X^{-1}\). The four coefficient conditions at \(X^1,\ldots,X^4\) therefore force a constant read. If that constant is zero, coprimality and the three peg units force \(H E_3\mid F'\), violating degree unless \(F'=0\). The nonzero \(D_8-(H/H_5)E_3\), where \(H_5=[X^5]H\), lies in the subspace. Thus the signed column cofactors give a nonzero polynomial \(R_0\) spanning its unique line after division by \(E_3\). The five-peg determinant above consequently vanishes on the actual five pegs.

In particular \(R_0(c)H(d)-R_0(d)H(c)=0\). The two paid tail reads also give
\[
 H_{\rm r}(c-z)R_0(d)+J_{\rm r}(d-z)R_0(c)=0,
\]
by clearing and cancelling only \(kH(x)\ne0\). The native Lean scalar gate checks this implication over commutative domains. Both \(u\)-padded divisions are made before any residue specialization. The polynomial \(H(c)R_0(X)-R_0(c)H(X)\) is a true nonzero scalar multiple of \(D_8/E_3\). Its two roots \(c,d\) are divided synthetically. The **divided** cross ensures the second synthetic identity still holds even if \(c,d\) merge at the selected place. The resulting cubic contains the **actual ordinary physical fifth**. That fifth must also satisfy the prior [arithmetic literal fifth cubic](../sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-regular-closed/README.md#actual-fifth-separately-for-its-two-physical-roles) at \(Y=c_5/\gamma\), whose derivation uses the actual arithmetic \(A'_{32}\), not a star swap. The only needed use of the fifth chronology is this paid cubic. Neither any later free tap nor an invertible backward tail matrix is assumed.

All finite local claims come from a degree-retaining input at each level \(s,u\), followed by checked synthetic deletion and unit polynomial remainder operations. A hypothetical characteristic-zero root is integral at the selected split place successively over the monic input at each level (after inverting the verified leading unit). Hence it maps into some residue component; no reduction of arbitrary unknown tableau coefficients is assumed. For the exact large quotient, the split-place orientation retains degree 4071 in 21 complete components. Their full retained fourth fibres give 23 no-gap outcomes and 5 no-actual-ordinary-fifth outcomes. No assertion is made when a remaining fourth, gap or missing-nodal leading unit fails to pay for that component.

## Replay

Install `sympy==1.14.0` and `python-flint==0.9.0`, then run `python3 check_arithmetic_arithmetic2.py` next to the declared sibling directories. The optional pinned LP64 FLINT 3.6.0 geometric backend falls back to the ordinary interpolator if unavailable; `RK_DISABLE_FAST_CRT=1` also selects the slow backend. Set `RK_ARITHMETIC_SCRATCH` to an existing disk directory with at least 180 MiB free if needed. The default replay generates its own scratch journal in a fresh temporary directory and trusts no precomputed checkpoint or factor table. The two native scalar lemmas were checked on Lean/Mathlib 4.36.0; the exact source-level diagonal and local arithmetic below them is not an end-to-end Lean proof.
