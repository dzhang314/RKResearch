# Sole genuinely nonliteral fifth transport, arithmetic rear

This excludes the remaining active-arithmetic-eighth case of sole nonliteral transport at actual physical fifth. The hypotheses are ten-stage strict SDIRK8 over a characteristic-zero field, only the first physical weight-zero stage has nonzero quadratic residual, detected cubic defect, seven distinct ordinary active clocks, one ordinary active literal, \(k\ne0\), and a coprime nonconstant affine active profile. The case with active star eighth is [separately closed](../sdirk-eight-silent-one-seven-distinct-coprime-nonliteral-fifth-star/README.md). Stages six through eight as the sole actual nonliteral transport are not included. The global **10–11** interval is unchanged.

Use the honest ordinary \(a,s\) two-anchor \(Q,P\) and literal fifth cubic equations \(E_T,E_A,D\) as in the star packet. The ordinary fourth \(s\) may equal the other literal silent clock \(b\); no condition \(s-b\ne0\) enters. The virtual fifth amplitude at \(z=\gamma y\), being carried by this sole physical stage, equals its actual amplitude and **may be zero**. The actual \(L_4(z)\) is not inverted or declared nonzero.

## Exact arithmetic rear and already active nodal pegs

Write \(q(X)=\gamma Q(X/\gamma)\), \(x=1-\gamma,\ c=x-\gamma u,\ d=x-2\gamma u\), and \(L_v=L_4(v),q_v=q(v)\). Let \(H=-2+u+4u^2-u^3,\ T=4u^3-12u^2+3u+2,\ k=1+2u-u^2\). With \(\delta=\gamma u,\ w=x-z\), the actual ninth and eighth relations are
\[
(q_x L_c-k q_cL_x)w+\delta k q_cL_x=0,\qquad
(Hq_xL_d+kTq_dL_x)w-2\delta kTq_dL_x=0.
\]
Cross them and cancel the genuine nonzero \(\delta kL_x\). The result
\[
 H q_xq_c L_d+2Tq_xq_d L_c-kTq_cq_d L_x=0
\]
contains neither actual \(y\) nor \(z\); no assumption on the transported cubic amplitude was used. The [native cross lemma](../../lean/RKCert/ReviewedNative/SDIRK8ArithmeticFifth.lean) gives this cancellation.

After exact physical guard factors this gives \(E(\gamma,s,u)\) of \(u\)-degree five. The actual five ordinary pegs \(\gamma a,\gamma s,x,c,d\), **not** the fifth silent, give the pole-free nodal determinant \(N(\gamma,s,u)\) of \(u\)-degree six. It is an exact necessary equation by the [paid rational Bézout identity](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) and ordinary nodal interpolation. In the residue proof positions remain physical; no merged or coincident reduced pegs are deleted.

Reconstruct \(\operatorname{Res}_u(E,N)\) exactly by bivariate, split-prime CRT, using the determinant height bound \((5+6)!\lVert E'\rVert^6\lVert N'\rVert^5\) for integral inputs in the \(1,\sqrt2\) basis. Verify an independent full reduction at \((1103,161)\). Its \((s,\gamma)\) degrees are \((81,189)\). Exact source divisions remove thirteen \(\gamma\) factors, two \(L_4(\gamma a)\), seven \(L_4(\gamma s)\), and two copies of the remaining homogeneous affine Gauss-resultant guard, leaving \(B(\gamma,s)\) of degrees \((37,116)\). For the last guard use \(q_1^4 L_4(-q_0/q_1)\), where the actual affine slope \(q_1\ne0\). Divide its explicit active-anchor factors from itself first because those factors are already nonzero. The remaining guard is nonzero because \(q,L_4\) are coprime. These divisions are exact in the polynomials in \((\gamma,s)\), not decisions made on finite residue zeros. They remove no other \(s\) at the same diagonal and do not guard \(L_4(z)\).

The original-field guards behind those exact divisions are \(\gamma\ne0\) from strictness; \(s-a\ne0\) and \(u\ne0\) from actual distinct ordinary active nodes; and nonvanishing \(q,L_4,H_4(s)\) as applicable at the ordinary anchors from the [coprime active profile classification](../sdirk-eight-silent-one-seven-distinct-anchors/README.md#classification-of-every-active-scalar-h-profile). In particular \(\gamma a,\gamma s\) are ordinary nodes even if \(s=b\), so both stripped Legendre factors are nonzero in the original field. Finally \(q_1\ne0\) and \(q,L_4\) coprime imply the actual \(q_1^4L_4(-q_0/q_1)\ne0\). Removing already nonzero anchor factors from this homogeneous polynomial preserves that nonzero value. No nonzero condition is placed on \(L_4(z)\).

## Complete monic residual check

The [two-anchor front](../sdirk-eight-silent-one-seven-distinct-coprime-nonliteral-fifth-star/README.md) gives \(J(\gamma,s)\) with actual fifth a common root of \(E_T,D\); its degree in \(s\) is \(16/17\) and in \(\gamma\) is 12. The exact outer diagonal is \(G=\operatorname{Res}_s(J,B)\). Its degree is bounded by \(116\deg_s J+37\cdot12\). At \((1103,161)\) the **entire** reduced resultant attains that bound, \(2300/2416\) in the two literal front types. Thus its exact degree and residue-leading unit follow without a huge independent reconstruction of its characteristic-zero coefficients.

The checker retains every factor of this reduced diagonal. At each \(\gamma\)-factor at least one nominal fourth lead survives; impose \(J=B=0\) in the resulting monic \(s\)-algebra. At every retained \(s\), either the actual nominal quintic \(E\) or sextic \(N\) has nonzero lead, so take the full common-root monic \(u\)-algebra. These checks license integrality and finite reduction of \(\gamma,s,u\). We need not assume the actual \(y\) is integral. Put
\[
 A=q_x L_c-kq_cL_x,\qquad B_9=\gamma u kq_cL_x .
\]
The genuine \(B_9\ne0\), so the ninth read gives \(A\ne0\) and \(\gamma A y=xA+B_9\). Evaluate the three necessary fifth polynomials homogeneously at numerator \(xA+B_9\) and denominator \(\gamma A\). Their scalar values must vanish and are integral in the prior monic algebras. No denominator is inverted after reduction, and simultaneous reduced zeros of numerator and denominator are **not** automatically discarded. The actual homogeneous residuals generate a unit in every retained component; this excludes the arithmetic chart. The same native file verifies homogeneous cubic substitution over a commutative ring. Concrete diagonal and fiber arithmetic is source-level.

Replay with `python3 check_nonliteral_fifth_arithmetic.py` in the sibling research tree, using `sympy==1.14.0` and `python-flint==0.9.0`. It uses the star packet's literal front and the earlier fourth/nodal helpers. All exact bivariate coefficients are rebuilt; no private caches. The native lemmas were kernel-checked on Lean/Mathlib 4.36.0.
