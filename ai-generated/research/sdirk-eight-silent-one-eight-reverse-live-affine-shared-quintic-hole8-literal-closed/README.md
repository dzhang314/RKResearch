# Corrected ordinary eighth hole, actually silent literal 2, 3 or 4

This excludes the three literal normally silent placements in both front phases of the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over characteristic-zero fields. There are ten strict SDIRK8 stages. Physical one alone has a nonzero quadratic defect and is ordinarily and reversely silent. Eight ordinarily weighted physical rows have distinct clocks; one other ordinarily silent row \(\zeta\in\{2,3,4\}\) has nonzero reverse read at its distinct ninth clock \(z\). The degree-one reverse numerator \(T\) and genuine quintic \(S\) share the sole root \(r=c_8\) of \(T\). Thus physical eight has nonzero ordinary weight and zero actual reverse read and cubic-defect amplitude. Its continued quartic \(H=(S/T)/\gamma^3\) has \(H(r)\ne0\). No ordering is used.

## Fixed true arithmetic gap and actual fourth

Use actual \(x=c_{10}=1-\gamma,\ c=c_9=x-\gamma u,\ k=1+2u-u^2\). By the [ordinary-hole rank packet](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md#corrected-kernel-and-genuine-early-rank-loss), the ordinary star rear is impossible using the actual zero eighth amplitude. In the arithmetic rear, the same fact forces
\[
 J_{\rm r}(u)=2+3u-12u^2+4u^3=0,\qquad r=x-2\gamma u .
\]
Neither this cubic nor the other almost-diagonal coefficient is divided out. There are no zero-gap, \(k=0\) or \(u=2\) roots of this cubic in characteristic zero. The true front determinant \(\Delta\ne0\) at physical hole8 was already checked on all early rank-loss components. Use its homogeneous quartic \(H_N=\alpha_N L_4+\beta_N K_3(\,\cdot\,,r)\) with \(H=H_N/\Delta\).

The two actual literal early clocks \(a=\gamma A,b=\gamma B\) have their known nonzero amplitudes, regardless of whether one is ordinarily silent. Actual fourth \(q=\gamma s\) is **not** the ordinary hole. Its genuine amplitude \(H_4(s)=H_N(\gamma s)/\Delta\) yields the exact padded equation
\[
 J(\gamma,u,s)=\frac{\Delta H_4(s)-H_N(\gamma s)}{(s-A)(s-B)}=0 .
\]
Only those two factors are divided out, by actual distinctness. Its degrees in \((u,s,\gamma)\) are \((3,2,10)\). No condition that \(H_4(s)\ne0\) is used when physical fourth is normally silent.

For \(\zeta=2\) or \(3\), \(z=a\) or \(b\). The actual penultimate comparison is
\[
 (x-z)H_N(c)-k(c-z)H_N(x)=0 .
\]
Its exact \(u\)-division gives \(N\) of bidegree \((6,11)\) in \((u,\gamma)\), with no additional divided factor. For \(\zeta=4\), \(z=\gamma s\) is its own actual silent clock. Define
\[
 R=\frac{H_N(c)-kH_N(x)}{u},\quad
 n=xR+\gamma k H_N(x),\quad d_0=\gamma R .
\]
The numerator defining \(R\) is exactly divisible by \(u\). The same true penultimate comparison gives \(d_0s=n\), with \(d_0\ne0\); if \(R=0\), it would imply \(\gamma kH_N(x)=0\). Thus one may homogenize the true \(J(\gamma,u,s)=0\) at \((n,d_0)\) without assuming a quadratic leading term. The resulting \((u,\gamma)\)-degrees are \((15,32)\), and only the exact \(\gamma^2\) is divided out, leaving \((15,30)\).

The full padded exact \(\operatorname{Res}_u(J_{\rm r}/4,N)\) has \(\gamma\)-degree **33** for \(\zeta=2,3\) and **90** for \(\zeta=4\). The replay uses bounded split CRT and preserves all formal degrees. No further diagonal factor is removed.

## Corrected signed four-peg solve and the paid penultimate equality

The ordinary hole \(r\) is not a peg in the seven-node \(D_7\). From \(a,b,q,x,c\) omit the actual literal ordinarily silent clock \(z\), leaving **four true ordinary nonhole pegs**. Normalize \(H_N\) to monic \(Q\) of degree four and use the signed functional \(I_r=I-(\beta_N/H_N(r))\operatorname{ev}_r\). As in the companion, cancellation at the nonhole ordinary nodes gives a constant genuine read, and precision seven gives
\[
 Q W_{D_7}^{I_r}-D_7 W_Q^{I_r}=\lambda\ne0 .
\]
Take \(V=(W_Q^{I_r})^{-1}\bmod Q\) with degree less than four. This yields \(D_7=Q U_3+\rho V\) for monic cubic \(U_3\). The four actual ordinary nonhole pegs give the four-row Cramer system for the three lower \(U_3\) coefficients and remainder scale. The system's determinant is checked as a unit over the complete retained algebras; no generic rank claim is needed.

The actual first backward row at physical nine implies \(b_9=b_{10}\ne0\). Cardinal reconstruction in the signed functional gives the division-free equality
\[
 W_{D_7}^{I_r}(c)D'_7(x)-W_{D_7}^{I_r}(x)D'_7(c)=0 .
\]
It is a unit in every full component. No actual fifth or later root is assigned or transported to the ordinary hole.

## Complete replay and scope

At \((1129,t=203)\) the exact monic diagonal bases retain their full degree and every factor. The complete gcd of the fixed arithmetic cubic and its gap projection is retained. For \(\zeta=2,3\) the entire actual fourth polynomial keeps its leading unit, so use the whole quadratic. For \(\zeta=4\) the actual \(d_0\) is a unit in every model; its full recovered fourth satisfies \(J\). The normalizations, signed mass, inverse modulo \(Q\), four-peg determinant and final paid weight residual all check as units. There are **59** components with counts \(9,11,14,9,7,9\). Finiteness over the localized coefficient ring lifts the units before passing to characteristic zero, with no assumed good reduction of an unknown tableau.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole8_literal.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared sibling proofs. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleEightLiteral.lean) verifies the fixed gap exclusions, actual silent fourth recovery with nonzero denominator, and homogeneous fourth equation allowing degree drops. These check on Lean/Mathlib 4.36.0. The saturation and finite replay remain source-level. The actual nonliteral silent stages 5, 6 and 7 and other ordinary hole placements are separate. The unrestricted **10–11** interval is unchanged.
