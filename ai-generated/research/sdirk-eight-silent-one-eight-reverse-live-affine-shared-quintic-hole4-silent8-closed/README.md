# Corrected ordinary fourth hole with actually silent eighth

This excludes both literal front phases of the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) with **ordinary hole at physical fourth and actually silent physical eighth** over characteristic-zero fields. The method is strict ten-stage SDIRK8. Physical one alone has nonzero quadratic defect and is ordinarily and reversely silent. Eight ordinary rows have distinct clocks, and ordinarily silent physical eighth has nonzero reverse read at its distinct ninth clock \(z\). The degree-one reverse numerator \(T\) shares its sole root \(r=c_4\) with genuine quintic \(S\). Stage four has nonzero ordinary weight and actual cubic-defect amplitude zero, but the continued quartic \(H=(S/T)/\gamma^3\) has \(H(r)\ne0\). No ordering is used. There is no ordinary-eighth star/arithmetic rear split in this placement.

## Four ordinary nonhole pegs give a signed monic-cubic determinant

Write \(r=\gamma s\). Here \(J=H_4(s)\) up to nonzero scalar is the true monic cubic, since actual fourth amplitude is zero. The two-front determinant \(\Delta\ne0\) follows from the complete rank-loss proof at physical hole four. Use its homogeneous \(H_N=\alpha_N L_4+\beta_N K_3(\,\cdot\,,r)\), with \(H=H_N/\Delta\). On nonhole ordinary pegs the normalized amplitudes agree with \(H\). Put \(h_r=H_N(r)\ne0\) and \(I_\#=h_r I-\beta_N\operatorname{ev}_r\); no polynomial profile value is assigned at the ordinary hole.

Let \(a=c_2,b=c_3,x=c_{10}=1-\gamma,c=c_9=x-\gamma u\), the four known ordinary nonhole pegs, and \(E=(X-a)(X-b)(X-x)(X-c)\). The seven nonhole ordinary nodes have \(D_7=E R\) with \(R\) monic cubic, whose roots are actual ordinary 5, 6, 7. The [signed coefficient argument](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md) supplies the three rows \([X^1],[X^2],[X^3]\) of
\[
 \mathcal B(X^jE)=H_N W_{X^jE}^{I_\#}-X^jE W_{H_N}^{I_\#},
 \qquad 0\le j\le3.
\]
They annihilate the four coefficients of the true monic \(R\). This uses scalar precision seven, never a signed-mass inverse or a generic cofactor pivot.

Let \(k=1+2u-u^2\), so \(z=x+\gamma k(u-2)/2\) by actual silent-eighth chronology, and put \(\varphi=2u+k(u-2)\). The actual tail gives \((u-2)H_N(c)=\varphi H_N(x)\). Its exact \(u\) division gives \(F\) of degrees \((4,3,10)\) in \((u,s,\gamma)\). Independently \(b_9=b_{10}\ne0\) gives \(H_N(c)E'(c)R(c)=H_N(x)E'(x)R(x)\). Combine it with the tail equality and cancel only the actual nonzero \(\gamma u H_N(x)\). The fourth row has entries
\[
 \varphi(c-a)(c-b)c^j+(u-2)(x-a)(x-b)x^j,\qquad 0\le j\le3.
\]
Neither \(u-2\) nor the silent amplitude is divided out in this step. The four signed/terminal rows share the true monic-cubic kernel, so their determinant \(P\) must vanish without a Cramer assumption.

## Exact projections with only true nonzero factors

The raw determinant has exact \((u,s,\gamma)\)-degrees \((11,30,65)\). Its signed rows contain a structural \(h_r^2\): after subtracting \(r\) times the preceding columns, each shifted signed column is a multiple of \(h_r\), and a term expanded along the terminal row uses at least two such columns. In the exact coefficient ring the source divides only
\[
 \gamma^3\alpha_N \left(\frac{h_r}{\gamma}\right)^2\left(\frac{\Delta}{\gamma}\right).
\]
Both quotients by \(\gamma\) are exact polynomials. These are all genuinely nonzero at the true tableau: nonagreement, genuine quartic degree and already excluded early rank loss justify them. In particular \(\Delta/\gamma\) is not discarded based on a reduced Cramer failure. The retained \(N\) has degrees \((11,10,29)\).

The padded \(\operatorname{Res}_u(F,N)\) from exact bounded split CRT has degrees \((73,226)\) in \((s,\gamma)\). Its only further division is \(\gamma^{16}\alpha_N^2H_N(x)^3\), justified by the true nonzero terminal amplitude and the preceding guards. The retained \(R_0\) has degrees \((58,168)\). With the full true fourth cubic \(J\), its resultant gives the full monic diagonal of exact degree **504** for each front type. No specialization leading assumption is used in these resultant implications at actual unknown points.

## Reconstruct the actual ordinary fifth, with only two literal pads

After the exact projections, use \(I_r=I-(\beta_N/h_r)\operatorname{ev}_r\) and the monic normalization \(Q\) of \(H_N\). The true signed identity \(QW_{D_7}^{I_r}-D_7W_Q^{I_r}=\lambda\ne0\) yields \(D_7=Q U_3+\rho V\), where \(U_3\) is a monic cubic and \(V=(W_Q^{I_r})^{-1}\bmod Q\). The four known ordinary nonhole pegs give the fixed four-row Cramer system, with an actual determinant checked as a unit only **after** finite projection. Dividing reconstructed \(D_7\) by those four pegs gives the monic cubic containing the actual ordinary fifth, without selecting any of its roots.

The true literal rows 2–5 determinant uses \(\boldsymbol h,C\boldsymbol h,A\boldsymbol h,\boldsymbol\tau_4\) with actual fourth amplitude **zero** and prospective fifth \(H_N(\gamma Y)/\Delta\). The exact pads \(Y-A,Y-B\) are canceled, leaving degree at most three. Do **not** cancel \(Y-s\): the nonzero continued profile at \(r=\gamma s\) is not the actual zero fourth amplitude. No distinctness from physical first is assumed. The full multiplication determinant of this literal fifth polynomial on the normalized missing monic cubic is a unit, excluding any actual ordinary fifth root. This test does not assign physical sixth or seventh.

## Complete replay

At \((1129,t=203)\) every reduced factor of each full monic diagonal is kept, with its full fourth and gap gcd. The monic fourth cubic and full leading \(F\) are retained, and no reduced collision is removed. The signed normalization, actual mass, modular inverse and fixed four-peg solve all check as units in the complete finite algebras. The literal fifth multiplication determinant is a unit in all **28 star-front and 10 arithmetic-front components**. The standard lift over the finite localized coefficient ring excludes all characteristic-zero points without presuming good reduction of a hidden tableau.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole4_silent8.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared sibling proofs. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleFourthSilentEight.lean) verifies the reduced terminal row, the monic-cubic determinant and the two literal pad cancellations on Lean/Mathlib 4.36.0. The saturation bridge and exact finite replay remain source-level.

Together with [actual silent 2 or 3](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) and [actual silent 5, 6 or 7](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md), this closes all placements with **ordinary hole at physical four** in the scoped nonagreement chart; actual silent four cannot coincide physically with an ordinary four. It does not cover other ordinary-hole positions, other numerators, or other support patterns. The unrestricted **10–11** interval is unchanged.
