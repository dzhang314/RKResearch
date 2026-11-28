# Regular corrected ordinary hole5, star front and arithmetic rear, actual silent 2 or 3

This excludes precisely the two literal ordinarily silent positions \(\zeta=2,3\) with **star front, ordinarily weighted arithmetic rear**, in the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over characteristic-zero fields. There are ten strict SDIRK8 stages, with only first quadratic defect and ordinarily and reversely silent first. Eight ordinary physical clocks are distinct, and one other ordinarily silent physical row is reverse-live at a separate ninth clock. The affine \(T\) and genuine quintic \(S\) share the ordinary fifth clock \(r=c_5\), where actual amplitude is zero but the continued quartic \(H=(S/T)/\gamma^3\) has \(H(r)\ne0\). Here the actual two-early-literal anchor determinant \(\Delta\ne0\); the [complete rank-loss packet](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-rank-closed/README.md) is separate. No ordering is used.

## Independent actual front and rear projections

Write \(Y=r/\gamma,\ s=c_4/\gamma,\ a=\gamma A,b=\gamma B\), and \(x=c_{10}=1-\gamma,\ c=c_9=x-\gamma u,\ d=c_8=x-2\gamma u,\ k=1+2u-u^2\). The full-rank actual early amplitudes give the homogeneous corrected quartic \(H_N=\alpha_N L_4+\beta_N K_3(\,\cdot\,,r)=\Delta H\). Its exact front relations are
\[
 J(\gamma,Y,s)=\frac{\Delta H_4(s)-H_N(\gamma s)}{(s-A)(s-B)}=0,\qquad
 \Psi(s,Y)=0 .
\]
The first uses true fourth, which is ordinary and not the hole. The second is the [actual h5=0 literal determinant](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-rank-closed/README.md#a-literal-polynomial-at-the-actual-zero-fifth-with-no-fake-fifth-pads). Its only polynomial pad divisions are in the earlier fourth variable \(s\), not fake fifth powers in \(Y\). For star front \(\Psi\) is linear in \(s\) and quartic in \(Y\). The exact padded \(\operatorname{Res}_s(J,\Psi)\) has bidegree \((11,10)\) in \((Y,\gamma)\); divide only the true nonzero \(\gamma\), leaving \(P\) of bidegree \((11,9)\).

The fixed arithmetic ordinary rear uses \(H_N\) at the true nonhole sites \(c,d,x\). With \(z=a\) or \(b\) the actual additionally silent clock,
\[
 \begin{split}
 H_{\rm r}(u)H_N(d)+2J_{\rm r}(u)H_N(c)-kJ_{\rm r}(u)H_N(x)&=0,\\
 (x-z)H_N(c)-k(c-z)H_N(x)&=0 ,
 \end{split}
\]
with \(H_{\rm r}=-2+u+4u^2-u^3,\ J_{\rm r}=2+3u-12u^2+4u^3\). The exact divisions by \(u^2,u\) give \(F,G\), respectively. No different ordinary-hole chronology or nonzero assumption on either arithmetic rear coefficient is used. The exact \(\operatorname{Res}_u(F,G)\) has bidegree \((24,85)\) in \((Y,\gamma)\); divide only \(\gamma^7\alpha_N\), leaving \(Q\) of bidegree \((21,72)\). The factor \(\alpha_N\ne0\) is true by the genuine quartic degree and \(\Delta\ne0\).

The outer padded \(\operatorname{Res}_Y(P,Q)\) has exact degree 897 in each actual silent orientation. Divide only \(\gamma^{84}\beta_N^{21}\), where \(\beta_N=\Delta b_r H(r)\ne0\) by correction and rank-two hypotheses. The full retained monic diagonal degree is **729**. All resultants are exact bounded split-prime CRT computations with their formal Sylvester shapes, not reductions at assumed generic powers. The necessary common-root projections apply even at an actual leading coefficient drop.

## True five-peg signed and terminal rows

The five true ordinary nonhole pegs are the *other* literal early clock, plus \(q=c_4,x,c,d\). They omit both the additional ordinarily silent row and ordinary hole at actual fifth. Their nodal \(E_5\) gives \(D_7=E_5R_2\) with \(R_2\) a monic quadratic whose roots are actual ordinary 6 and 7. Apply the [denominator-cleared signed coefficient rows](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs) for \(I_\#=H_N(r)I-\beta_N\operatorname{ev}_r\). The rows of nonconstant coefficients in \(H_N W_{X^jE_5}^{I_\#}-X^j E_5 W_{H_N}^{I_\#}\), \(0\le j\le2\), annihilate the true monic quadratic. The paid actual \(b_9=b_{10}\ne0\) supplies the fourth row
\[
 H_N(c)E_5'(c)c^j-H_N(x)E_5'(x)x^j .
\]
The four \(3\times3\) minors are all necessary zeros. No Cramer inverse, ordinary derivative inverse, or signed-mass inverse is used in the final test.

Use the full monic diagonal reductions at \((1129,t=203)\). In every degree-preserving reduced factor, at least one of \(P,Q\) retains its full leading unit, and their **whole** \(Y\)-gcd is retained. The same leading-unit rule is checked for \(J,\Psi\) and \(F,G\), with their complete respective \(s,u\) gcds. This includes multiple \(s\) roots where they occur. The four minors generate a unit on all **21 and 20** complete reduced diagonal components, with their multiplicities. The finite localization lift rules out characteristic-zero points without assuming actual tableau good reduction.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole5_star_arithmetic_literal.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared sibling proofs. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleFiveRegularLiteral.lean) verifies the exact two-literal homogeneous profile identity on Lean/Mathlib 4.36.0, alongside the already checked true literal zero-fifth and signed terminal gates. The finite arithmetic is source-level. Ordinary star rear, arithmetic front, other regularly silent placements and other ordinary holes are separate. The unrestricted **10–11** interval is unchanged.
