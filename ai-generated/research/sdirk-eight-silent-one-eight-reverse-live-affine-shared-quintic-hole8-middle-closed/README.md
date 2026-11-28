# Corrected ordinary hole8, actually silent fifth, sixth or seventh

This excludes all three nonliteral silent placements in both literal front phases of the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over characteristic-zero fields. There are ten strict SDIRK8 stages. Physical one alone has nonzero quadratic defect and is ordinarily and reversely silent. Eight ordinary nodes have distinct clocks, and one further ordinarily silent row \(\zeta\in\{5,6,7\}\) has actual nonzero reverse read at a separate ninth clock. The affine reverse numerator \(T\) and genuine quintic \(S\) share the sole root \(r=c_8\) of \(T\). Physical eight is ordinary with actual \(h(r)=0\), but its continued quartic \(H=(S/T)/\gamma^3\) has \(H(r)\ne0\). See the [placement ledger](HOLE8-PLACEMENTS.md) for the complete ordinary-hole8 scope. The unrestricted **10–11** interval remains unchanged.

## True fixed arithmetic rear and signed coefficient kernel

The [literal ordinary-hole8 companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole8-literal-closed/README.md) gives the true fixed arithmetic gap \(F=J_{\rm r}/4\) with \(J_{\rm r}=2+3u-12u^2+4u^3\), \(x=1-\gamma,\ c=x-\gamma u,\ r=x-2\gamma u\). The star rear is impossible. Actual rank loss at the two early ordinary clocks was excluded there without substituting a continued amplitude at the hole. Use \(H_N=\alpha_N L_4+\beta_N K_3(\,\cdot\,,r)\), with \(H=H_N/\Delta\) and true \(\Delta\ne0\), and the genuine padded fourth equation \(J(\gamma,u,s)=0\) at \(q=\gamma s=c_4\). The fourth equation has degrees \((3,2,10)\) in \((u,s,\gamma)\) and comes from the two actual nonzero factors \(s-A,s-B\).

The five ordinary nonhole pegs here are **\(a,b,q,x,c\)**, with neither \(r\) nor the normally silent clock included. Their nodal \(E_5\) gives \(D_7=E_5 R\) where \(R\) is monic quadratic. Its two roots are the ordinary clocks remaining among physical 5, 6, 7, different physical choices for the three placements. We do not identify them at this step.

As in the [five-peg signed proof](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs), use \(h_r=H_N(r)\) and the denominator-cleared \(I_\#=h_r I-\beta_N\operatorname{ev}_r\). It is a true degree-seven functional on the seven ordinary nonhole nodes after its common scale. For \(D_j=X^jE_5,\ 0\le j\le2\), define
\[
 B_j=H_N W_{D_j}^{I_\#}-D_j W_{H_N}^{I_\#}.
\]
All degrees are at most three from signed quartic orthogonality. Since the corresponding expression on \(D_7\) is constant, the rows \([X^1],[X^2],[X^3]\) of \(B_j\) annihilate the coefficients of the monic quadratic \(R\). Their \(3\times3\) determinant \(P\) is therefore zero before any solve or pivot.

## Exact factors, with unit policy

The raw signed \(P\) has degrees \((33,3,63)\) in \((u,s,\gamma)\). The two consecutive shifted columns for \((X-r)E_5\) and \((X-r)X E_5\) give the structural \(h_r^2\) factor, as in the earlier signed proof. There is also a genuine \(\Delta/\gamma\) factor. Indeed \(B_j(a),B_j(b)\) are multiples of \(\Delta\): \(D_j\) vanishes at the actual pegs, while \(H_N(a)=\Delta H_a,\ H_N(b)=\Delta H_b\). Subtract the two peg evaluations. Writing \(p_{ij}=[X^i]B_j\), this gives
\[
 (a-b)\bigl(p_{1j}+(a+b)p_{2j}+(a^2+ab+b^2)p_{3j}\bigr)=\Delta t_j .
\]
Replace the first signed row by the indicated combination, then scale it by \(a-b=\gamma(A-B)\). Multilinearity gives \((a-b)P=\Delta\widetilde P\) over the full polynomial coefficient domain. The source verifies the exact \(\Delta/\gamma\) quotient and all divisions directly, not by suppressing a failed modular pivot.

Divide from \(P\) only \(\alpha_N h_r^2(\Delta/\gamma)\). All three are nonzero in the original problem: \(\alpha_N\ne0\) by genuine quartic degree, \(h_r\ne0\) by nonagreement, and \(\Delta/\gamma\ne0\) by the proved early rank case and strict diagonal. The retained \(N\) has degrees \((13,3,28)\). The padded exact \(\operatorname{Res}_s(J,N)\) has degrees \((35,86)\) in \((u,\gamma)\). Divide only \(\gamma^6\alpha_N(\Delta/\gamma)^2\) to get the necessary \(R_0\) of degrees \((26,56)\). The exact resultant \(\operatorname{Res}_u(F,R_0)\) gives the **full degree-168 monic diagonal** in each front phase, with no further factor removed. Both resultants use complete degree-preserving bounded split CRT. The padded identities retain all actual leading-degree drops.

## Independent equal-terminal-weight row

The actual paid backward equality \(b_9=b_{10}\ne0\) together with the genuine constant nodewise deflation gives
\[
 H_N(c)D'_7(c)=H_N(x)D'_7(x).
\]
At a known peg \(D'_7(c)=E_5'(c)R(c)\), likewise at \(x\). Append the row \(H_N(c)E_5'(c)c^j-H_N(x)E_5'(x)x^j\) for \(j=0,1,2\). The four \(3\times3\) minors of the resulting four-row matrix must all vanish. This is a common necessary condition **before** the different actual fifth, sixth or seventh assignments. It proves each physical placement separately without assigning an ordinary fifth when fifth is normally silent.

At \((1129,t=203)\) the full monic diagonal and all its reduced factors are used, **28** for the star front and **17** for the arithmetic front. Each keeps the complete gap gcd of \(F,R_0\) and the whole fourth quadratic with a checked leading unit. The four minors jointly generate a unit on every complete algebra; no inverse of the signed mass, Cramer determinant, or actual ordinary nodal derivative is used in the final certificate. The finite localization argument lifts these checks without assuming good reduction of an unknown tableau. The 45 components are counted once, not once per silent placement.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole8_middle.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared sibling proofs. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleEightMiddle.lean) verifies the two-peg difference and exact signed front-determinant factor over arbitrary commutative rings; the existing signed and terminal minors are checked in the [hole4 middle native receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleMiddle.lean). Verification used Lean/Mathlib 4.36.0. The full saturation and exact finite arithmetic are source-level, and this tableau exclusion is characteristic zero.
