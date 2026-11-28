# Corrected ordinary hole at fourth, actual silent fifth, sixth or seventh

This excludes the three physical placements \(\zeta=5,6,7\), with each literal front and ordinary-eighth rear phase, in the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over characteristic-zero fields. There are ten strict SDIRK8 physical stages. Physical one alone has nonzero quadratic defect and is ordinarily and reversely silent. Eight ordinary physical rows have distinct clocks; one other ordinarily silent row \(\zeta\) is reverse-live at a distinct ninth clock. The degree-one reverse numerator \(T\) shares its sole root \(r=c_4\) with the genuine quintic \(S\). Stage four is **ordinary**, with true cubic-defect amplitude zero. Its continued quartic \(H=(S/T)/\gamma^3\) has \(H(r)\ne0\). The rank-loss case and both literal ordinarily silent positions 2 or 3 are handled by the companion. Actual silent eighth and other ordinary-hole positions remain separate; the unrestricted **10–11** interval is unchanged.

## Signed polynomial determinant from five true nonhole pegs

Keep \(r=\gamma s\), the actual ordinary fourth, with the fixed monic cubic \(J=0\) from \(H_4(s)=0\). The two literal front readings have nonzero determinant \(\Delta\) by the companion's full rank-loss check at physical hole four. Use the same homogeneous quartic \(H_N=\alpha_N L_4+\beta_N K_3(\,\cdot\,,r)\), with \(H=H_N/\Delta\). In particular \(\alpha_N\ne0\) from the genuine quartic profile and \(h_r:=H_N(r)\ne0\) from nonagreement. No equation replaces the actual zero amplitude at fourth with \(H_N(r)/\Delta\).

The five **ordinary nonhole** pegs \(a=c_2,b=c_3,x=c_{10},c=c_9,d=c_8\) are common to all three placements. Write their monic product \(E_5\). The seven nonhole ordinary nodes have monic nodal \(D_7=E_5 R\), \(R=X^2+r_1X+r_0\). For \(\zeta=5,6,7\) the two roots are the other two ordinary clocks among stages 5, 6 and 7, respectively. They are not assigned to later stages in this argument.

The signed functional \(I_r=I-b_r\operatorname{ev}_r\), \(b_r=\beta_N/h_r\), has precision seven on the nonhole nodes. Use its denominator-cleared form \(I_\#=h_r I-\beta_N\operatorname{ev}_r\). As in the companion, actual deflation at the nonhole sites and cardinal interpolation imply
\[
 \mathcal B(D_7)=H_N W_{D_7}^{I_\#}-D_7 W_{H_N}^{I_\#}
 \quad\text{is a nonzero constant}.
\]
The corrected moments kill \(I_\#(X^j H_N)\) for \(0\le j\le3\). The joined divided difference therefore gives \(\deg\mathcal B(D)\le3\) for any \(D\) of degree at most seven: its first difference has total degree at most six before multiplication by \(H_N(Y)\), and the difference of \(H_N\) has \(X\)-degree at most three. No higher scalar read is used. For \(D_j=X^j E_5,\ j=0,1,2\), the three rows \([X^1],[X^2],[X^3]\) of the three signed coefficient columns \(\mathcal B(D_j)\) annihilate \((r_0,r_1,1)^\mathsf T\). Their determinant \(P\) vanishes without any need for a pivot.

## Exact nonagreement factors and full diagonal models

The determinant has exact degrees \((\deg_u,\deg_s,\deg_\gamma)=(6,30,63)\). It contains a structural \(h_r^2\) factor: subtract \(r\) times the previous column successively (equivalently use \(D_0,(X-r)E_5,(X-r)XE_5\)). For the latter two columns \(D(r)=0\), so the evaluation-at-\(r\) part of their Bézout expression is a multiple of \(h_r\). For example
\[
 H_N W_{(X-r)E}^{\operatorname{ev}_r}
 -(X-r)E W_{H_N}^{\operatorname{ev}_r}=h_r E .
\]
The exact \(\rho=h_r/\gamma\) is polynomial of degrees \((7,9)\) in \((s,\gamma)\), and truly nonzero. From \(P\) divide only \(\gamma^3\alpha_N\rho^2\), verified exactly over the original coefficient field. The retained \(N\) has degrees \((6,13,36)\).

Independently use the true ordinary-eighth shape \(F\) evaluated at actual tail \(x=1-\gamma,\ c=x-\gamma u,\ d\). It uses neither a known literal silent clock nor the false continued value at fourth. The padded \(\operatorname{Res}_u(F,N)\) is computed by bounded, exact split CRT. After only the additional nonzero \(\gamma^{12}\alpha_N^2\) division it has degrees \((s,\gamma)=(38,108)\) in star rear or \((77,216)\) in arithmetic rear. Its resultant with the actual cubic \(J\) gives exact degrees **324** and **648**, respectively, and the full monic diagonals are retained. No degree drop at an actual point is assumed away by the padded resultants.

## Terminal ordinary weights give an independent fourth row

At the actual penultimate the paid first backward identity gives \(b_9+b_{10}u=b_9(1+u)\), hence \(b_9=b_{10}\ne0\). The actual nonzero signed nodewise residual at those two nonhole pegs is constant. Thus
\[
 H_N(c)D'_7(c)=H_N(x)D'_7(x).
\]
A derivative at a known peg is \(D_7'(c)=E_5'(c)R(c)\), likewise at \(x\). This yields the fourth homogeneous row, whose entry at column \(j\) is
\[
 H_N(c)E_5'(c)c^j-H_N(x)E_5'(x)x^j .
\]
The same true monic quadratic annihilates this row as well as the three signed rows. Every \(3\times3\) minor with the terminal row must therefore vanish. This test is before any reconstruction or ordering of the two ordinary roots, so it closes each of the three actual silent placements without exchanging their later chronology or claiming an ordinary fifth when fifth is silent.

At \((1129,t=203)\), the four orientation models retain all **94** complete reduced diagonal components (21, 36, 15, 22), with multiplicities. Each uses the full fourth gcd of \(J\) and its exact projected equation, and the complete gap gcd of \(F,N\). The full \(F\) leading coefficient is checked a unit before adjoining its monic quotient. The three minors involving the true terminal row generate a unit in every full retained algebra, including those containing repeated gap factors. The finite localization argument then excludes characteristic-zero points. No signed-mass inverse, early rank pivot, ordinary derivative inverse, or Cramer inverse is needed in these final tests.

## Replay and Lean

With `sympy==1.14.0` and `python-flint==0.9.0`, run `python3 check_eight_reverse_live_affine_shared_quintic_hole4_middle.py` beside its declared companion proofs. The [native Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleMiddle.lean) verifies the signed evaluation column, double determinant factor, monic coefficient-minor implication, derivative at the true peg, and terminal weight row on Lean/Mathlib 4.36.0. The saturation bridge and exact arithmetic remain source-level.
