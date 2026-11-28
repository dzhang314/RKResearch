# Seven distinct zeros with two silent off clocks and a varying double

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight, over a characteristic-zero field with common nonzero diagonal \(\gamma\). Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose exactly seven physical entries of \(\mathbf g\) vanish, at seven distinct literal clock labels, and the three off rows have two physical clocks, with two different nonzero residual values at the doubled clock.

**Result.** This chart is impossible for every characteristic-zero field, including both live reflected phases and a silent zero at stage 8. Together with the [separate low-label cases](../sdirk-eight-seven-eight-zero-census/README.md#3-exact-low-label-exclusion-for-the-two-clock-varying-pure-branch), this excludes the **entire** exactly-seven pure varying-double, two-off-clock chart in characteristic zero. It does not exclude other seven-zero charts or change the overall stage interval.

## 1. Supported traces give small exact forward fields

Use the [paid saturated support census](../sdirk-eight-seven-eight-zero-census/README.md). All three off weights vanish; both reverse pure rows in \(Z_3\) are supported on the seven zero coordinates \(U=\ker G\). Normalize by \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\). The first two forward rows are off at their two distinct clocks \(1,1+u\), and the literal third is zero, by the three distinct clocks at the front. Its phase is arithmetic since the forward second residual ratio is nonzero, so
\[
 a=x_3=1+2u,\qquad Q(u)=4u^3-12u^2+3u+2=0.
\]
Write \(d=1\) or \(1+u\) for the doubled varying off clock, and \(f\) for the other off clock, with nonzero normalized residual \(\eta_f\).

There is a useful extra span of **actual supported grade-three columns**: every scalar polynomial \(S(T)\) of degree at most three vanishing at \(d\) occurs. Indeed
\[
 S(\mathbf x)-\frac{S(f)}{(f-d)\eta_f}(\mathbf x-d\mathbf1)\odot\boldsymbol\eta,\qquad
 \boldsymbol\eta=\mathbf g/\gamma^2,
\]
vanishes at each physical off row; its pure correction has grade at most three and its scalar trace on the zero rows is \(S\).

The grade-four discrepancy on \(U\) is the line of the shifted fourth Legendre polynomial
\[
 L_D(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4 .
\]
Indeed \(GE_2\) has rank three, vanishes on \(U\), and is contained in \(F_4\) of dimension four. The scalar vector \(L_D(\mathbf x)\) is in \(F_4\) by ordinary moments and is nonzero on seven distinct labels. At \(a\) it cannot vanish: for the supported pure quadratic \((T-1)(T-1-u)\), its \(M=CA-AC-A^2\) read there is diagonal \(-\gamma^2(a-1)(a-1-u)\ne0\).

Put \(S(T)=(T-a)(T-d)\) and write \(b\) for the second chronological zero. The two supported inputs \(S,TS\) both vanish at \(a\), so in their actual \(A'\) reads both \(a\) and \(b\) are diagonal. With \(J\) the primitive from zero, the two line equations are
\[
 L_D(a)[S(b)-JS(b)]+L_D(b)JS(a)=0,
 \qquad
 L_D(a)[bS(b)-J(TS)(b)]+L_D(b)J(TS)(a)=0 .
\]
Eliminating the common Legendre value gives a quartic polynomial in \(b\), independent of \(D\). Over \(\mathbb Q(u)\) its exact factorization is the forbidden \(b=a\) and an irreducible cubic. With \(b\) in that cubic, the first displayed line equation is a quartic in \(D\), irreducible over \(\mathbb Q(u,b)\). The replay verifies \(u+b\) is a primitive element of degree nine, with explicit inverse coordinates. Thus for **each** choice of \(d\) the only possible forward field is one abstract field of degree \(36\); root orientation is not restricted to the rationals or reals.

We also use the third forward diagonal gate. If \(c\) is the third chronological zero, take \(S_3(T)=(T-a)(T-b)(T-d)\), another actual supported grade-three trace. It kills both earlier zero donors. Hence
\[
 L_D(a)[S_3(c)-JS_3(c)]+L_D(c)JS_3(a)=0 .
\]
All three equations are through ordinary grade four, with actual off rows giving zero contributions irrespective of interleaving.

## 2. Rear cardinal rows and the arithmetic compatibility sextic

Let \(s=x_{10}=D-1,\ t=x_9=D-1-v\), and let \(r=x_8\). The pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T M/2\) is supported on the seven distinct zeros and annihilates scalar powers through degree five. It is therefore a nonzero barycentric row. In particular it is nonzero at **every** zero label. The common rear ratio \(\kappa=1+2v-v^2\) cannot vanish since the literal zero-ratio relation would support \(\mathbf z\) at only \(s\). The eighth row cannot be a silent off row: the literal ghost requires \(z_8\ne0\). Thus row 8 is a zero, live or silent.

For the monic seven-label polynomial \(P_7\) define the cardinal numerators \(B(x_i)=I_D(P_7/(T-x_i))\), with \(I_D(T^j)=D^j/(j+1)\). Then \(B(x_i)=b_iP_7'(x_i)\), including at a silent label. Since \(z_iP_7'(x_i)\) is constant, the ratios of the literal reverse residual to its weight become
\[
 \kappa B(t)=B(s),\qquad
 \kappa_3 B(r)=B(s)\ \text{if row 8 is live},
\]
where \(\kappa_3\) is the normalized third reflected residual. If row 8 is silent, \(B(r)=0\) and the [literal ghost gate](../sdirk-eight-four-zero-gaussian-rear/README.md) gives \(H(v)=v^3-4v^2-v+2=0,\ r=s-2v\). For live arithmetic \(r=s-2v\), the cleared literal third read gives \(H(v)\kappa_3=-\kappa Q(v)\). Here \(H(v)\ne0\), since \(Q,H\) are coprime over \(\mathbb Q\) and \(\kappa\ne0\). The live star has \(r=s-(2-v)\) and \(\kappa_3=\kappa\).

The live arithmetic case has one additional no-tap relation. Use the reflected scalar variable \(Y=D-T\), with the three known live rear labels \(1,1+v,1+2v\) in it. Put \(J_*=3v-2\) and
\[
 P_{\mathrm{rev}}(Y)=H(v)(4Y-2-Y^2)+2J_*(Y-1)(Y-1-v).
\]
Its values on those labels are \(H,H\kappa,H\kappa_3\) by direct interpolation. If \(\omega=z_{10}/b_{10}\ne0\), the actual grade-two row of scalar profile \(P_{\mathrm{rev}}(D-T)\) obtained from its weighted evaluation and the pure correction \(-H\mathbf z^\mathsf T/\omega\) vanishes at **all three** rear donor labels. Its right multiplication by \(A'\) is zero on each of them by chronology. The right primitive has reflected profile \(J P_{\mathrm{rev}}(Y)\); its pure discrepancy is in \(Z_3=\langle\mathbf z^\mathsf T,\mathbf z^\mathsf T(A'-I)\rangle\), which is \(\mathbf z^\mathsf T\) times affine functions of the clock because \(\kappa\ne0\). Dividing the three discrepancies by their nonzero pure coordinates gives the arithmetic affine relation
\[
 \frac{J P_{\mathrm{rev}}(1+2v)}{\kappa_3}
   = 2\frac{J P_{\mathrm{rev}}(1+v)}{\kappa}
       -J P_{\mathrm{rev}}(1).
\]
All three weights are live in this step. Cleared against the prior identity for \(\kappa_3\), this forces
\[
 8v^6-44v^5+22v^4+97v^3-55v^2-13v+6=0 .
\]
The polynomial identity, with only nonzero arithmetic guards canceled, has a separate Lean check. No assumption that the full mirror is an RK method is made.

## 3. Exact rejections of the three rear branches

The five known distinct zero labels are \(a,b,s,t,r\); the other two form a monic quadratic \(U_2(T)\). Write \(P_7=P_5 U_2\) for their five-label mask \(P_5\). The ordinary equation \(I_D(P_7)=0\), the first cardinal ratio, and either the second ratio or silence \(B(r)=0\) give a homogeneous three-by-three matrix on the two unknown and one leading quadratic coefficients of \(U_2\). Its determinant must vanish even at an ordinary pivot drop. Every probe uses ordinary degrees at most seven.

In the **silent** and **live arithmetic** branches, the necessary gap polynomial is the ghost cubic or the compatibility sextic. In the simple residue embeddings below, the determinants have constant gcd with these exact gap polynomials. The gap roots are integral because the cubic is monic and the sextic leading coefficient \(8\) is a unit at these primes. Reduction therefore rules out every common algebraic root, not just residue field rational roots. No polynomial factor is stripped based on a residue-only nonzero test.

In the **live star**, \(B(t)=B(r)\) because \(\kappa\ne0\), and
\[
 B(t)-B(r)=(t-r)I_D\!\left(P_7/((T-t)(T-r))\right).
\]
With \(m=D-2\) and \(F=(T-a)(T-b)(T-s)\), the literal pair \(t,r=m\pm(v-1)\) gives two ordinary recovery rows
\[
 I_D(F U_2)=0,\qquad I_D(F(T-m)^2 U_2)=0 .
\]
They are independent of the squared gap or its sign. The ordinary two-by-two pivot is a unit in the selected simple residue embedding, so is nonzero in the exact field. The recovered monic quadratic has constant gcd with the **third forward** equation for \(c\) after reduction. Since its roots are integral at the selected prime, no actual forward third zero can satisfy that equation. Both chronological orders and both reflected orientations are covered.

| Doubled clock | Branch | \(p\) | \(u+b\bmod p\) | \(u\bmod p\) | \(b\bmod p\) | \(D\bmod p\) | Checked residue |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- |
| \(1\) | Silent, live arithmetic, live star | 61 | 29 | 38 | 52 | 4 | determinant degrees \(4,9\); star pivot \(22\), \(U_2=T^2+27T+12\) |
| \(1+u\) | Silent, live arithmetic | 41 | 29 | 35 | 35 | 17 | determinant degrees \(4,9\) |
| \(1+u\) | Live star | 41 | 29 | 35 | 35 | 26 | star pivot \(38\), \(U_2=T^2+3T+1\) |

At each entry the primitive-element and diagonal factor roots are simple, with unit coefficient denominators. They give embeddings of the respective degree-36 characteristic-zero fields into \(p\)-adic fields. The computations do not assert a corresponding exclusion in characteristic \(41\) or \(61\).

## 4. Replay and exact scope

Run `python forward_clock_tower.py` and `python check_rear.py` with SymPy 1.14 and Python-flint 0.8. The replay builds the exact fields and validates the fixed table above; there is no finite-grid inference. The native `RKCert.Research.SDIRKEightSevenZeroDistinctScalar` module checks the division-free two-line elimination, star moment cancellation and the arithmetic compatibility polynomial over the stated scalar domains. The rooted chronology, algebraic field construction and final exclusion are the mathematical proof and exact replays, not one native `HasOrder` theorem.
