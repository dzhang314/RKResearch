# Eight distinct zero clocks with a constant reverse numerator

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field. Let \(\mathbf c=A\mathbf1\) and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly eight physical zeros of \(\mathbf g\), at eight distinct clocks. The [low-label result](../sdirk-eight-eight-zero-low-labels/README.md) then places the two off rows, with distinct clocks and individually zero weights, at physical positions 1 and 2.

**Result.** This chart is impossible if the reverse quadratic pure row has a **constant** barycentric numerator on its eight zero-residual labels. It covers the silent-eighth, live arithmetic, and live star reflected phases. The proof is characteristic-zero, not an exclusion of the nonconstant numerator or a general 11-stage lower bound.

## 1. The actual two-mode grade-four trace

Normalize \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\), \(C'=\operatorname{diag}(\mathbf x)\), and let \(U=\ker\operatorname{diag}(\mathbf g)\). Write \(P_8\) for the monic polynomial of the eight zero labels. The reverse grade-two pure row \(\mathbf z^\mathsf T\) is supported on \(U\), and its first six ordinary moments vanish. Thus \(z_iP'_8(x_i)=\theta(x_i)\) there for some affine \(\theta\), by the leading-coefficient identity for cardinal interpolation. Here assume \(\theta\) constant; it is nonzero because \(z_{10}\ne0\). In particular the second rear ratio is nonzero, and all eight coordinates of \(\mathbf z\) on \(U\) are nonzero.

Let \(L_{j,D}\) be the shifted Legendre polynomial scaled so \(L_{3,D}=20T^3-30DT^2+12D^2T-D^3\); the leads of \(L_{4,D},L_{5,D}\) are \(70,252\). Let \(I_D(T^k)=D^k/(k+1)\) and set \(\mu=I_D(P_8)\), a formal mean, **not** an order-nine assumption. The dual \(W_3\) is spanned by the four ordinary rows \(\mathbf b^\mathsf T(C')^j\), \(0\le j\le3\), and the pure rows \(\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\). Its pure pair is independent on rows 9 and 10. By saturation \(F_4=\operatorname{Ann} W_3\). For a column in \(F_4|_U\), interpolate its eight values by a polynomial \(F\) of degree at most seven. The last two rows make its degree-seven and then degree-six coefficients zero: each is a leading cardinal coefficient with factor \(z_iP'_8(x_i)\) constant. The first three ordinary rows now pair with \(F\) exactly (total degree at most seven), placing \(F\) in the span of \(L_{3,D},L_{4,D},L_{5,D}\).

For the fourth ordinary row, the quadrature of a degree-eight polynomial equals its mean minus its degree-eight coefficient times \(\mu\), since the remainder modulo \(P_8\) is exact. In particular
\[
 I_D(T^3 L_{3,D})=D^6/140,\quad
 \mathbf b^\mathsf T(C')^3 L_{4,D}(\mathbf x)=0,\quad
 \mathbf b^\mathsf T(C')^3 L_{5,D}(\mathbf x)=-252\mu.
\]
Thus the actual pure space has precisely the two trace modes
\[
      F_4|_U=\langle L_{4,D},S_{5,D}\rangle|_U,\qquad
      S_{5,D}=L_{5,D}+\lambda L_{3,D},\qquad
      \lambda=35280\mu/D^6 .
\]
This argument uses paid field operations only, including the formal ninth-denominator mean, not eighth-degree quadrature precision.

## 2. Two rear cardinal rows and the quadrature defect

Denote the five early physical zero clocks by \(a,b,c,d,e\), and the last three by \(r=x_8,t=x_9,s=x_{10}\), with \(s=D-1\). Put \(\sigma=(T-a)(T-b)(T-c)\) and \(P_2=(T-d)(T-e)=T^2+v_1T+v_0\). At each label \(x\), \(B(x)=I_D(P_8/(T-x))=b_iP'_8(x)\). Because the barycentric numerator is constant, the literal ratio at the second rear row gives \(B(s)=\kappa B(t)\), \(\kappa=1+2v-v^2\ne0\), where \(t=s-v\).

In the finite-gap branches, \(r=s-2v\), and let \(U_6=\sigma(T-s)(T-t)(T-r)\), \(U_x=U_6/(T-x)\). The two masks whose products with \(P_2\) have zero mean are:

| Phase | First mask | Second mask | Gap equation |
|---|---|---|---|
| Silent eighth | \(\kappa U_t-U_s\) | \(U_r\) | \(H(v)=0\) |
| Live arithmetic | \(\kappa U_t-U_s\) | \(-\kappa Q(v)U_r-H(v)U_s\) | \(T_6(v)=0\) |

Here \(H(v)=v^3-4v^2-v+2,\ Q(v)=4v^3-12v^2+3v+2\), and \(T_6(v)=8v^6-44v^5+22v^4+97v^3-55v^2-13v+6\). The second live row is the literal arithmetic third-ratio equation \(H(v)\kappa_3=-\kappa Q(v)\), combined with \(\kappa_3 B(r)=B(s)\), without dividing by \(H\). The compatibility sextic is the [actual three-input affine gate](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic), valid here because the two reverse pure directions are \(\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\). In these branches \(\mu=I_D(U_6 P_2)\).

For live star let \(m=D-2,\ \delta=v-1\), so \(t,r=m\mp\delta\), \(s=m+1\) and \(\kappa=2-\delta^2\). The two singleton ratios \(B(t)=B(r)\) and \(B(s)=\kappa B(t)\) reduce to the gap-free masks
\[
 \sigma(T-s),\qquad \sigma((T-m)^2-2).
\]
Indeed the first difference divided by \(t-r\ne0\) gives the first mask. With this mean zero, the second ratio factors as \((1-\delta^2)I_D(\sigma P_2((T-m)^2-2))=0\). The removed factor is nonzero because otherwise one of \(t,r\) equals \(s\). Since \(P_8=\sigma P_2(T-s)((T-m)^2-\delta^2)\), the first mask gives \(\mu=I_D(U_6 P_2)\) with effective \(U_6=\sigma(T-s)(T-m)^2\), independent of the free gap. No equation \(I_D(P_8)=0\) is used.

## 3. Actual early reads give two equations before any moment division

The [forward gates](../sdirk-eight-eight-zero-low-labels/README.md#1-literal-placements-and-exact-profile-gates) give \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\). Let \(Z_2=(T-a)(T-b),Z_3=T Z_2\). These are supported \(E_3\) inputs because the two supported quadratics \(2T-1-T^2/2\) and \((T-1)(T-1-u)\) are coprime and their affine multiples span all cubics. Here \(J\) means formal integration from zero. Their two \(F_4\) primitive discrepancies have first-two matrix given by \(-JZ_2,-JZ_3\) at \(a,b\), with determinant \(a^2b^2(a-b)^3/24\ne0\). Their reads at \(c\) are diagonal, so the discrepancy values there are \(Z_2(c)-JZ_2(c),Z_3(c)-JZ_3(c)\). Consequently there are explicit polynomials \(\alpha(c),\beta(c)\), independent of \(D\), expressing the \(c\)-value of any \(F_4|_U\) column as \(\alpha(c)\) times its \(a\)-value plus \(\beta(c)\) times its \(b\)-value. The replay computes this inverse and verifies its endpoint values.

Put
\[
 g_j(c,D)=\frac{L_{j,D}(c)-\alpha(c)L_{j,D}(a)-\beta(c)L_{j,D}(b)}
                   {(c-a)(c-b)} .
\]
This is a polynomial, via the exact endpoint values of \(\alpha,\beta\). The \(L_4\) relation is the same quadratic \(C_3(c;D)=-g_4(c,D)=0\). The other shape relation is \(g_5+\lambda g_3=0\). Writing \(M_i=I_D(T^i U_6)\), the latter is a third homogeneous row on the coefficients \((v_0,v_1,1)\):
\[
     (35280 g_3 M_0,\ 35280 g_3 M_1,\ D^6 g_5+35280 g_3 M_2).
\]
Put beside it the two ordinary rows \((I_D(R),I_D(TR),I_D(T^2R))\) on the masks \(R\) from section 2. Their determinant \(A_0(D,c)\) vanishes for any actual tableau, **without** an ordinary pivot hypothesis.

## 4. The exact singular factor is structurally impossible

The exact initial field is regenerated with primitive \(u+b\) and degree six for the star, and with primitive \(u+b+2v\) and degrees 18 and 36 for silent and arithmetic. The replay checks irreducibility, inverse maps and the input clock equations. Let \(C_3=\ell_2c^2+\ell_1c+\ell_0\). When \(\ell_2\ne0\), scale \(L=\ell_2 c\), so \(L^2+\ell_1L+\ell_2\ell_0=0\). Clearing powers of \(\ell_2\) in \(A_0\) gives a remainder \(A+B L\) in this monic quadratic algebra. Its norm has degree 80 in \(D\). Remove only factors of \(\ell_2\), the forbidden \(D=0\), and prospective \(a,b\) collisions with the fixed rear labels. The \(\ell_2\) factors remove 20 degrees, the power of \(D\) is 12, and no collision factor contributes. The guarded norm has degree 48.

Write \(p_{4j}=L_{4,D}(a)L_{j,D}(b)-L_{4,D}(b)L_{j,D}(a)\). Since \(L_4,S_5\) form a basis and the \(a,b\) read is injective, its actual basis determinant \(p_{45}+\lambda p_{43}\) is **nonzero**. Consider the polynomial
\[
 E=p_{45}g_3-p_{43}g_5=g_3(p_{45}+\lambda p_{43})
\]
on the actual shape equation. Its norm in the same scaled quadratic algebra has degree 42. Stripping only \(\ell_2\) gives \(H_0\) of degree 30, and the replay verifies by **exact division** that \(H_0\) divides the guarded degree-48 norm. This is not a discard of roots based on finite-specialization rank.

To identify the branch at a root of \(H_0\), let \(E_0+E_1L\) be the scaled remainder of \(E\). The exact polynomial \(E_0 B-E_1 A\) vanishes modulo \(H_0\). At a root of \(H_0\), \(B\), \(\ell_2\), and the scaled norm of \(g_3\) are nonzero, verified on the **whole** degree-30 reduction with preserved leading coefficient. Thus the actual \(L=-A/B\) forces \(E=0\) and \(g_3\ne0\); the required basis determinant would be zero. This contradicts the literal first-two read, even if the ordinary moment recovery were singular. It removes the exact degree-30 factor. The other factor \(N_1\) has degree 18.

## 5. The fourth diagonal rejects the remaining degree-18 factor

For each branch use the following fixed simple primitive residue \((p,z_0)\):

| Silent eighth | Live arithmetic | Live star |
|---:|---:|---:|
| \((59,1)\) | \((59,28)\) | \((13,9)\) |

The full residue algebra of \(N_1\) is used, without asking that its factors split. Its degree is preserved. The replay checks \(D,\ell_2,B\) are units there, reconstructs \(c=-A/(B\ell_2)\), and checks the ordinary two-by-two determinant is a unit. It uses the two ordinary rows to recover the coefficients of \(P_2\), and recomputes \(\lambda\) from \(\mu=I_D(U_6P_2)\). It checks the actual first-two evaluation determinant of \(L_4,S_5\) is a unit before using the basis.

Use \(\sigma=(T-a)(T-b)(T-c)\) as an actual supported cubic. The first three physical zero inputs vanish. Its primitive discrepancy in the two-mode \(F_4\) trace is determined by its first two values \(-J\sigma(a),-J\sigma(b)\), giving coefficients in \(L_4,S_5\). At the fourth physical zero \(d\), the read is diagonal. Hence the polynomial \(\sigma-J\sigma\) minus that trace vanishes at \(d\) as well as the first three labels. After clearing the first-two evaluation determinant, divide by the monic \(\sigma\); this yields a degree-at-most-two polynomial \(C_4\) which must vanish at \(d\), since the literal labels are distinct. The replay checks the synthetic division in the entire quotient. Reducing \(C_4\) modulo \(P_2\), the remaining linear polynomial has **unit quadratic norm** in that quotient, so neither of the prospective roots of \(P_2\) can be \(d\).

For the leading drop \(\ell_2=0\), the degree of \(\ell_2\) is preserved in the same residue. The linear coefficient \(\ell_1\) is a unit modulo it; substituting \(c=-\ell_0/\ell_1\) gives \(A_0\) with constant gcd with \(\ell_2\). Thus the leading-drop branch is independently excluded **without** a moment or forward evaluation pivot.

All these good reductions lift the exact common field using the simple primitive root. Unit leading coefficients force any hypothetical roots of \(H_0,N_1,\ell_2\) to be integral in any extension of that valuation. The checked units allow the displayed recovery divisions on every such root. Finally the recovered monic \(P_2\) forces \(d\) integral, so the full residue norm test rules it out. This proves a characteristic-zero exclusion; there is no finite-field-grid inference or corresponding assertion over every positive characteristic.

## 6. Replay and native scope

Run `python check_constant.py PHASE` with SymPy 1.14 and Python-flint 0.8 for `PHASE=ghost,arith,star`. Expect the arithmetic extension to take longer. The [Lean source](../../lean/RKCert/Research/SDIRKEightEightZeroConstantBarycentric.lean) checks the cleared Legendre moment and the scalar rank-factor cancellation; the quadratic norm gate is separately native in the early-repeat companion. The physical saturated-flag ingress and exact field-size certificates are the mathematical proof and independent Python replay, not an unconditional native order theorem or a global stage-bound improvement.
