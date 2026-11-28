# The last seven-label paired-star branch

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field. Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose \(\mathbf g\) has exactly eight physical zeros at seven distinct zero labels. The [midpoint and repeat census](../sdirk-eight-eight-zero-late-mate/README.md) and the [first-three unequal-cardinal exclusion](../sdirk-eight-eight-zero-star-unequal-front/README.md) leave only a live reflected star. Its repeated clock \(q\) connects physical row 8 or 9 to physical row **6 or 7**, with unequal grouped cardinals \(B(q)\ne B(p)\) at the two members of the star pair. The other two off rows are distinct, silent, and at physical positions 1 and 2.

**Result.** This last seven-label chart is impossible in every characteristic-zero field. Together with the preceding exclusions this rules out **all seven-label configurations with exactly eight physical quadratic zeros**. The eight-distinct-label case with nonconstant reverse numerator remains separate, so the overall ten-stage lower question is not changed. No positivity, real order, or weighting assumption on the early copy is used.

## 1. Two ordinary rows with a cubic peak-gap projection

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and use \(I_D(T^j)=D^j/(j+1)\). The first three zero labels \(a,b,c\) in physical rows 3, 4, 5 are singletons. Put
\[
 \sigma(T)=(T-a)(T-b)(T-c),\qquad
 m=D-2,\quad Y=T-m,\quad s=m+1,\quad q=m+\delta,\quad p=m-\delta.
\]
Thus \(p,q\) are the two star pair labels, with \(p\) a singleton. Let \(x=m+\xi\) be the other fourth/fifth early label, so the monic seven-label polynomial is
\[
 P_7=\sigma(T)(Y-\xi)(Y-\delta)(Y+\delta)(Y-1).
\]
Write \(\kappa=2-\delta^2\), and \(n_j=I_D(Y^j\sigma)\) for \(0\le j\le4\). Ordinary exactness and the two **singleton** cardinals give \(I_D(P_7)=0\) and \(B(s)=\kappa B(p)\). In these coordinates the ratio uses the mask
\[
  \kappa(Y-1)(Y-\delta)-(Y^2-\delta^2).
\]
Adding \(1+\delta\) times the nodal mask and canceling \(1+\delta\ne0\), since \(p\ne s\), gives the second ordinary mask \((Y-\delta)(Y^2-2)\). Thus the two masks, before multiplying by \(\sigma(Y-\xi)\), are
\[
 R=(Y-\delta)(Y+\delta)(Y-1),\qquad
 S=(Y-\delta)(Y^2-2).
\]
The ordinary equations are \(A_1=\xi A_0,\ B_1=\xi B_0\), with
\[
 A_i=n_{i+3}-n_{i+2}-\delta^2(n_{i+1}-n_i),\quad
 B_i=n_{i+3}-2n_{i+1}-\delta(n_{i+2}-2n_i),\quad i=0,1.
\]
Their determinant \(A_0 B_1-A_1 B_0=0\) is only cubic in \(\delta\); it is a necessary condition even if the two ordinary recovery pivots vanish. All ordinary means use degree at most seven.

## 2. Cubic pure transfer and the two actual fourth-read lines

By the [split-free two-mode result](../sdirk-eight-eight-zero-star-unequal-front/README.md#1-the-pure-singleton-profile-and-its-literal-early-jump), the actual \(F_4|_U\) basis on singleton labels is \(L_{4,D}\) and
\[
 K(T,q)=\sum_{j=0}^3(2j+1)D^{6-2j}L_{j,D}(T)L_{j,D}(q).
\]
Only the **early physical copy** of \(q\) has the known extra value \(\chi D^6\) in the second mode, with \(\chi=P'_7(q)/(B(p)-B(q))\). All of \(a,b,c\) are singleton reads in this branch. Let \(\alpha(c),\beta(c)\) be the actual third-read transfer coefficients, recovered from the two independent supported inputs \(Z_2=(T-a)(T-b),Z_3=T Z_2\) as in the first-three packet. Then the front gate \(C_3(c;D)=0\) is transfer for \(L_4\). Transfer for \(K\), divided by the nonzero \((c-a)(c-b)\), is the cubic gap polynomial
\[
 G(\delta)=\frac{K(c,q)-\alpha(c)K(a,q)-\beta(c)K(b,q)}{(c-a)(c-b)}=0.
\]
The numerator's exact division is by the first-two endpoint identities. Neither transfer involves a repeated physical coordinate here.

Let \(E\) be the first-two determinant of \(L_4,K\), nonzero for the actual \(F_4\) basis. For the supported input \(\sigma\), the true first three reads vanish, so its pure discrepancy values there are \(-J\sigma\), where \(J\) is integration from zero. Let \(C_L,C_K\) be the Cramer numerators for fitting these two values at \(a,b\) in the two modes, with determinant \(E\). The polynomial
\[
 F(T)=E(\sigma-J\sigma)(T)-C_L L_4(T)-C_K K(T,q)
\]
vanishes at \(a,b,c\) by the transfer equations. It is therefore \(\sigma(T)Q_1(T)\), where \(Q_1\) has degree at most one. This fit is used **cleared**, without division by \(E\) at the final test.

If the early \(q\) is physical row 7, then \(x\) is the fourth zero, at physical row 6. Its input is singleton and its actual read is diagonal, so \(Q_1(x)=0\). Writing \(Q_1(T)=u_0+u_1T\), the corresponding fourth-read line is
\[
 (-u_0-mu_1)=\xi u_1.
\]

If the early \(q\) is physical row 6, then its fourth read is diagonal with the split-free extra term \(C_K\chi D^6\). Let \(M=I_D(\sigma(Y-\xi)(Y-1))=(n_2-n_1)-\xi(n_1-n_0)\). Since \(B(p)-B(q)=(p-q)M\) and
\[
 P'_7(q)=\sigma(q)(q-x)(q-p)(q-s),
\]
the relation \(F(q)=C_K\chi D^6\), after clearing \(M\) and canceling the actual nonzero \(\sigma(q)\), becomes
\[
 Q_1(q)(n_2-n_1)+C_K D^6(\delta-1)\delta
 =\xi\,[Q_1(q)(n_1-n_0)+C_KD^6(\delta-1)].
\]
This is again a line for the same \(\xi\), with **no division by a physical weight**. For each orientation every two-by-two minor between this extra line and the two ordinary lines is zero, including at a last-label moment pivot drop.

## 3. Exact guarded diagonal projection

Regenerate the degree-six initial field \(K_0=\mathbb Q(u,b)\) with primitive \(u+b\), \(a=1+2u\), \(Q(u)=0\), \(b^2-(2u+4)b+1+2u=0\). The replay checks irreducibility, both inverse coordinates and the first-two primitive determinant. Take the resultant in \(\delta\) of the two cubic equations \(G=0\) and \(A_0B_1-A_1B_0=0\). Its degrees in \(D,c\) are 48, 12. Write \(C_3=\ell_2 c^2+\ell_1 c+\ell_0\). For \(\ell_2\ne0\), set \(L=\ell_2 c\) and use the monic quadratic relation \(L^2+\ell_1L+\ell_2\ell_0=0\). The cleared resultant reduces to \(A+B L\); its norm is
\[
 A^2-AB\ell_1+B^2\ell_2\ell_0
\]
of degree 186 in \(D\). Removing only factors of \(\ell_2\) reduces to degree 138, and removing \(D^{24}\) gives degree 114. No scalar early/rear collision factor contributes.

The degree-114 projection is **exactly** \(H^2 N^3\) up to a scalar unit in \(K_0\), with \(\deg H=30,\deg N=18\). To produce \(H\) without a high-degree factor search, form the third-site residuals \(g_3,g_5\) of \(L_{3,D},L_{5,D}\), each divided by \((c-a)(c-b)\), and the first-two determinants \(p_{4j}=L_4(a)L_j(b)-L_4(b)L_j(a)\). In the same scaled quadratic algebra, the norm of \(p_{45}g_3-p_{43}g_5\), stripped of factors of \(\ell_2\), gives \(H\). The divisions by \(H^2\) are exact. The monic cubic root \(N\) of the remaining degree-54 quotient is recovered from its reversed leading coefficients and checked by multiplying back.

## 4. The rank factor is Hankel two-atom, not a finite rank discard

Consider the cubic masked Hankel determinant
\[
 {\cal H}=\det\begin{pmatrix} n_0&n_1&n_2\\n_1&n_2&n_3\\n_2&n_3&n_4\end{pmatrix}.
\]
If its scaled remainder in \(L\) is \(h_0+h_1 L\), the replay verifies the exact congruence \(h_0B-h_1A=0\bmod H\). For an actual root of \(H\) the checked units \(B,\ell_2\) identify \(c=-A/(B\ell_2)\); this exact identity gives \({\cal H}=0\) on the **actual** branch. Further \(\Delta=n_0n_2-n_1^2\ne0\), with a unit check in all geometric \(H\) fibres below.

Define the monic quadratic
\[
 Q_2(Y)=Y^2+v_1Y+v_0,\quad
 \Delta v_0=n_1 n_3-n_2^2,\quad
 \Delta v_1=n_1n_2-n_0n_3 .
\]
The first two moment recurrences are the two Cramer rows, and \({\cal H}=0\) gives the third: \(n_{j+2}+v_1 n_{j+1}+v_0n_j=0\) for \(0\le j\le2\). In the exact quotient by \(Q_2(\delta)\), put \(\epsilon=-v_1-\delta\), so \(Q_2(Y)=(Y-\delta)(Y-\epsilon)\). The row \((n_{j+1}-\epsilon n_j)_{j=0}^3\) is geometric with ratio \(\delta\) by the three recurrences. Its initial value is a unit in the quadratic algebra: its quadratic conjugate product equals \(n_1^2-n_0n_2=-\Delta\). Thus this argument is valid even if the quadratic has a repeated root.

Multiply \((Y-\epsilon)\sigma(T)\) by \(D^6/(n_1-\epsilon n_0)\). Its first four \(Y\)-moments equal the reproducing kernel's, \(D^6\delta^j\). Their difference therefore belongs to the \(L_4\) line, since it has degree at most four with four zero means. The scaled \((Y-\epsilon)\sigma\) vanishes at \(a,b,c\). Hence, on this quadratic gap algebra, \(K\) is proportional to \(L_4\) at those actual first reads; this gives \(G=0\) and shows that any actual root of \(Q_2\) has \(E=0\), contradiction. The ordinary determinant also vanishes modulo \(Q_2\): take \(\xi=\epsilon\) in both ordinary equations, and each integrand contains \(\sigma Q_2(Y)\) times a degree-at-most-two factor, with zero mean by the three recurrences. Consequently \(Q_2\) divides **both** cubic gap polynomials exactly over each actual \(H\) field. Their complementary linear factors have constant gcd in every indicated good residue fibre, as checked below, so there is no other common gap root. The entire \(H\) factor is excluded, not just its rank drop modulo a prime.

## 5. Complete fixed residue check and leading drop

Use \(p_{\rm res}=17,\ z_0=11\) as the fixed simple residue of the degree-six primitive element. The reduction preserves the degrees of \(H,N,\ell_2\); \(B,\ell_2\) are units on \(H,N\), and \(\ell_1\) is a unit on the separate leading-drop guard \(\ell_2\). Each factor below is handled in its full finite extension. At each fibre at least one original gap cubic has its degree-three leading coefficient a unit, so every hypothetical exact gap is integral even if the other cubic drops degree.

| Exact diagonal branch | Degrees of simple residue factors | Exact/finite exclusion |
|---|---|---|
| \(H\) | \(1,5,24\) | \(\Delta\) unit, the common gap gcd is \(Q_2\); the complementary linears are coprime |
| \(N\) | \(1,3,5,9\) | common gap algebra degree three; the cleared fourth-read minors have constant gcd with it for each chronology |
| \(\ell_2=0\) | \(4\) | \(c=-\ell_0/\ell_1\); the original two gap cubics are coprime |

In the \(N\) branch the fourth-read polynomial quotient is constructed in the entire common gap algebra and both necessary minor pairs are checked. No inverse of \(E\), last-label moments, or prospective output weights is taken. The leading-drop computation uses the original gap equations, not the scaled-quadratic norm. The whole residue field of each irreducible diagonal factor and the polynomial gcd over that field cover nonsplit gaps as well. A single representative root of each residue factor suffices because the checks commute with finite-field conjugation.

The simple primitive residue lifts to an embedding of \(K_0\), and all exact coefficients used are integral there. Preserved leading coefficients force every hypothetical diagonal and gap integral in any extension of that valuation. The unit recovery pivots then justify reducing the original exact equations to each displayed fibre. These checks prove characteristic-zero nonexistence; they make no uniform claim in finite characteristic.

## 6. Replay and scope

Run `python check_unequal_late.py` with SymPy 1.14 and python-flint 0.8. The exact Sylvester resultant and square–cube projection split may take around a minute. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroStarUnequalLate.lean) checks the reduced ordinary mask, the third Hankel recurrence, its two-atom shift and the cleared fourth jump. The actual saturated order flags and exact local-field comparisons are the mathematical proof and Python replay, not an end-to-end native tableau theorem.

The new companion is included as source; its independent stock Lean replay was not completed at publication.
