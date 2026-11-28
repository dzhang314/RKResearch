# Three silent off clocks: the low-label nonzero-ratio branch is impossible

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\). Set \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly seven physical entries of \(\mathbf g\) are zero; the three other physical rows have three distinct clocks. Suppose the second reflected defect ratio is nonzero.

**Result.** The seven physical zero rows must have **seven distinct literal clocks**. This packet excludes every case with six or fewer zero clock labels and does not address the zero reflected ratio or the seven-distinct case. It does not change the unrestricted stage interval.

## 1. Clock multiplicities force a five-label arithmetic rear

By the [paid rank census](../sdirk-eight-seven-eight-zero-census/README.md), the three off weights are silent, and the pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\), \(C=\operatorname{diag}(\mathbf c)\), is supported on \(U=\ker\operatorname{diag}(\mathbf g)\). It annihilates scalar powers through degree five. Normalize
\[
 A'=A/\gamma,\quad \mathbf x=\mathbf c/\gamma,\quad D=1/\gamma,\quad
 s=x_{10}=D-1,\quad t=x_9=s-v,\quad r=x_8,
\]
and let \(I_D(T^n)=D^n/(n+1)\). The normalized reflected ratio \(\kappa=1+2v-v^2\) is nonzero. The last two weights and last two \(z\) coordinates are nonzero. At six or fewer literal zero labels, Vandermonde forces all \(z\) aggregates to vanish. Hence \(s,t\) each need a separate duplicate, and there are at most five labels.

A silent row 8 has \(z_8\ne0\) by the [literal ghost gate](../sdirk-eight-four-zero-gaussian-rear/README.md), so it must itself be a zero, not an off row. A live row 8 must also be a zero, since all off weights vanish. Both possible literal third phases have \(r\) distinct from \(s,t\). If \(z_8\ne0\), it needs a third duplicate, leaving at most four zero labels. Whenever there are at most four, ordinary moment rank forces precisely four Gaussian labels. The three reflected labels are then a directed Gaussian triple \(x,y,2y-x\) (arithmetic, including ghost) or \(x,y,4x-y\) (star). The replay certifies constant gcd between the Gaussian polynomial and the projection of either possible directed pair (use the divided difference in the second variable to keep the distinct pair algebra). Thus four or fewer labels are impossible and \(z_8=0\).

Therefore row 8 is live, and its phase is arithmetic since the star would give its reflected ratio equal to \(\kappa\ne0\). With \(Q(T)=4T^3-12T^2+3T+2\), the literal arithmetic ratio formula at zero third residual yields
\[
 r=s-2v,\qquad Q(v)=0 .
\]
There are exactly five labels, with just the two duplicate groups at \(s,t\), and a singleton at \(r\). The four zero rows before row 8 have four different clocks: the two early copies of \(s,t\) and two unseen labels.

## 2. Ordinary projection and actual supported forward reads

Set \(P_3=(T-s)(T-t)(T-r)\), and let \(Q_2\) be the monic quadratic on the other two literal labels. The ordinary masked moments \(I_D(T^j P_3Q_2)=0,\ j=0,1,2\), give a three-by-three Hankel determinant in \(D\) over \(\mathbb Q(v)\), with entries \(m_{i+j}=I_D(T^{i+j}P_3)\). Its degree is 15 and the exact factor \(D^6\) may be removed because \(\gamma\ne0\). This test does not assume that all five ordinary aggregates are live. The guarded degree-nine polynomial has exact factor degrees \(1,8\), and the lower two-by-two pivot for recovering \(Q_2\) is verified later on every root fiber.

The first two physical rows are off by the [multi-clock row-two gate](../sdirk-eight-seven-eight-off-silent/README.md); write their clocks \(1,1+u\), and denote the third off clock by \(d\). The literal first three physical clocks are pairwise distinct. Thus the first zero is either physical row 3, or physical row 4 after all three off clocks. Its clock is \(a\), and the next two zero clocks are \(b,c\). By the previous chronology the three are distinct and belong to the four known early labels \(\{s,t\}\cup\{\text{roots of }Q_2\}\).

The unique quadratic polynomial \(P\) interpolating the normalized residual \(\mathbf g/\gamma^2\) on the three off clocks can be written
\[
 P=P_0+\lambda R_0,\qquad
 P_0(T)=2T-1-T^2/2,\quad R_0=(T-1)(T-1-u).
\]
Its actual supported grade-two vector is \(P(\mathbf x)-\mathbf g/\gamma^2\); denote it by \(\mathbf P\). Also the actual scalar cubic \(\mathcal R=R_0(T-d)\) is supported. Since there are at least two physical off clocks, \(F_3\) is zero on the seven zero rows. By rank, \(F_4|_U\) is the line of \(L_D(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4\): \(GE_2\) has rank three and vanishes there, while \(L_D\) cannot vanish at five distinct labels.

Write \(J\) for the primitive from zero. The first diagonal read gives \(JP(a)=P(a)\). In fact \(a,P(a),L_D(a)\) are all nonzero. To see this, the normalized commutator \(M'=C'A'-A'C'-(A')^2\) acts injectively on vectors supported on \(U\) after restricting the output to \(U\), by its principal triangular block with unit diagonal \(-1\). The nonzero \(M'\mathbf P|_U\) is proportional to \(L_D\) and its first zero entry is \(-P(a)\). If \(a=0\), then \(JP(a)=P(a)=0\) but \(L_D(0)=D^4\ne0\). If \(a\ne0,P(a)=0\), then \(L_D(a)=0\) and the pure read of the supported input \(T P\) also gives \(J(TP)(a)=0\). Setting \(T=aY\), a polynomial \(P(aY)=(Y-1)(\mu Y+\nu)\) with both primitives zero at \(a\) has \(\mu=\nu=0\) by the two normalized moments (determinant \(-1/72\)). This contradicts \(P(1)=1/2\).

The only earlier zero donor at \(b\) has tap \(\theta=(JP(b)-P(b))/P(a)\). Pairing the \(TP\) discrepancies at the first and second zero via the common \(L_D\) line gives the linear graph gate
\[
 \mathcal G(P;a,b)
 =L_D(a)\bigl[(b-a)P(b)+aJP(b)-J(TP)(b)\bigr]
 -L_D(b)\bigl[aP(a)-J(TP)(a)\bigr]=0 .
\]
No coefficient at an off donor enters this computation.

## 3. Three forward placements in one good reduction

If the first zero is physical **row 3**, its literal phase is arithmetic; \(u=(a-1)/2\), \(Q(u)=0\). At each residue candidate the coefficient \(\mathcal G(R_0;a,b)\) is a unit, so \(\lambda\) is exactly reconstructed by the second-zero gate. The \(P(a)\) pivot is also a unit. The same second-zero read applied to the supported cubic \(\mathcal R\) gives
\[
 \mathcal D(\mathcal R)
 =L_D(a)\bigl[(\mathcal R-J\mathcal R)(b)+\theta\mathcal R(a)\bigr]
  -L_D(b)(\mathcal R-J\mathcal R)(a)=0 .
\]
This is linear in \(d\) because \(\mathcal R=TR_0-dR_0\), and \(\mathcal D(R_0)\) is a unit on all those fibers. At the third zero \(c\), the vectors \(\mathbf P,\mathbf x\odot\mathbf P,\mathcal R(\mathbf x)\) see only the two earlier zero donors. For arbitrary prospective taps \(n_a,n_b\) the three equations have left columns
\[
 \begin{pmatrix}
 P(a)&P(b)\\ aP(a)&bP(b)\\ \mathcal R(a)&\mathcal R(b)
 \end{pmatrix}.
\]
Their right column is
\[
 \begin{pmatrix}
 JP(c)-P(c)\\
 J(TP)(c)-cP(c)+[aP(a)-J(TP)(a)]L_D(c)/L_D(a)\\
 J\mathcal R(c)-\mathcal R(c)+[\mathcal R(a)-J\mathcal R(a)]L_D(c)/L_D(a)
 \end{pmatrix}.
\]
The augmented determinant must vanish. The residue proof checks the pivot \(L_D(a)\) and excludes both \(c\) choices for every possible directed \((a,b)\).

If the first three rows are off in **star**, the front second and third residuals are the same, at normalized clocks \(1+u,3-u\). They both agree with \(P_0\), hence the actual graph is \(P=P_0\). The first and second supported reads \(JP_0(a)=P_0(a)\), \(\mathcal G(P_0;a,b)=0\) are incompatible at every geometric fiber. This test does not fix the front star gap.

If the first three rows are off in **arithmetic**, the third clock is \(1+2u\). The literal front tap identity gives
\[
 P_\sharp=H(u)P_0+(3u-2)R_0,\qquad H(u)=-2+u+4u^2-u^3.
\]
Here \(H(u)\ne0\): its vanishing would also force \(u(3u-2)=0\), incompatible with \(H\). Therefore \(P_\sharp\) is a nonzero scaling of the actual graph. The first and second gates \(JP_\sharp(a)-P_\sharp(a)=0\), \(\mathcal G(P_\sharp;a,b)=0\) are two polynomials of degree at most three in the front gap \(u\). At least one preserves degree three in every tested fiber, so any simultaneous root is integral at the selected good reduction. The two reduced polynomials have constant gcd for all ordered \((a,b)\), and no front gap root survives.

## 4. Exact geometric replay

At \(p=37\), \(v=22\) is a simple residue root of the irreducible rear cubic. The guarded diagonal polynomial reduces to
\[
 16(D+28)(D^4+16D^3+35D^2+6D+25)(D^4+23D^3+10D+31),
\]
where the two quartics are irreducible. The replay uses explicit fields of degrees two and eight over \(\mathbb F_{37}\), containing all the diagonal roots and any quadratic completions. It checks all nine exact residue diagonal choices and both roots of each monic completion, with nonzero ordinary pivots and pairwise distinct labels. On the 108 ordered \((a,b)\) pairs it verifies the arithmetic gcds; there are three row-3 pairs and three front-star pairs satisfying the respective first necessary residue gates, all excluded by the additional reads above.

The simple rear root embeds \(\mathbb Q(v)\) into \(\mathbb Q_{37}\); the diagonal projection has unit leading coefficient, and the ordinary quadratic is monic at every recovered residue fiber. Thus every algebraic coefficient choice can be placed in an extension of this embedding and reduced to one of the checked roots. All divided pivots are tested where they occur. This proves the characteristic-zero exclusion rather than extrapolating from the absence of a prime-field tableau.

Run `python check_five_label.py` with SymPy 1.14 and python-flint 0.8. The checked Lean/Mathlib 4.36.0 scalar module `RKCert.Research.SDIRKEightSevenZeroThreeClockFiveLabel` certifies the two-supported-donor determinant and the monic Hankel kernel identity. The remaining coefficient-field projection and rooted chronology are stated separately above; there is no new end-to-end native rooted theorem.
