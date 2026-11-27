# Exactly two quadratic-zero rows are impossible at the strict SDIRK8 floor

Consider an actual ten-stage lower triangular Runge–Kutta tableau \(A,\boldsymbol b\) of order at least eight, with common nonzero diagonal \(\gamma\). Take the usual quadratic residual \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\) where \(\boldsymbol c=A\boldsymbol1\), and write \(C=\operatorname{diag}(\boldsymbol c)\), \(G=\operatorname{diag}(\boldsymbol g)\), \(M=CA-AC-A^2\). Use the actual grade-\(j\) column and row spaces \(E_j,W_j\), their zero-profile spaces \(F_j,Z_j\), and polynomial primitives \(J\) from zero and \(J^*\) to one, as in the [two-way saturated flag theorem](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md). \(I=J|_{X=1}\) is the ordinary polynomial mean. All objects act on actual ordered rows, including any silent stages.

**Main finite branch.** There is no such tableau over a characteristic-zero field with exactly two zero entries of \(\boldsymbol g\) at distinct clocks when
\[
     E_2\cap U=0,\qquad \dim(E_3\cap U)=1,
\]
where \(U=\ker G\) is the two-dimensional space on those physical coordinates. No other weight signs, clock distinctness, or edge pattern are assumed. The [prior two-zero theorem](../sdirk-eight-saturation/README.md) forces both distinct zero clocks to be roots of the fourth shifted Legendre polynomial \(L_4(X)=X^4-2X^3+9X^2/7-2X/7+1/70\). The proof below tests all twelve **chronologically directed** pairs of distinct roots. Section 5 rules out all other two-zero branches algebraically. This is a branch exclusion, not a change to the general strict SDIRK order-eight interval **10–11**.

## 1. A weighted duality count produces one literal silent row

At saturation the column-space dimensions for grades \(0,\ldots,7\) are \(1,2,4,6,8,9,10,10\), and the row dimensions agree. Also \(F_{j+2}=ME_j\) and \(Z_{j+2}=W_jM=\operatorname{Ann}(E_{5-j})\), and \(GE_j\subset F_{j+2}\), \(W_jG\subset Z_{j+2}\). The last inclusion follows from pairing through ordinary order after adding the genuine pure quadratic as a diagonal letter. These are identities of spans, not an assumption that a transposed method satisfies ordinary order.

Write \(U_{\mathrm{row}}\) for actual rows supported on the two zero indices. We use the exact identity
\[
 \dim(W_j\cap U_{\mathrm{row}})
      =2-\dim(E_{5-j}\cap U). \tag{1}
\]
Indeed the rank of restricting \(Z_{j+2}=\operatorname{Ann}(E_{5-j})\) to \(U\) is the right side. Right multiplication by \(M\) maps \(W_j\cap U_{\mathrm{row}}\) injectively into that restricted space since the principal block \(M_{UU}\) is triangular with nonzero diagonal. Conversely \(W_jG\) vanishes on \(U\), and has codimension \(\dim(W_j\cap U_{\mathrm{row}})\) in \(Z_{j+2}\) by rank-nullity and \(\dim Z_{j+2}=\dim W_j\). This proves both inequalities. In particular \(W_2\cap U_{\mathrm{row}}\) is a line and \(W_3\) contains both physical supported rows.

For any \(j\), weighting an actual column in \(E_j\) by \(B=\operatorname{diag}(\boldsymbol b)\) puts its transpose in \(W_j\): keep its scalar representative and use ordinary rooted pairing to put its weighted pure part in \(Z_j\). On \(E_3\) this map is injective. To see it, if the weighted column vanishes, its at-most-cubic scalar representative is zero by the first four ordinary scalar probes and the invertible Hilbert matrix. Its pure part belongs to \(F_3=GE_1\). Here \(G\) is injective on \(E_1\subset E_2\), so \(F_3=\langle\boldsymbol g,C\boldsymbol g\rangle\). At least four different clocks carry nonzero output weights by the same Hilbert rank. At least two distinct such clocks are on nonzero-\(g\) rows because there are only two zero rows. Consequently weighting is injective on \(F_3\) too. Dimension now gives \(E_3^{\mathsf T}B=W_3\), and \(E_2^{\mathsf T}B=W_2\).

There has to be a silent row: otherwise invertible coordinate weighting would send the two forward supported axes to the two reverse supported axes, contradicting \(\dim(E_3\cap U)=1\). Conversely every silent coordinate column lies in \(\operatorname{Ann}(W_3)=F_4\) because \(W_3\) is the weighted image. By \(E_2\cap U=0\), \(F_4=GE_2\); the kernel of weighting on this space has dimension \(\dim(W_2\cap U_{\mathrm{row}})=1\), using (1) and the isomorphism \(E_2^{\mathsf T}B\to W_2\). Therefore there is **exactly one** silent row, with chronological index \(\ell\). Neither zero row is silent, since its coordinate row belongs to \(W_3\).

## 2. The three-coordinate packet forces the diagonal and the silent clock

Let the two zero rows be \(i<j\) with clocks \(a,b\), respectively. The genuine line \(W_2\cap U_{\mathrm{row}}\) has quadratic scalar trace proportional to
\[
     r(X)=\frac{L_4(X)}{(X-a)(X-b)}
         =X^2+kX+q,\quad k=a+b-2,\quad q=(a+b)k-ab+9/7 .
\]
Here is the extraction. The last weight is nonzero by trimming against the ten-stage floor. The pure row \(\boldsymbol b^{\mathsf T}M\) has nonzero last component and spans \(Z_2\); hence the last quadratic residual cannot be zero, since that would force the proportional row \(\boldsymbol b^{\mathsf T}G\) to vanish and leave at most two output weights. Thus \(\boldsymbol b^{\mathsf T}G\) itself spans \(Z_2\), and every grade-two row is \(\boldsymbol b^{\mathsf T}P(C)\) plus a multiple of \(\boldsymbol b^{\mathsf T}G\). For the supported row the four observations against \((X-a)(X-b)X^m\) for \(0\le m\le3\) vanish. The scalar trace multiplied by \((X-a)(X-b)\) is therefore proportional to \(L_4\). Its trace cannot be zero, since its only possible pure part already vanishes on \(U\). Normalize the supported row to have trace \(r\). Its two entries are \(b_i r(a)\) and \(b_j r(b)\), nonzero by simplicity of \(L_4\). The same receipt paired with each degree-three Gauss cardinal gives the Gauss weights \(b_i,b_j\), though their precise magnitudes are not needed here.

Take the unique forward preimage \(\boldsymbol w\in E_2\) of this supported row under weighting. It is supported exactly at \(i,j,\ell\), with values \(r(a),r(b),\eta\), where \(\eta\ne0\) by \(E_2\cap U=0\). Its scalar trace is \(r\): weighting preserves scalar profiles, and their uniqueness at grade two comes from ordinary moment detection. Consequently \(\boldsymbol w=r(\boldsymbol c)+\alpha\boldsymbol g\) for some \(\alpha\).

The reverse pure space \(Z_3=W_1G\) vanishes on the two zero rows. Indeed \(W_1\cap U_{\mathrm{row}}=0\): a supported row of grade one would have at-most-linear trace, which is killed by the same four probes against \((X-a)(X-b)X^m\); its degree-one pure part is zero. Compare dimensions in \(W_1G\subset Z_3\). Applying right multiplication by \(A\) to the supported \(W_2\) row therefore reads \(J^*r\) at the later index \(j\). Triangularity sees only its own diagonal at that column. Divide by \(b_jr(b)\ne0\) to obtain
\[
                  \gamma=\frac{(J^*r)(b)}{r(b)}.                 \tag{2}
\]

Forward, \(F_4=GE_2\) vanishes on both zero rows. In particular the earliest zero index is at least five: on its literal prefix the three scalar column probes \(\boldsymbol e_i^{\mathsf T}A^m\), \(m=0,1,2\), on \(\boldsymbol 1,\boldsymbol c,\boldsymbol c^{\odot2}\) have determinant \(-a^6/72\ne0\) and kill the nonzero pure column \(\boldsymbol g\). All four independent columns are in the kernel of the nonzero prefix row \(\boldsymbol e_i^{\mathsf T}M\) by clean grade four. Now let \(d=c_\ell\). Applying \(A\) to \(\boldsymbol w\) and \(C\boldsymbol w\) at \(i\) sees no later zero row. The pure parts at these grades vanish there. Hence
\[
 A_{i\ell}\eta=D,\qquad d A_{i\ell}\eta=N,\qquad
 D=(Jr)(a)-\gamma r(a),\qquad N=(J(Xr))(a)-\gamma a r(a).           \tag{3}
\]
The equations also hold if \(\ell>i\) because that tap is zero. If \(a+b=1\), \(r\) is reflection invariant so (2) gives \(D=0\), whereas the exact replay shows \(N\ne0\) for all four directed reflected pairs. All other directed pairs give \(D\ne0\), so \(\ell<i\) and \(d=N/D\). The replay checks that \(d\ne\gamma\) and \(R=r(\gamma)\ne0\); thus \(\ell\ne1\), the first weight is active, and \(\alpha=-R/g_1\). Every active row outside the two zero stages now lies on the **forced quadratic graph**
\[
                      g_m/g_1=r(c_m)/R .                        \tag{4}
\]
In particular no assumption was made that all graph clocks are different.

## 3. The genuine first three rows eliminate every silent index

Write \(u=(c_2-\gamma)/\gamma\), \(w=(c_3-\gamma)/\gamma\), \(v=A_{32}/\gamma\), and \(\kappa(u)=1+2u-u^2\). Minimality gives \(u\ne0\) because otherwise the first two rows have identical rooted features. The [actual three-row identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) give the following exhaustive alternatives:
\[
\begin{array}{c|cc}
 & w & g_3/g_1\\ \hline
 v=0 &2-u &\kappa(u)\\
 v\ne0 &2u &\kappa(2u)+2vu,
 \quad v\,H(u)=2u(3u-2),\quad H(u)=-2+u+4u^2-u^3 .
\end{array}
\]
For clarity, these identities use only the two-dimensional genuine \(F_3\), whose first two coordinates are independent on \(\boldsymbol g,(A-\gamma I)\boldsymbol g\). The pure \([A,M]\boldsymbol1\) is zero on the first two coordinates (both factors have constant diagonal), so it is zero, giving \(vu(2u-w)=0\) at the third. The same two-coordinate argument gives \((C-\gamma I)\boldsymbol g=\kappa(u)(A-\gamma I)\boldsymbol g\). Reading that at the third produces the displayed cases, deleting duplicated first rows by full stage rank. This derivation does not require the first three weights to be active.

If the third row is active, it is a nonzero-\(g\) row since \(i\ge5\), and (4) then requires one of
\[
\begin{aligned}
S(t)&=R\kappa(t)-r(\gamma(3-t))=0,\\
T(t)&=\left(R\kappa(2t)-r(\gamma(1+2t))\right)H(t)+4Rt^2(3t-2)=0
\end{aligned}
\]
at \(t=u\). The second identity follows by multiplying by \(H(u)\); it does not divide by the adjacent tap or by \(H(u)\).

* If \(\ell=2\), the second clock is \(d\), so \(u=u_d=(d-\gamma)/\gamma\). The third is active, and the exact receipt gives \(S(u_d),T(u_d)\ne0\) in every nonmirror orientation.
* If \(\ell\ne2\), the second is active. Its literal normalized residual \(\kappa(u)\), together with (4) and \(u\ne0\), gives
  \[
              u=\frac{2R-\gamma(2\gamma+k)}{R+\gamma^2}.
  \]
  The exact receipt guards the denominator in all eight nonmirror pairs.
* If \(\ell=3\), the forced third clock is \(d\). The two alternatives require \(u_d=2-u\) or \(u_d=2u\), both rejected by the receipt.
* For any \(\ell\ge4\), the third is active and the exact receipt gives \(S(u),T(u)\ne0\).

Together with the exclusion of \(\ell=1\), this exhausts every possibility.

## 4. Independent exact replay and coefficient domain

Run [check_front.py](check_front.py) with Python 3; it uses only the standard library. It verifies opposite signs of \(70L_4\) on each of four disjoint rational brackets of width \(10^{-20}\), together with reflection symmetry of the brackets; thus every root is identified and every ordered pair is covered. The rational arithmetic is interval arithmetic with exact endpoints and strict division guards. For the four mirror pairs only \(N\) is tested, without dividing by \(D=0\), and the cleared \(T\) avoids an unverified division by \(H\). All eight nonmirror pairs have the following certified signs (site indices sorted by clock, not by physical chronology):

| Pair | \(\gamma,D,d-\gamma,R,R+\gamma^2,S(u_d),T(u_d),u_d-2+u,u_d-2u,S(u),T(u)\) |
|---|---|
| 1,2 | +--+++++--+ |
| 1,3 | +--+++++--+ |
| 2,1 | ++-++------ |
| 2,4 | +-+--++-+++ |
| 3,1 | -+-++-++++- |
| 3,4 | +++-+-++--- |
| 4,2 | -++++------ |
| 4,3 | +-+++-+-+-- |

The mirror signs for \(N\) at \((1,4),(2,3),(3,2),(4,1)\) are respectively \(-,+,+,-\).

The [native signed-box file](../../lean/RKCert/ReviewedNative/SDIRK8TwoZeroLineScalarReceipt.lean) checks every box pair by kernel reduction, binds the evaluated expressions to the field formulas in Section 3, and checks all four bracket-endpoint sign changes. The [native support-rank lemma](../../lean/RKCert/ReviewedNative/TwoSidedSupportRank.lean) proves the finite-dimensional comparison behind (1). Both compiled on Lean/Mathlib 4.36.0 and their four public axiom audits report only the standard quotient, choice, and propositional extensionality axioms. The tableau-to-box reduction and remaining branch exclusions are the mathematical proof in this note, not a single end-to-end Lean theorem, and no other toolchain was checked here. The four brackets contain all complex roots of \(L_4\), since all four are simple real roots. Ordering is used only for this exact sign replay in \(\mathbb R\), not for any tableau algebra. For a proposed tableau over any characteristic-zero field, embed the finite number field \(\mathbb Q(a,b)\) into \(\mathbb C\). Both clocks map to real roots; every tested entry belongs to that number field as a rational expression in \(a,b\), and nonvanishing transfers. No embedding of the entire coefficient field or ordering on it is needed.

## 5. The other two-zero branches are excluded without the scalar scan

In fact no ten-stage strict SDIRK8 tableau in characteristic zero can have **exactly two** quadratic-zero rows, even at coincident clocks. The support identity (1) holds for the two physical coordinates regardless of their clock values. As before, \(F_2\) is spanned by \(\boldsymbol g\), and \(Z_2\) by \(\boldsymbol b^{\mathsf T}G\): the latter follows because \(b_{10}\ne0\) and a terminal zero would leave at most two active rows. Thus both pure spaces vanish at these axes.

### Distinct clocks

The clocks \(a,b\) are both Gauss roots by the prior two-zero theorem. If \(E_2\cap U\ne0\), a nonzero supported vector there must have nonzero scalar trace proportional to \(r=L_4/[(X-a)(X-b)]\), by the four probes in Section 2. Its values at the two zero rows are proportional to \(r(a),r(b)\ne0\). It and its componentwise clock multiple are independent and supported on \(U\), filling both axes in \(E_3\). Now (1) forces \(W_2\cap U_{\mathrm{row}}=0\), which is impossible: weighting the supported degree-two vector gives a row there and is nonzero by invertibility of the degree-two scalar moment system on its nonzero trace. Hence \(E_2\cap U=0\).

The dimension of \(E_3\cap U\) is at least one, by \(GE_3\subset F_5\): if the intersection were zero then \(GE_3=F_5\) would vanish on \(U\), although the \(L_3\) column lies in \(F_5\) and is nonzero at both Gauss clocks. Dimension one is the branch excluded in Sections 1–4. It remains to exclude the possibility that \(E_3\) contains both literal axes.

Here \(F_4=GE_2\) is clean on both zero rows and \(F_3=GE_1\). A nonzero vector supported on just the \(a\)-axis has cubic trace proportional to \(\Pi_a(X)=(X-b)r(X)\) by the four probes against \((X-a)X^m\); likewise the \(b\)-axis has trace \(\Pi_b=(X-a)r(X)\). Thus there are affine polynomials \(H_a,H_b\) such that on every row with \(g_m\ne0\),
\[
             (c_m-b)r(c_m)+g_m H_a(c_m)=0,\qquad
             (c_m-a)r(c_m)+g_m H_b(c_m)=0.
\]
Multiplying the first by \(c_m-a\) and the second by \(c_m-b\) and subtracting shows that the degree-two polynomial \((X-a)H_a-(X-b)H_b\) vanishes at all nonzero-\(g\) clocks. If there are three distinct such clocks, it vanishes identically. Since \(a\ne b\), this gives \(H_a=\lambda(X-b)\) and \(H_b=\lambda(X-a)\). At any nonzero-\(g\) row at least one of those two linear factors is nonzero, so \(r(\boldsymbol c)+\lambda\boldsymbol g\) is supported on \(U\); it is a nonzero vector of \(E_2\) because its zero-row values are \(r(a),r(b)\ne0\). This is a contradiction.

If there are at most two distinct nonzero-\(g\) clocks, four distinct active clocks are still necessary by the Hilbert rank, so there are exactly two, disjoint from \(a,b\). The resulting four-node scalar quadrature has precision seven, and its monic nodal polynomial is orthogonal to degrees at most three, hence is \(L_4\). Thus the two remaining clocks are the roots of \(r\), and \(r(\boldsymbol c)\) itself is a nonzero vector of \(E_2\) supported on \(U\), again a contradiction. This exhausts distinct clocks.

### Coincident clocks

If both zero rows have clock \(a\), the four probes \((X-a)X^m\), \(0\le m\le3\), kill the trace of any supported grade-two column or row. Their pure parts already vanish on \(U\). Consequently \(E_2\cap U=W_2\cap U_{\mathrm{row}}=0\). By (1) both axes must belong to \(E_3\), and \(F_4=GE_2\) is clean on \(U\). A normalized single-coordinate column has uniquely forced scalar trace \(\Pi_a/\Pi_a(a)\) by the same four probes at degree three; if \(a\) is not a Gauss root the trace would be zero and it could not be normalized. The two normalized axes therefore have identical traces. Their difference would be in \(F_3\) and nonzero on \(U\), contrary to \(F_3\subset F_4\).

The same coincident-clock argument in fact rules out **any number greater than one** of zero residuals when they all share a single clock: \(E_2\) and \(W_2\) still miss the whole zero-coordinate space, the general form of (1) uses its dimension in place of two, and the same difference of two normalized axes is impossible. A terminal zero would again force all weights onto just one clock and so cannot invalidate the pure-row argument.

The unrestricted zero-free case, the remaining singleton-zero Gauss cases, and multiple distinct zero clocks with at least three zero rows remain unresolved. No ten-stage general lower endpoint is closed.
