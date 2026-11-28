# DIRK12/15: a four-singleton dirty end run is impossible in either direction

For a real order-twelve ordinary DIRK with fifteen stages, \(C(2)\), and \(f_5=3\), work in the [four cancelling dirty-pair face](../dirk12-fifteen-rank3-four-cancelling-pairs/README.md). In that face the remaining seven clean physical stages are on the fixed seven-node Lobatto grid. **Exactly two dirty physical stages lie between the first and last interior clean rows.** The two physical end runs contain exactly three distinct dirty labels each. The two-central-dirt case is decided in the [separate companion proof](../dirk12-fifteen-rank3-three-singleton-end-exclusion/README.md). The overall real bound **15–16** is unchanged. No assumption is made that the dirty clocks are disjoint from the Lobatto grid.

Write \(T_j,F_j,\mathcal B_j\) for the actual numerical, pure forward and genuine scalar weighted reverse spaces at grade \(j\), where grade means tree order minus one. Write \(J S(x)=\int_0^x S\), \(J^*S(x)=\int_x^1 S\), and \(I(S)=\int_0^1 S\). The actual reverse primitive in the original coordinates is \(\widehat N=\beta^{-1}A^{\mathsf T}\beta\), with \(\beta\mathbf v=\mathbf b\odot\mathbf v\). Chronological arguments in that direction use the reflected physical ordering and clock. They do not use an unweighted reverse tableau with full rooted order.

## The actual clean-supported profiles

On the four distinct dirty labels \(z\), the two stages have identical nonzero amplitudes \(h_z\) of the cubic defect \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\). Put \(H=\prod_z(X-z)\) and
\[
            L(S)=\sum_z \frac{S(z)}{h_z H'(z)},\qquad \mu_j=L(X^j)\quad(0\le j\le5).
\]
The four nonzero coefficients and four distinct sites make \(L\ne0\), already on \(P_3\), irrespective of dirty/clean clock coincidences. Degree-three interpolation of \(S(z)/h_z\) at the four dirty sites gives the following literal profiles:

- For \(S\in P_5\), there is a clean-supported genuine grade-five state \(S(\mathbf c)-\mathbf h Q(\mathbf c)\) with \(Q\in P_2\) exactly when \(L(S)=0\).
- For \(S\in P_4\), the same holds in grade four with \(Q\in P_1\) exactly when \(L(S)=L(XS)=0\).

Indeed \(L(S)\) is the leading cubic interpolation coefficient by the barycentric formula. Once that coefficient vanishes, \(L(XS)\) is the quadratic coefficient. These are physical states: on both stages of every dirty pair they vanish, and at every clean row their value is \(S\) at its own clock. The true reverse grades four and five give the same normalized states because \(\mathcal B_j=\beta F_j\) on those grades.

List the clean clocks in physical order as
\[
               \gamma_0=0,\ \gamma_1,\ldots,\gamma_5,\ \gamma_6=1,
\]
with no required numerical ordering of the five interior clocks. Put
\[
  F=\prod_{i=0}^2(X-\gamma_i),\qquad G=\prod_{i=4}^6(X-\gamma_i),\qquad
  F_4=(X-\gamma_3)F,\quad G_4=(X-\gamma_3)G.
\]
Write \(\mathbf a=(L(FX^j))_{j=0}^2\) and \(\mathbf d=(L(GX^j))_{j=0}^2\). Both are nonzero. For example, if \(\mathbf a=0\), barycentric separation at the four dirty labels gives \(F(z)=k h_z\) for a constant \(k\ne0\): the four annihilation weights for powers \(0,1,2\) are a one-dimensional line, and the monic cubic \(F\) cannot vanish on all four labels. Consequently the cubic polynomial \(P\) interpolating \(h_z\) is \(F/k\), which vanishes at \(0,\gamma_1\). The grade-three clean profile \(P(\mathbf c)-\mathbf h\) and its grade-four clock lift then vanish physically through the first interior clean row. Their actual primitive reads at that row are \(JP(\gamma_1)\) and \(J(XP)(\gamma_1)\), since the true pure grades four and five vanish there. Writing \(P=X(X-\gamma_1)R\), \(\deg R\le1\), these two zero integrals force \(R=0\) by the definite Gram on affine polynomials, contradiction. Reflection gives \(\mathbf d\ne0\) from the corresponding true reverse grades, with the terminal and last interior clean clock in place of the two forward clocks.

## Two true causal cuts, both paid at \(6+5=11\)

Take grade-five clean-supported states on opposite sides of the physical cut just after \(\gamma_2\), represented by polynomials \(R=G_4\,r\) and \(S=F\,s\), respectively. The grades let \(\deg r\le1,\ \deg s\le2\). Since \(A\) is lower triangular, the actual weighted pair of the earlier state with \(A\) applied to the later state is zero. Rooted order pays the full \(5+6=11\) product, so \(\int RJ S=0\) under \(L(R)=L(S)=0\). Repeat at the cut just after \(\gamma_3\), with \(R=G\,r\), \(S=F_4\,s\), \(\deg r\le2,\ \deg s\le1\).

With respect to ascending monomials the fixed cut matrices are
\[
 M_{ij}=I(G_4 X^i J(FX^j))\quad(0\le i<2,\ 0\le j<3),\qquad
 N_{ij}=I(GX^i J(F_4X^j))\quad(0\le i<3,\ 0\le j<2).
\]
They both have rank two by the fixed arithmetic below. Put
\[
 U=\begin{pmatrix}-\gamma_3&1&0\\0&-\gamma_3&1\end{pmatrix},
 \qquad \Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\]
The first cut says \( \mathbf r^{\mathsf T} M\mathbf s=0\) on \(\ker (U\mathbf d)^{\mathsf T}\) and \(\ker\mathbf a^{\mathsf T}\); the second says \( \mathbf r^{\mathsf T}N\mathbf s=0\) on \(\ker\mathbf d^{\mathsf T}\) and \(\ker(U\mathbf a)^{\mathsf T}\). Neither short functional \(U\mathbf d,U\mathbf a\) can vanish: otherwise the relevant rank-two cut matrix would have to vanish on a two-dimensional kernel in its three-dimensional side. The first cut now puts \(\mathbf a\) on the nonzero line generated by \(M^{\mathsf T}\Omega U\mathbf d\). The second puts \(\mathbf d\) on the nonzero line generated by \(N\Omega U\mathbf a\).

The pair \((\mathbf a,\mathbf d)\) determines \(L|P_5\) uniquely, as \(FP_2\oplus GP_2=P_5\) by the disjoint cubic hulls. For a two-component nonzero \(\mathbf x=(x_0,x_1)\), let \(L_+\) be the functional with \(\mathbf a_+=M^{\mathsf T}\mathbf x,\ \mathbf d_+=0\), and let \(L_-\) be the one with \(\mathbf a_-=0,\ \mathbf d_-=N\Omega U M^{\mathsf T}\mathbf x\). An actual functional therefore has the form
\[
                     L=s L_+ + t L_-,\qquad st\ne0 .
\]
One can choose \(s=1\) by definition of \(\mathbf x\); the homogeneous notation is useful. The unique \(L_+\) is supported as an evaluation functional on the three clean clocks \(\gamma_4,\gamma_5,1\); the mass at such a clock \(u\) is \(\mathbf a_+\) evaluated on the degree-two Lagrange cardinal at \(u\), divided by \(F(u)\). Likewise \(L_-\) is supported on \(0,\gamma_1,\gamma_2\), with masses obtained from \(\mathbf d_-\) and \(G(u)\). These are exact **representations of a functional on \(P_5\)**; they do not move any actual physical dirty node.

## Two early clean primitive equations

For the first forward interior clean row \(u=\gamma_1\), let \(V=X(X-u)\). On \(S=VQ\), \(\deg Q\le2\), impose \(L(S)=L(XS)=0\). The corresponding grade-four state is physically zero through \(u\), so \(JS(u)=0\) because its grade-five discrepancy vanishes at clean rows. The fixed row vector \((\int_0^u V X^j)_{j=0}^2\) therefore lies in the span of \((L(VX^j))_{j=0}^2\) and \((L(V X^{j+1}))_{j=0}^2\). Their three-row determinant is zero, without any independence assumption on the two rows. For the last interior \(\gamma_5\) the analogous equation uses \(V=(X-\gamma_5)(X-1)\), with integral from \(\gamma_5\) to \(1\) and the actual grade-five reverse discrepancy.

The first determinant has no \(t^2\) term: \(L_-\) is supported on \(0,\gamma_1,\gamma_2\), and multiplication by \(V\) kills its first two supports, so its two remaining determinant rows are proportional. By the same reasoning the reverse determinant has no \(s^2\) term. After dividing by the nonzero \(s,t\), these are
\[
   a(\mathbf x)s+b(\mathbf x)t=0,\qquad c(\mathbf x)s+d(\mathbf x)t=0
\]
for four binary quadratic forms. Their coefficients are obtained without any unknown tableau coefficients. The fixed arithmetic proves that \(a,b\) have no common binary projective zero. Hence \([s:t]=[b:-a]\) and \(e=ad-bc=0\).

## The extra dirt-front gates

First suppose the forward end run is four-singleton. Let \(P\ne0\) be the degree-at-most-three polynomial interpolating the four \(h_z\). The actual grade-four state \(C(P(\mathbf c)-\mathbf h)\) is zero on the origin and all its subsequent four first dirty rows, regardless of their order. Thus the primitive is zero through those rows. Its true grade-five discrepancy is in \(\mathbf h P_2(\mathbf c)\), which forces \(J(XP)(z)/h_z\) to agree with a quadratic at all four dirty labels. Substituting the scalar formula for \(L\) gives \(L(J(XP))=0\). Independently, if the reverse end run is four-singleton, the argument starting from the physical terminal, for the masked state \((I-C)(P(\mathbf c)-\mathbf h)\), gives \(L(J^*((1-X)P))=0\) with the actual normalized reverse primitive and pure flag. These tests use grade five, not a clean claim for grade six.

The coefficients of \(P\) are proportional to the signed maximal minors of the \(3\times4\) Hankel matrix \((\mu_{i+j})_{0\le i<3,\,0\le j<4}\). Its rows have rank three because it factors as the degree-two Vandermonde at the four distinct dirty sites, the invertible diagonal of the four weights in \(L\), and the invertible degree-three Vandermonde. The kernel contains \(P\): \(L(X^iP)=\sum_z z^i/H'(z)=0\) for \(i=0,1,2\). Use its cofactor vector \((p_0,p_1,p_2,p_3)\); the two gates are then precisely
\[
 \begin{split}
  g_f&=\sum_{i=0}^{3}p_i\frac{\mu_{i+2}}{i+2}=0,\\
  g_r&=\sum_{i=0}^{3}p_i\left[
    \left(\frac1{i+1}-\frac1{i+2}\right)\mu_0
           -\frac{\mu_{i+1}}{i+1}+\frac{\mu_{i+2}}{i+2}\right]=0 .
 \end{split}
\]
Both are quartic in the \(\mu_j\), hence bidegree \((4,4)\) in \((\mathbf x;(s,t))\). Substituting \(s=b(\mathbf x),t=-a(\mathbf x)\) yields binary degree-twelve forms \(f,g\). The second finite rank check below gives no projective zero of \((e,f)\), and separately none of \((e,g)\). Either four-singleton end is therefore impossible. The preceding chronology restriction already requires at least three singleton labels at each end; hence exactly three at each end and exactly two central dirt rows.

## Fixed-grid arithmetic and exact transfer

The five interior roots of \(L_6'=-42+840X-5040X^2+12600X^3-13860X^4+5544X^5\) reduce modulo \(1013\) to the five distinct residues \(347,468,507,546,667\). For all 120 permutations, the independent Python checker constructs \(M,N\), the moments and both dirt-front forms from monomial antiderivatives. It checks:

1. cut ranks \(2,2\);
2. the degree-three homogeneous coefficient rows from multiplying \(a,b\) by the two degree-one monomials span the four-dimensional binary scalar space;
3. each of two sixteen-row degree-fifteen matrices has full rank: multiply \(e\) by degree-eleven monomials and either \(f\) (forward case) or \(g\) (reverse case) by degree-three monomials.

For exact transfer, divide \(L_6'\) by its leading coefficient, a unit at \(1013\). The real splitting field is generated by roots integral over \(\mathbb Z_{(1013)}\). Choose any prime above \(1013\) in the ring generated by these roots. The reductions of the five roots are exactly the five simple residues, and they are distinct from \(0,1\). All denominators used in the computations are powers/products of their distinct differences and the small integration denominators, hence units at that prime. For any real chronological permutation, its coefficient matrices reduce to one tested permutation. A full-size minor nonzero at this prime is nonzero over the actual field, so each verified full rank holds over \(\mathbb R\). Full binary homogeneous coefficient space excludes a projective common zero by containing both pure powers of the two coordinates. No reduction of an arbitrary tableau coefficient, dirty label, moment, or unknown projective coordinate is used.

    python3 -B check.py

The analytic implication from actual rooted order is mathematical, not an end-to-end native Lean lower-bound theorem. The attempted earlier mixed-jet elimination is not used: pointwise grade-six discrepancy comparison must include the actual clean Lobatto weights, and its apparently independent unweighted gates do not certify any exclusion.
