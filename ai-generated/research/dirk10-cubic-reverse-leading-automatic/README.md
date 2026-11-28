# The cubic decoder's reverse leading actions can be recovered from actual order

This supplement strengthens the [ten-mesh cubic-decoder obstruction](../dirk10-cubic-decoder-ten-mesh-obstruction/README.md). Keep its first three hypotheses (the literal six-row opening, rank-one common cubic decoder, first reflected donors, and consecutive three-port block), but **drop its fourth hypothesis on the reverse leading ansatz**. The fourth hypothesis follows in rational auxiliary coordinates, with no change to the literal tableau. Thus the exclusion of a paid twelve-stage order-ten tableau over \(\mathbb Z[1/210]\) holds in this chart even without choosing the reverse leading actions in advance. This is still not a general DIRK12 lower bound.

The essential proof works on any ten distinct rational sites \(0,1\) and eight proper sites with all the scalar weights nonzero under the same literal six-row three-port geometry. One explicit Jacobi causal branch must be checked separately on any changed mesh.

## Quotient from the actual rooted equations

Use \(F=X(X-u)(X-p)(X-r)\) and the notation of the cubic-decoder obstruction. For any size-\(m\) actual rooted linear combination \(d\), let \(\boldsymbol\Delta\) be the high deviation from its pure polynomial and \(\rho\) the decoded old deviation from the same polynomial. The deviation \(\boldsymbol\Delta-E\rho=d_H-E\Pi d_L\) vanishes at literal merged ports. Put
\[
       \mathbf H_j=K\mathbf W_j-\frac{\mathbf W_{j+1}}{j+1},
           \qquad \mathbf W_j=\mathbf w\odot(\mathbf1-\mathbf x)^j .
\]
The **one-unary-parent** contextual identity in the prior proof uses no reverse leading actions. It gives
\[
   \langle \mathbf H_j,\boldsymbol\Delta-E\rho\rangle=0
           \quad\hbox{when }j\le4,\quad m+1+j\le10 .
\]
The injection scalar term vanishes because the actual size-six pure-zero combination \(A d_0\) has high deviation \(\boldsymbol\eta\), and its leaf contexts already prove \(\boldsymbol\eta\perp\mathbf W_0,\ldots,\mathbf W_4\), again without reverse assumptions.

A bush of size \(m\) yields \(F\) times a monic polynomial of degree \(m-5\) for \(m=5,\ldots,9\); its stage polynomial is literally \(\mathbf x^{m-1}\). It follows that \(\mathbf H_0,\mathbf H_1,\mathbf H_2\) annihilate \(EF\cdot P_4,EF\cdot P_3,EF\cdot P_2\), respectively, where \(P_j\) denotes polynomial evaluations through degree \(j\). These tests have no support on merged ports.

On the six nonports, let \(q\in P_5\) interpolate
\[
            q(x_i)=\frac{\eta_i-Q_\eta(x_i)}{F(x_i)} .
\]
Here \(Q_\eta\in P_3\) interpolates \(0,\eta_u,\eta_p,\eta_r\) at \(0,u,p,r\). The extra leaf contexts at the root of the size-six \(A d_0\) give
\[
 \boldsymbol\Delta_m-E\rho_m
       =EF\cdot E(X^m q+L_m)\quad\text{on nonports},\qquad
       \deg L_m\le m-1 .
\]
Indeed the actual high vector is \(\mathbf x^m\odot\boldsymbol\eta\), and its decoded low vector interpolates \(X^m Q_\eta\) at \(0,u,p,r\). The quotient of the difference between \(X^mQ_\eta\) and its cubic interpolant has degree at most \(m-1\); for \(m=0\) it is zero. The already paid bush tests silence \(L_m\). Thus \(\mathbf H_0\) also annihilates \(EF\cdot E(X^m q)\) for \(0\le m\le3\), and \(\mathbf H_1\) does so for \(0\le m\le2\).

## The first two reverse actions

If \(\deg q\le1\), the polynomial \(Q_\eta+Fq\) has degree at most five, has zero constant, and agrees with \(\boldsymbol\eta\) on all nine high sites. Its degree-four scalar moment orthogonalities then imply that \(\int_0^1 X s(X)^2dX=0\) for the polynomial \(s\in P_4\) defined by \(Q_\eta+Fq=Xs\). The scalar quadrature integrates this polynomial product exactly, and real positivity forces \(s=0\), contradicting \(\eta_u=1\). Thus \(2\le\deg q\le5\). Multiplying it by \(X^{5-\deg q}\) gives the missing leading degree five alongside the bush \(P_4\) tests. Since the six nonports are distinct and \(F\) is nonzero there, \(\mathbf H_0\) vanishes on all physical nonports.

In particular, at the first reflected nonport \(1\), the first chronological row of \(K\) has zero self tap (its weight is nonzero and \(y=0\)). Hence \(\mathbf H_1\) itself vanishes at \(1\). Let \(\bar q\in P_4\) be the restriction interpolant of \(q\) on the **five proper nonports**. If \(\deg\bar q\ge2\), multiplication by \(X^{4-\deg\bar q}\) gives the missing leading degree four alongside the bush \(P_3\) tests. Thus \(\mathbf H_1\) vanishes on the proper nonports too.

The only exception is \(\deg\bar q\le1\). Then \(\widetilde H=Q_\eta+F\bar q\) agrees with \(\boldsymbol\eta\) at every high site except possibly \(1\), is of degree at most five, and vanishes at the origin. Its five scalar moments are all equal (the only possible jump is at \(1\)). Therefore \(\int_0^1(1-X)X^j\widetilde H(X)dX=0\) for \(j=0,\ldots,3\). Writing \(\widetilde H=Xh\), the four linear conditions on \(h\in P_4\) have a one-dimensional kernel: their restriction to \(P_3\) has invertible Gram matrix by real positivity of \(X(1-X)\) on \((0,1)\). The kernel is spanned by the explicitly integrated Jacobi polynomial
\[
             H(X)=X(1-14X+56X^2-84X^3+42X^4).
\]
Since \(\eta_u=1\), this branch would give \(\eta_p=H(p)/H(u)\). The literal causality equation forces
\[
      u^3(2p-u)H(p)-p^3(2u-p)H(u)=0 .
\]
On the old ten-node mesh and first three fixed reflected donors, the [exact replay](check.py) checks all 30 oriented pairs from \(\{-1/6,1/6,1/3,1/2,2/3,5/6\}\), even the zero-pivot pairs: every numerator is nonzero. Thus the exceptional branch is absent on this mesh, and both physical leading actions necessarily hold.

## Gauging the projected ports and cubic density

Changing a high column corresponding to a literal port in \(T\) makes the opposite change in \(-TE\Pi\) at its retained low column. Since \(\Pi\) interpolates literally at each port, this cancels identically after redirection. Equivalently, the merged physical tableau does not depend on the three port rows of \(K\), apart from coefficients already fixed in the low opening; the latter do not change under the cancelling operation.

The actual nonport part of \(\mathbf H_2\) annihilates \(EF\cdot P_2\) from the bushes. In the six-dimensional space of polynomials of degree at most six with zero constant, evaluating at \(u,p,r\) is surjective and has kernel \(F P_2\). Thus one can uniquely assign three port values of \(\mathbf H_2\) so that the complete \(\mathbf H_2\) annihilates \(X,\ldots,X^6\). This choice does not modify any physical nonport entry. The physical terminal entry is zero by the first leading action. Independently set \(\mathbf H_0,\mathbf H_1\) to zero on each port.

These three prescribed linear row actions at each port can be realized in the auxiliary \(K\) using just the first three reflected nonport columns, whose weighted quadratic Vandermonde matrix is nonsingular over \(\mathbb Q\). The port rows come last in reflection, so this respects auxiliary lower triangularity. Even if the auxiliary interpolation coefficients are not all in \(\mathbb Z[1/210]\), every actual physical coefficient is unchanged. The earlier census only uses the nonport rows and the proof of the unpaid literal midpoint tap, so the gauging does not weaken its arithmetic conclusion.

In summary, the assumed reverse leading actions and orthogonal cubic density are merely a choice of gauge for this fixed mesh. Over a different mesh, the explicit exceptional Jacobi ratio might not be excluded; no claim is made about it there. The real positivity argument is an intermediate tool for rational coefficients, not an assertion of the same classification over arbitrary fields.
