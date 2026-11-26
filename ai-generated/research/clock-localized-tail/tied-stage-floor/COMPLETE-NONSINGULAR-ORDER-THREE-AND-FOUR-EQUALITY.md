# Complete real nonsingular DIRK equality classes at orders three and four

This note is algebraic except where it counts real roots. It classifies physical lower triangular tableaux at the quadratic stage floor, with no sign conditions or advance assumption on equal clocks, silent weights or zero quadratic residuals. The strict common-diagonal subclass is explicit.

Write \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). At these floors the simplifying condition
\[
             \mathbf b^{\rm row}A=\mathbf b^{\rm row}(I-C)
\]
is necessary. Indeed the difference row is paid pure at degree one and annihilates \(E_{p-2}\). For order three at two stages the scalar rank already makes \(E_1\) full; for order four at three stages the pure \(M\mathbf1\) direction and two independent scalar directions make \(E_2\) full. Here \(M=CA-AC-A^2\) is nonsingular. A terminal zero weight is impossible, since trimming would retain ordinary order and nonsingularity below the quadratic floor.

## Order three, two stages

There must be two distinct weighted clocks, or the positive two-by-two ordinary quadrature Gram could not have rank two. The two-node polynomial is orthogonal to constants, so the first two moment equations do not by themselves force the nodes to be Gaussian. There are consequently more two-stage DIRK tableaux of order three than the symmetric pair; the exact variable-diagonal parametrization is as follows.

Let the first clock be \(x\) and the last \(y\). Require \(x\ne y\), \(x\ne0\), and \(1-y\ne0\); the latter two conditions ensure nonsingular diagonals. Use the two interpolatory weights for degrees zero and one, require their degree-two moment \(1/3\), and require both weights nonzero. Then
\[
                A=\begin{pmatrix}x&0\\ 2y-1&1-y\end{pmatrix}.
\]
The terminal relation determines the second diagonal and its row sum determines the lower entry. The other column of the simplifying condition follows because both row sides have sum \(1/2\); the remaining order-three chain is then \(\mathbf b\cdot(1-\mathbf c)\odot\mathbf c=1/6\). Thus the condition on the two nodes is exactly \(\int_0^1(t-x)(t-y)\,dt=0\). This permits asymmetric degree-two quadrature.

If the diagonal is common, \(y=1-x\). Then the two nodes must be the roots of \(L_2(t)=t^2-t+1/6\), since \(\int(t-x)(t-y)=0\) with their sum one. Both weights are \(1/2\), and the two real choices of \(x=\gamma\) give \(a_{21}=1-2\gamma\). Both residuals are nonzero and opposite, since \(g_1=\gamma^2/2\) and \(\mathbf b\cdot\mathbf g=0\). In the variable-diagonal two-stage class all weights are also nonzero, so both residuals are nonzero by the same argument.

## Order four, three stages

Write \(x=c_1,y=c_2,z=c_3\) and \(d=a_{22}\). The terminal simplifying equation gives \(a_{33}=1-z\) and
\[
 A(d)=
 \begin{pmatrix}
 x&0&0\\[2pt]
 y-d&d&0\\[2pt]
 2z-1-a_{32}&a_{32}&1-z
 \end{pmatrix},
 \qquad a_{32}=\frac{b_2}{b_3}(1-y-d).
                                                                    \tag{1}
\]
Necessarily \(b_2\ne0\): if it vanished, (1)'s defining column equation forces \(a_{32}=0\), and deleting the unused middle row and column retains order and nonsingularity, against the floor. The first column of the simplifying condition always follows from the other two since their total moment on \(\mathbf1\) is already \(1/2\).

For any weights paying bushy quadrature through degree three and satisfying the simplifying condition, only one more order condition is needed:
\[
                     \mathbf b\cdot(\mathbf c\odot A\mathbf c)=1/8 .
                                                                    \tag{2}
\]
Indeed \(\mathbf b\cdot A\mathbf c=1/6\), \(\mathbf b\cdot A\mathbf c^{\odot2}=1/12\), and \(\mathbf b\cdot A^2\mathbf c=1/6-1/8=1/24\) then follow by applying the simplifying condition. Along with the four bushy moments and (2), these are the full eight conditions through order four. Equivalently the only extra condition is \(\mathbf b\cdot(\mathbf c\odot\mathbf g)=0\), since \(\mathbf b\cdot\mathbf g=0\) already follows.

### Three distinct clocks

Take real distinct \(x,y,z\) with
\[
             \int_0^1(t-x)(t-y)(t-z)\,dt=0 .
\]
Use the unique Lagrange quadrature weights on those three clocks. The integral condition accounts for degree three after interpolation. Keep \(b_2b_3\ne0,\ x\ne0,\ z\ne1\). The left side of (2) on (1) is affine in \(d\) with nonzero coefficient \(b_2(y-x)(y-z)\). Indeed its variable terms are \(b_2 y\,d(y-x)\) and \(-b_2 z\,d(y-x)\). Thus there is exactly one permissible value, namely
\[
 d=\frac{1/8-S_0}{b_2(y-x)(y-z)},\qquad
 S_0=b_1x^3+b_2 y^2 x+b_3 z\,[x(2z-1)+z-z^2]
                           +b_2 z(1-y)(y-x).
\]
Keep it iff \(d\ne0\). This is the complete distinct-clock parametrization. If all weights are nonzero, then every residual is nonzero: if one vanished, the two genuine equations \(\mathbf b\cdot\mathbf g=\mathbf b\cdot(\mathbf c\odot\mathbf g)=0\) would force the other two to vanish, contrary to \(g_1=x^2/2\). If \(b_1=0\), the other two clocks must be the Gauss roots and \(b_2=b_3=1/2\). Then both weighted residuals vanish and the only nonzero residual is the first silent one. For this branch the above formula is also the elementary stage-two relation \(d=y(y/2-x)/(y-x)\).

### Repeated clocks

There must be at least two distinct weighted clocks. If there are exactly two their monic product is orthogonal to constants and linears by degree-three quadrature, so they are the Gauss roots with aggregate weights \(1/2\) each. The possibility \(x=y\) is impossible: the first and second rows give identical rooted profiles by induction, even with different diagonals, because the incoming first-stage coefficient plus the self coefficient is then \(x\). This contradicts full \(E_2\). The possibility \(y=z\) is impossible: the initial singleton weight is \(1/2\), and the two pure equations for \(\mathbf g,\mathbf c\odot\mathbf g\) force \(g_1=0\), contrary to nonsingularity. The **only** repeated-clock family has \(x=z\) one Gauss root, \(y=1-x\) the other, and
\[
 b_2=\tfrac12,\quad b_3\ne0,\quad b_1=\tfrac12-b_3,\qquad
 d=\frac{y(y/2-x)}{y-x},\qquad A=A(d).
\]
The middle scalar equation is \(g_2=0\), which gives this \(d\), and then the equations for the other fibre follow from \(\mathbf b\cdot\mathbf g=0\). Hence (2) holds. The indicated \(d\) is nonzero, since Gauss nodes cannot have \(y=2x\) (their sum is \(1\) and product \(1/6\)); \(x,1-z=y\) are also nonzero. No distinct-clock or full-weight assumption has been used to discard a zero-residual case.

### Strict common diagonal: exactly three real tableaux

The repeated family cannot be strict common-diagonal, since its outer diagonals are \(x,y\) distinct. In a distinct-clock common-diagonal method the outer clocks are \(\gamma,1-\gamma\), and \(b_1\ne0\); otherwise the last two clocks are Gauss and the middle clock equals the first. The quadratic Gauss choice for the outer pair is impossible as well, because the middle interpolatory weight would be zero. In centered coordinates, integrating the cubic node product gives
\[
      -(y-\tfrac12)\bigl(\tfrac1{12}-(\gamma-\tfrac12)^2\bigr)=0 .
\]
Thus \(y=1/2\) and the outer weights agree,
\[
        b_1=b_3=w=\frac1{6(2\gamma-1)^2},\qquad b_2=1-2w.
\]
The two paid pure equations now require \(g_3=g_1\), since the middle clock is centered between the outer two. Direct substitution gives
\(g_3-g_1=(1/2-\gamma)(a_{32}+4\gamma-1)\).
Hence \(a_{32}=1-4\gamma,\ a_{31}=2\gamma\), and the remaining simplifying column equation is exactly
\[
                 3d_*^3-3d_*+1=0,\qquad d_*=1-2\gamma .
\]
Conversely every real root gives the stated weights and rows \((\gamma),(1/2-\gamma,\gamma),(2\gamma,1-4\gamma,\gamma)\) and passes all the exact conditions above. The cubic has one root in each of \((-2,-1)\), \((0,1/2)\), \((1/\sqrt3,1)\) by endpoint signs, and no others. None is \(0,1,\pm1/\sqrt3\), so the steps and the middle weight are all defined and nonzero. The floor class has exactly three real physical tableaux, all in the nowhere-zero quadratic residual branch. This counts and excludes the other equality charts, rather than claiming priority for the classical individual tableau formulas.
