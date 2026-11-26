# Actual first-row relations and a residual-level obstruction at the tied floor

Take a real nonsingular common-diagonal order-\(p\) tableau at the exact quadratic floor, where both parity sums reach it. The first-row statements need \(p\ge4\); the level statements below need \(p\ge6\). Thus the orders in scope are the even orders, and the odd orders \(p=4h-1\) from seven. Write
\[
 C=\operatorname{diag}(A\mathbf1),\quad
 M=CA-AC-A^2,\quad N=A-\gamma I,\quad
 \mathbf g=A\mathbf c-\tfrac12\mathbf c^{\odot2}.
\]
By floor saturation, \(F_3=ME_1\) has dimension two and \(E_{p-2}\) is full. In particular \(c_2\ne\gamma\), since otherwise the first two stages have identical rooted profiles. The columns \(\mathbf g,N\mathbf g\) span \(F_3\); on the first two coordinates their determinant is \(g_1^2(c_2-\gamma)\ne0\). The pure vector \([A,M]\mathbf1\) vanishes on those two coordinates, since \([A,M]=[N,M+\gamma^2 I]\) is the commutator of two strictly lower triangular matrices. It therefore vanishes identically. Similarly \((C-\gamma I)\mathbf g\) vanishes at the first stage and is a scalar multiple of \(N\mathbf g\), with coefficient read at the second stage. Define
\[
 u=\frac{c_2-\gamma}{\gamma},\quad
 w=\frac{c_3-\gamma}{\gamma},\quad
 r=\frac{a_{32}}{\gamma},\quad
 \kappa=\frac{g_2}{g_1}=1+2u-u^2,\quad
 q=\frac{g_3}{g_1}=1+2w-w^2+2ru .
\]
The actual equations are
\[
       [A,M]\mathbf1=0,\qquad
       (C-\gamma I)\mathbf g=\kappa N\mathbf g,\qquad
       r u(2u-w)=0,\qquad wq=\kappa\,[w+r(\kappa-1)] .               \tag{1}
\]
For the third-coordinate commutator, the literal link coefficient is \(\gamma^3 r u(2u-w)\). The last identity is just the third-coordinate pure relation, with no division by a residual.

The first three rows are consequently constrained to one of these alternatives:
- If \(r=0\), then \(w=2-u\), \(u\ne 0,1,2\), and \(q=\kappa\). Indeed \(w=0\) or \(w=u\) would duplicate an earlier row on every rooted feature; for \(w\ne0\), (1) reduces to \(1+2w-w^2=\kappa\).
- If \(r\ne0\), then \(w=2u\) and
\[
  r(-2+u+4u^2-u^3)=2u(3u-2).
\]
The denominator shown here cannot vanish: \(u\ne0\), and the only further zero of the numerator is \(2/3\), where the denominator is \(4/27\).

Several cross-order physical consequences now follow.
1. If \(c_2=3\gamma\), then \(u=2,\kappa=1\); the first alternative is impossible, and the second gives \(w=4,r=2,q=1\). The first three rows are literally the first three uniform midpoint substeps, with clocks \(\gamma,3\gamma,5\gamma\) and the two third-row preceding taps both \(2\gamma\). If \(i\) is the first later departure from \(g_i=g_1\), (1) becomes \((c_i-\gamma)(g_i-g_1)=0\), since every earlier residual equals \(g_1\). There must be a departure by \(\mathbf b\cdot\mathbf g=0\) and \(\mathbf b\cdot\mathbf1=1\). Hence the first departure repeats the literal clock \(\gamma\). In particular \(c_2=3\gamma\) is impossible when the first clock never recurs, even if subsequent weights have arbitrary signs or zeros.
2. If the third stage is a pure adjacent chain, \(a_{31}=0,a_{32}\ne0\), then \(r=w=2u\) and \(u^2-4u+2=0\), so \(u=2\pm\sqrt2\). These are mandatory values, not claims that those prefixes always extend.
3. If \(g_2=0\), then \(\kappa=0\), (1) localizes **all** nonzero residuals to clock \(\gamma\), and the two admissible third-row alternatives both give \(g_3=0\). If the first clock never recurs, the first row is the sole nonzero residual and is silent. If \(g_2\ne0,g_3=0\), only the second alternative is possible. Substituting its exact \(r,w\) in \(q=0\) gives \(4u^3-12u^2+3u+2=0\), in addition to the nonzero guards already listed. This branch is not declared impossible. Its two degree-two scalar primitive tests at the first zero agree: for \(\gamma=1\), using either \((x-1)(x-1-u)\) or \(z-[1/2+(1-u/2)(x-1)]\) through the first two pairs gives, up to a nonzero constant, the same cubic. Thus counting them twice would not produce a new obstruction.

## A genuine across-order residue-level cost in the nowhere-zero branch

Now assume all residuals are nonzero, the literal clocks are pairwise distinct, and every receiving stage takes nonzero strict feeds from just one residual value. There is no assertion that ordinary order enforces this last restriction. Since \(g\ne0\), all actual weights are nonzero at the tied floor by the weighted-support recurrence. Every stage except the first has preceding feeds, since \(c_i-\gamma\ne0\). Equation (1) shows that the residual multiplies by \(\kappa\) on every actual strict edge: if the preceding residual level is \(g'\), the left weighted tap is \((c_i-\gamma)g'\), so the receiver has \(g_i=\kappa g'\). The value \(\kappa=1\) is already excluded by the first-clock recurrence, and \(\kappa=-1\) would make all \(g_i^2=g_1^2\), contrary to the paid square test. The case \(\kappa=0\) is outside this branch. Thus for real \(\kappa\) the powers are distinct.

Let \(d_i\) be the resulting physical layer, with \(g_i=g_1\kappa^{d_i}\) and \(d_1=0\). Every strict feed joins successive layers. Put
\[
 D(t)=\operatorname{diag}(t^{d_i}),\qquad
 B(t)=\sum_i b_i t^{d_i},\qquad X(t)=\sum_i b_i c_i t^{d_i}.
\]
This \(D(t)\) is a grading mask, not the matrix of output weights. The physical identity \(D(t)N=t N D(t)\) and the exact simplifying condition
\(\mathbf b^{\rm row}A=\mathbf b^{\rm row}(I-C)\) give
\[
 (1+t)X(t)=[\gamma+(1-\gamma)t]B(t).                                \tag{2}
\]
Indeed compute \(\mathbf b^{\rm row}D(t)A\mathbf1\) using the commutation identity and then the simplifying condition. As \(c_1=\gamma,c_s=1-\gamma\) are distinct, \(\gamma\ne1/2\), so \(B(-1)=0\). If \(m=\lceil p/2\rceil\), the order conditions give \(B(\kappa^k)=0\) for \(1\le k\le m-1\) from the genuine pure powers \(\mathbf g^{\odot k}\). All \(m\) roots listed are distinct, and \(B(1)=1\). Consequently there are at least \(m+1\) actual layers. Thus a single-feeding-level, singleton-clock equality method cannot use just the \(m\) levels needed by the univariate \(g\)-moments. At odd tied \(p=4h-1\), \(\kappa>0\) is moreover impossible in this architecture, since it makes all \(g_i>0\) and contradicts the previously proved strict one-sign stage price. The sole-level feed requirement is not needed for consequence 1 above.

## Two-ended refinement: a required relation between the first two rows

Let \(D_*=\max_i d_i\). At an actual sink with no strict successor, the corresponding column of the simplifying condition forces \(c_i=1-\gamma\), because \(b_i\ne0\). Literal clock distinctness makes the last stage the unique sink. Every path increases the layer and reaches that sink, so \(d_s=D_*\) and the leading coefficient of \(B(t)\) is nonzero.

For the following identity only the ordinary weighted adjoint matrix is needed, not a general transpose-preserves-order claim. Define \(A^\star=B_b^{-1}A^\top B_b\) with \(B_b=\operatorname{diag}(\mathbf b)\). Then \(A^\star\mathbf1=\mathbf1-\mathbf c\). The genuine row \(\mathbf b^{\rm row}\operatorname{diag}(\mathbf g)\) lies in the one-dimensional annihilator spanned by \(\mathbf b^{\rm row}M\); as all residuals and weights are nonzero, they are nonzero proportional. Also \(B_b^{-1}M^\top B_b\) is the reflected commutator for \((A^\star,I-C)\). Applying the proportionality to \(\mathbf1\) shows that the reflected quadratic residual is \(\rho\mathbf g\), with \(\rho=g_1/g_s=\kappa^{-D_*}\) by the last physical stage. The reflected off-diagonal matrix obeys \(D(t)(A^\star-\gamma I)=t^{-1}(A^\star-\gamma I)D(t)\).

Write \(Y_2(t)=\sum_i b_i c_i^2t^{d_i}\), \(L(t)=\gamma+(1-\gamma)t\), \(R(t)=(1-\gamma)+\gamma t\), and \(S(t)=R(t)-L(t)\). Applying the two graded simplifying identities respectively to \(\mathbf c\) and \(\mathbf1-\mathbf c\) gives
\[
\begin{split}
 \tfrac12(2t+1)Y_2(t)+g_1B(\kappa t)&=L(t)X(t),\\
 \tfrac12(t+2)\,[Y_2(t)+B(t)-2X(t)]+t\rho g_1B(\kappa t)
                                     &=R(t)[B(t)-X(t)] .
\end{split}
\]
These use exactly \(A\mathbf c=\mathbf c^{\odot2}/2+\mathbf g\) and the reflected corresponding equation. Eliminating \(X,Y_2\) using (2) and \(R^2-L^2=(1+t)S\) yields the following polynomial identity:
\[
 g_1(1+t)\,[\rho t(2t+1)-(t+2)]B(\kappa t)
  =(t-1)P_\gamma(t)B(t),\quad
 P_\gamma(t)=\gamma^2(1+t^2)+(3\gamma-2\gamma^2-\tfrac12)t .          \tag{3}
\]
Starting from \(B(-1)=0\), (3) propagates zeros backwards at \(-\kappa^{-j}\), unless \(P_\gamma(-\kappa^{-j})=0\). These literal arguments are distinct and never \(1\), for real \(\kappa\ne0,\pm1\). A nonzero polynomial cannot have infinitely many of them, so for at least one integer \(j\ge1\)
\[
     (2+\kappa^j+\kappa^{-j})\gamma^2-3\gamma+\tfrac12=0 .           \tag{4}
\]
This is a required concrete relation between \(\gamma=c_1\) and \(\kappa=1+2(c_2-\gamma)/\gamma-((c_2-\gamma)/\gamma)^2\), not only a rank test in unknown higher tableau rows. If \(\kappa>0\), then \(\kappa^j+\kappa^{-j}>2\) and (4) forces \(1/4<\gamma<1/2\); its discriminant further gives \(\kappa^j+\kappa^{-j}\le 5/2\). If \(\kappa<0\) no such interval for \(\gamma\) is asserted regardless of the parity of \(j\). The refined relation requires the genuine single-feeding-level architecture, not merely a temporarily repeated value among the first three stages.
