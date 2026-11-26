# A nonzero third-row cross tap forces mixing or repeated clocks

Consider a real strict common-diagonal RK method of ordinary order \(p\ge6\) at the nonsingular quadratic stage floor, in the tied parities (even, or \(p\equiv3\bmod4\)). Write \(\gamma\ne0\) for its common diagonal, \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\), \(N=A-\gamma I\) and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). A receiving row mixes residual levels if it has two actual nonzero strict taps from predecessors with different \(g\) values. No restriction is put on the tap signs or on noncontributing zeros.

At this stage floor the earlier literal first-three calculation gives, with \(u=(c_2-\gamma)/\gamma\), \(w=(c_3-\gamma)/\gamma\), \(r=a_{32}/\gamma\) and \(\kappa=g_2/g_1=1+2u-u^2\),
\[
 (C-\gamma I)\mathbf g=\kappa N\mathbf g ,
 \qquad
 \begin{cases}
   w=2-u,\quad g_3=g_2,&r=0,\\
   w=2u,\quad r(-2+u+4u^2-u^3)=2u(3u-2),&r\ne0.
 \end{cases}
\]
Here \(u\ne0\), and in the first alternative \(u\notin\{1,2\}\). In the second, if \(a_{31}=0\) then \(r=w=2u\), so
\[
                      u=2\pm\sqrt2,\qquad
                      \kappa=-1\mp2\sqrt2.                       \tag{1}
\]
These formulas are valid whether or not some residuals vanish.

**Claim.** If all literal clocks are pairwise distinct and no receiving row mixes residual levels, then \(a_{32}=0\). In particular a nonzero \(a_{32}\) forces, somewhere in the actual tableau, either repeated clocks or a genuinely mixed receiving row. This is not inferred just from coincident dyadic lengths or an assigned graph layer.

## Nonzero value of \(\kappa\)

The distinct clocks imply \(c_i\ne\gamma\) for \(i>1\), so each of these rows has some strict feed. If all its feeds have residual \(g'\), the first identity gives \(g_i=\kappa g'\). Thus \(\kappa\ne0\) and absence of mixing propagate nonzero residuals to **all** stages, without needing to assume this initially. Also \(\kappa=1\) would propagate the same \(g_1=\gamma^2/2\) everywhere, contradicting \(\mathbf b\cdot\mathbf g=0\). The value \(\kappa=-1\) would propagate \(g_i^2=g_1^2\) everywhere, contradicting the ordinary paid squared defect. It follows that there are distinct levels \(g_i=g_1\kappa^{d_i}\), with nonnegative integer \(d_i\), and every strict tap comes from the immediately preceding level. All actual weights are nonzero by the weighted-support rank argument at the floor.

If \(a_{32}\ne0\), row three cannot also tap the first stage, since \(g_2=\kappa g_1\ne g_1\). So (1) holds. To rule out this concrete adjacency, use the already established two-ended level identity. For clarity the exact ingredients of that identity are the following. Define \(D_*=\max_i d_i\), \(B(t)=\sum_i b_i t^{d_i}\), \(m=\lceil p/2\rceil\), and \(\rho=\kappa^{-D_*}\). Under the exact condition \(b^{\rm row}A=b^{\rm row}(I-C)\), every graph sink has \(c=1-\gamma\) because all weights are nonzero. Thus the last stage is the unique sink, where the level is \(D_*\). Its reflected quadratic defect is \(\rho\mathbf g\): this follows from the pure row \(b^{\rm row}\operatorname{diag}(\mathbf g)\) being proportional to \(b^{\rm row}(CA-AC-A^2)\), and the literal last reflected stage has defect \(\gamma^2/2\). The forward and reflected quadratic moment identities with the grading mask \(\operatorname{diag}(t^{d_i})\) consequently give
\[
 g_1(1+t)\,[\,\rho t(2t+1)-(t+2)\,]B(\kappa t)
    =(t-1)P_\gamma(t)B(t),\qquad
 P_\gamma(t)=\gamma^2(1+t^2)+(3\gamma-2\gamma^2-\tfrac12)t .
\]
No generic polynomial solution classification is needed here. Ordinary pure power moments give \(B(\kappa^{m-1})=0\). Since these successive powers never equal \(-1\) and are all distinct, the displayed identity forces, for some integer \(k\ge m-1\ge2\), the vanishing of the square bracket at \(t=\kappa^k\); otherwise \(B\) would have infinitely many roots, though \(B(1)=1\). The resulting relation is
\[
                     \kappa^{D_*-k}=\frac{2\kappa^k+1}{\kappa^k+2}.  \tag{2}
\]
At that zero \(t\ne-2,-1/2\), so no denominator was discarded.

For either algebraic value in (1), relation (2), which involves only rational coefficients and integer powers, would also hold for the conjugate \(\xi=-1-2\sqrt2\). This conjugation is legitimate without any assumption on the field of the other tableau coefficients: equation (2) itself contains only \(\kappa\) and integers, and can be cleared of denominators in \(\mathbb Q(\sqrt2)\). For \(k\ge2\), the real \(t=\xi^k\) satisfies \(|t|>9\). The right side \((2t+1)/(t+2)=2-3/(t+2)\) lies strictly between \(1\) and \(3\). The left side is an integer power of \(\xi\): a positive such power is either \(1\), has magnitude at least \(|\xi|^2>9\), or has magnitude at most \(|\xi|^{-2}<1/9\). This contradiction rules out the adjacent-only chain, and hence \(a_{32}\ne0\), in the no-mixing singleton chart.

## Zero value of \(\kappa\)

Here the pure relation gives \((C-\gamma I)\mathbf g=0\), so distinct clocks leave \(g_1\) as the sole nonzero residual. If \(a_{32}\ne0\), absence of mixing again forces \(a_{31}=0\), but then (1) contradicts \(\kappa=0\). Hence the first three rows form the same actual star. Both successors have zero residual and the only two possible strict single-parent zero clocks \((2\pm\sqrt2)\gamma\).

In this branch the first three rows are all silent output sites and every later stage is genuinely clean through rooted degree three. To see this, no later stage can tap row 1: adding any other predecessor would mix the sole nonzero level with the zero level, while a sole tap from row 1 with zero residual must reuse one of those two already occupied clocks. Thus \(N\mathbf g\) is supported on exactly stages 2 and 3, with both entries nonzero and their clocks distinct. The genuine pure profiles \(\mathbf g, N\mathbf g,CN\mathbf g\) span the literal first-three coordinate space and are all in \(F_4\). Their annihilation by the ordinary output gives \(b_1=b_2=b_3=0\). Since \(F_3\) has dimension two and is exactly \(\operatorname{span}(\mathbf g,N\mathbf g)\), all its vectors vanish at the later rows, proving the claimed clean grade. This zero branch is not declared impossible, and does not admit division by \(G=\operatorname{diag}(\mathbf g)\).

Therefore the first three rows must be a literal star in either form of the singleton no-mixing chart. In the nonzero branch they exhaust the two possible first-level clocks, so the fourth stage must have level two and tap only rows 2 and 3. The companion note derives an exact physical induction from this star. Neither theorem asserts a new unrestricted minimum or claims that distinct clocks and single-level feeding are consequences of arbitrary RK order.
