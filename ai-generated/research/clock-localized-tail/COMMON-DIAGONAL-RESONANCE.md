# Removing the common-diagonal resonance loss by one hidden line

This extends the [common-diagonal mixed-word theorem](COMMON-DIAGONAL.md) to the case in which the top shifted moment vanishes. It works over the same paid coefficient fields and does not require nonresonant moments, an ordering, or any extra tableau identity. It uses genuine separated words with one or two strictly causal taps between the two clock operations.

## Statement

Use the common-diagonal tail setting. An actual rooted vector \(\boldsymbol\eta\) is supported on a clock \(\theta\ne1\) and first nonzero at physical row \(\ell\). The actual output \(\boldsymbol\beta\), normalized on \(\boldsymbol\eta\), is last nonzero at row \(t_*\). The tableau has a nonzero common diagonal \(\gamma\) on \([\ell,t_*]\). Define
\[
 \delta\coloneqq1-\theta,\qquad
 \rho\coloneqq\gamma/\delta,\qquad
 T\coloneqq(A-\gamma I)/\delta,\qquad
 C\coloneqq\operatorname{diag}((\mathbf c-\theta\mathbf1)/\delta).
\]
For a Beta shift \(m\ge0\) and paid budget \(L\), the exact word model acts on 1 by multiplication by \(Z\) for \(T\) and by \(P_0(Z)\partial_Z\) for \(C\), where
\[
P_0(Z)\coloneqq (Z+\rho)^2,\qquad
\mu_j\coloneqq\frac{m!}{(m+j)!},\qquad
\nu_j\coloneqq\sum_{a=0}^j\binom ja(-\rho)^{j-a}\mu_a.
\]
The scalar read of \(Z^j\) is \(\nu_j\). These are the actual paid identities of the common-diagonal theorem, from rooted order \(p\) for \(\boldsymbol\eta\in E_d\) when \(d+m+L+1\le p\) and the original output is nonzero.

**Claim.** For \(L\ge6\), there are at least \(L+1\) rows after \(\ell\) and through \(t_*\), even when \(\nu_L=0\). The case \(\nu_L\ne0\) is proved there. The prior resonant argument gives at least \(L\). It remains to exclude exactly \(L\) at resonance.

## The complement can be removed without losing the clock filtration

Suppose \(\nu_L=0\) and precisely \(L\) later rows are available. Work on the literal suffix from \(\ell\) to \(t_*\), with its physical indices shifted to \(0,\ldots,L\). All operations genuinely restrict to it: input has no earlier entry, and output has no later entry. There is only one possible entry of \(T^L\) on this strictly triangular suffix, from its first coordinate to its last coordinate. The equation \(\boldsymbol\beta\cdot T^L\boldsymbol\eta=0\), and the two actual nonzero end entries, therefore imply \(T^L=0\) there. Write \(N\coloneqq L-1\). By the shifted moment recurrence consecutive moments cannot both vanish, so \(\nu_N\ne0\).

Let
\[
 \boldsymbol\eta_i\coloneqq T^i\boldsymbol\eta\quad(0\le i\le N),\qquad
 U\coloneqq\operatorname{span}\{\boldsymbol\eta_0,\ldots,\boldsymbol\eta_N\}.
\]
These are nonzero and have strictly increasing first nonzero physical indices. Thus \(U\) has dimension \(N+1=L\) in a suffix of dimension \(L+1\). The nilpotent \(T\) has a chain of length \(L\) and no chain of length \(L+1\), so its two Jordan blocks have sizes \(L,1\). Define
\[
 W\coloneqq \ker T\cap\ker(\boldsymbol\beta\cdot-).
\]
Since \(\boldsymbol\beta\cdot\boldsymbol\eta_N=\nu_N\ne0\), \(W\) is a line complementary to \(U\). Projection \(\pi\) onto \(U\) along \(W\) commutes with \(T\), and the output kills \(W\). These assertions require no relation between \(C\) and \(W\).

Let \(r\) denote the unique physical index omitted by the first nonzero indices of \(\boldsymbol\eta_i\). Since \(\boldsymbol\eta_0\) starts at 0, \(1\le r\le N+1\). The first nonzero index of \(\boldsymbol\eta_i\) is \(i\) for \(i<r\) and \(i+1\) for \(i\ge r\). Every nonzero \(\mathbf w\in W\) starts at or after \(r-1\): if it started at \(j<r-1\), subtracting a nonzero multiple of \(\boldsymbol\eta_j\) would make it start strictly after \(j\). Applying \(T\) would then make it start strictly after \(j+1\), although \(T\mathbf w=0\) and \(T\boldsymbol\eta_j=\boldsymbol\eta_{j+1}\) starts exactly there.

For each \(i\), let \(U_i\coloneqq\operatorname{span}\{\boldsymbol\eta_i,\ldots,\boldsymbol\eta_N\}\). The projected clock \(\pi C|_U\) preserves every \(U_i\). If \(i<r\), neither the diagonal \(C\) nor subtracting a multiple of \(\mathbf w\) can introduce any entry before the first index of \(U_i\). Within \(U\) that physical cutoff is exactly \(U_i\) by the distinct leading indices. If \(i\ge r\), \(U_i\) already fills the whole physical suffix beginning at its first index, so applying \(C\) stays in \(U_i\) before projection. In particular one need not assume that \(W\) starts at the omitted index rather than one before it.

## Separated reads detect the inverse moment series

Identify \(U\) with the truncated polynomial space \(\mathbb K[Z]/(Z^{N+1})\) via \(\boldsymbol\eta_i\leftrightarrow Z^i\). Define
\[
g(Z)\coloneqq\sum_{j=0}^N\frac{\nu_{N-j}}{\nu_N}Z^j,\qquad
G(Z)\coloneqq g(Z)^{-1},\qquad
Q(Z)\coloneqq P_0(Z)-\rho^2G(Z).
\]
The actual output is \(\nu_N[Z^N](g\,\cdot)\). On this space \(T\) multiplies by \(Z\). Denote the projected clock action by \(\mathcal C\). It is exactly \(Q\partial_Z\). Indeed for \(i\ge1\) the one-clock tests
\(T^kCT^i\boldsymbol\eta\) for \(k\le N-i\) compare it with \(iP_0Z^{i-1}\). The possible formal term at degree \(N+1\) in the scalar powers has zero moment by resonance. Replacing \(P_0\) by \(Q\) changes \(g\,iP_0Z^{i-1}\) by just \(-i\rho^2Z^{i-1}\), invisible at the tested coefficients \(i,\ldots,N\). The projected clock preserves \(U_i\) and \(Q(0)=0\), so this determines its entire action on \(Z^i\). At \(i=0\) both sides are zero because \(C\boldsymbol\eta=0\). Multiplying the derivative by \(Q\) is well-defined modulo \(Z^{N+1}\).

For \(h\ge1\), the actual scalar word \(T^k C T^h C T\boldsymbol\eta\) gives exactly the same read with \(\mathcal C\) at both clocks: the middle \(T^h\) kills the component in \(W\) after the first clock, and the output kills it after the second. The formal model, before any truncation, uses \(P_0\partial_Z\) instead. Define
\[
 R(Z)\coloneqq Q(Z)G'(Z)/G(Z).
\]
The difference of the two inner two-clock polynomials, multiplied by \(g\), is
\[
 h Z^{h-1}(-2\rho^2P_0+\rho^4G)+
 Z^h(-\rho^2P_0'-\rho^2R).
\tag{1}
\]
Indeed \(Q\partial_Z(Z^h Q)=hZ^{h-1}Q^2+Z^h QQ'\), and subtraction uses
\(g(Q^2-P_0^2)=-2\rho^2P_0+\rho^4G\) and
\(g(QQ'-P_0P_0')=-\rho^2P_0'-\rho^2R\).

The budget \(k+h+3\le L=N+1\) compares the coefficients of (1) at \(j=N-k\ge h+2\). The terms involving \(P_0,P_0'\) have degree at most \(h+1\) and cannot reach those coefficients. Therefore, for every \(2\le a\le N-h\),
\[
 [Z^a]R=h\rho^2[Z^{a+1}]G.
\]
Use both \(h=1\) and \(h=2\). It follows that \([Z^a]R=0\) for \(2\le a\le N-2\) and \([Z^j]G=0\) for \(3\le j\le N-1\).

Let \(G_*\) be the quadratic truncation of \(G\) and \(Q_*\coloneqq P_0-\rho^2G_*\). Replacing \(G\) by \(G_*\) in \(QG'/G\) leaves the coefficients through degree \(N-2\) unchanged: differentiation lowers the congruence by at most one and multiplication by \(Q_*\) restores it. The constant term is zero. Hence
\[
 Q_*G_*'=\lambda ZG_*
\]
for a scalar \(\lambda\). Both sides have degree at most three, which is why \(N\ge5\) suffices. Any root of \(G_*\) in a splitting field has multiplicity one or two. Its derivative lowers that multiplicity by one, so divisibility in the last identity forces \(Q_*\) to vanish at the root. Since \(Q_*\) agrees there with \(P_0=(Z+\rho)^2\), every root is \(-\rho\). The constant term of \(G_*\) is one, and thus
\[
 G_*=(1+Z/\rho)^e,\qquad e\in\{0,1,2\}.
\]

If \(e=0\), then \(g\equiv1\pmod{Z^N}\), which gives \(\nu_1=\nu_2=0\), impossible by their recurrence and \(\nu_0=1\). If \(e=1,2\), the inverse coefficients through degree \(N-1\) give
\[
 \nu_i=D(-\rho)^i P(i)\qquad(1\le i\le N)
\]
for a nonzero scalar \(D\), where \(P(i)=1\) for \(e=1\) and \(P(i)=N-i+1\) for \(e=2\). The index \(i=0\) is deliberately left free by this truncated information. Inverting the binomial translation, for \(e\le n\le N\) one obtains
\[
 \mu_n=\rho^n(\nu_0-DP(0)).
\]
The reason is that the \(n\)-th finite difference of \(P\) is zero, so the sum over \(i\ge1\) cancels the missing constant term. But this makes the adjacent ratios of \(\mu_n\) equal to \(\rho\), whereas the paid factorial ratios at \(n=e,e+1\) are \(1/(m+e+1)\) and \(1/(m+e+2)\), distinct. The indices are available since \(e+2\le N\). This contradiction excludes the putative resonant suffix, completing the proof.

## Consequences and remaining boundaries

Combined with the nonresonant proof, the \(L+1\) statement is now uniform in \(\rho\ne0\) for \(L\ge6\), at every clock other than 1. There is no need for any field ordering, a root-of-Laguerre test, clock formation beyond the actual vector, a paid word beyond degree \(L\), or a nonzero weight in the hidden line. The argument needs the two separated words; adjacent clock powers alone leave the hidden-line term. It gives no claim for \(L=4,5\) beyond the earlier results.

For the prefix-rank theorem of seal 3c699221…, the earlier cutoff \(k_-=\max(h_0-1,t-L-1)\) now works for every visible clock except 1, where \(h_0\) is the first stage of the common-diagonal block and \(t\) is the last output. At the even midpoint, every visible clock is already a nonendpoint Gaussian node by the independent formation proof, so all weighted outputs including the ordinary one use \(k_-\) without a diagonal exception. At other grades all positive Beta weights already vanish at the remaining clock 1; they can share the same earlier prefix, even if the ordinary output might need the additional row. The moment rank proof can then use the shifted Hilbert block for \(m=1,\ldots,L\), with rank \(\min(j+1,L)\) instead of \(\min(j+1,L+1)\). No unrestricted numerical stage bound is inferred.

The clock 1 boundary itself is real in the local scalar model. To see the limited scope, take any nonzero rational diagonal \(\gamma\ne1\), one earlier row at clock \(\gamma\), and a suffix of \(L+1\) rows all at clock 1. The strict part on the suffix is the single unit adjacent shift; use the one earlier tap in each suffix row to make its true row sum 1. Let \(\boldsymbol\eta\) be the first suffix coordinate vector and put output weights \((-\gamma)^i\) at its successive suffix coordinates. Then \(\boldsymbol\beta\cdot(A-\gamma I)^i\boldsymbol\eta=(-\gamma)^i\) for \(0\le i\le L\), and every word with a factor \(C_{\mathrm{orig}}-I\) is zero on these reads. This is precisely the local endpoint word data, with just \(L\) later physical rows. The vector is even in \(E_2\): the clock-1 indicator is affine in \(C_{\mathrm{orig}}\) applied to \(\mathbf1\), and subtracting its image under \(A-\gamma I\) leaves the first suffix coordinate. This is not asserted to be a full order-\(p\) tableau. It only rules out proving a stronger endpoint result from these local words and triangular shape alone.
