# Two-ended width or a true Laguerre continuation after the forced star

Use the same actual no-mixing, distinct-clock, real strict common-diagonal tied-floor hypotheses as the two companion notes. Separate here the nowhere-zero and zero-residual mechanisms.

## The nowhere-zero branch: the low layer widths are forced

As every stage has nonzero weight, an actual graph sink has \(c_i=1-\gamma\) by the simplifying condition; distinct clocks make the last stage the unique sink. Every stage must have a path to it, and all strict edges join successive residual layers. In particular if there is just one stage in some intermediate layer, every stage in the preceding layer must feed that stage, and every stage in the following layer must receive its sole predecessor from it.

Here is the useful bottleneck obstruction. Suppose two or more distinct clocks are in level \(d-1\), there is a single stage at level \(d\), level \(d+1\) exists, and \([A,M]\) vanishes entrywise at level \(d+1\). For any stage of that last level, its actual entry in \([A,M]\) at a source from level \(d-1\) is its unique length-two path product times
\[
                       2c_{\rm middle}-c_{\rm target}-c_{\rm source}.
\]
All these products are nonzero by the unique-sink observation. Thus vanishing forces all the source clocks equal, a contradiction. This is a literal row identity, not an inference from rank alone.

There are already two different clocks at level one. The first pivot argument gives \([A,M]=0\) entrywise through level three, so a singleton at level two is impossible. Hence \(n_2\ge2\), removing the occupancy premise from the next step. For \(p\ge7\), the next step in the companion note now necessarily gives \([A,M]\mathbf c^{\odot2}=0\) globally and vanishing entrywise through level four. Therefore the same bottleneck argument gives \(n_3\ge2\), since \(D_*\ge m=\lceil p/2\rceil\ge4\). At even order six, \(n_2\ge2\) already contradicts the paid \(E_3\) rank. For tied order seven, levels zero through three now give at least \(1+2+2+2=7\) independent columns of \(E_4\) by the explicit layer Vandermonde, plus the nonzero \(\mathbf v_4\) that debuts at layer four. This contradicts the tied floor dimension \(\dim E_4=7\).

For \(p\ge7\) there is a broader two-ended alternative. The [saturated weighted mirror duality](../../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) gives a genuine order-\(p\) tableau \(A^\star=B_b^{-1}A^\top B_b\) in the reversed chronology at the same floor when all weights are nonzero; here it is again common-diagonal, and its quadratic residual is a nonzero scalar multiple of \(\mathbf g\). Thus it has distinct reflected clocks and single-level feeding, exactly because every original edge joins successive levels. The proved assertions apply to the reversed actual layers as well. In the original orientation:
- The first three and last three interior levels each carry at least two clocks whenever those six levels are distinct.
- The commutator annihilates original clock powers of degrees \(0,1,2\) on the right, and their weighted copies on the left. In fact the reflected commutator is \(-B_b^{-1}[A,M]^\top B_b\), and its reflected clock powers span the same degree-at-most-two clock polynomials.
- The ordinary commutator is zero entrywise on the leading levels through four, and on the trailing levels from \(D_*-4\) onwards.

Every nonzero block of \([A,M]\) would therefore have to join two actual layers distance two, each with at least four distinct clocks: if either side had at most three, the corresponding paid moments and honest Vandermonde rank would kill that block. Since the levels (0,1,2) and the three reflected levels have width at most three by their true polynomial recurrence, such a block must have source at level at least three and target at level at most \(D_*-3\). Consequently \(D_*\ge8\). The mandated two clocks in six boundary interior levels then cost \(D_*+7\) baseline physical stages, and two level widths of at least four cost at least four more because the baseline size at any layer is at most two. Thus
\[
  [A,M]\ne0\qquad\Longrightarrow\qquad
                    D_*\ge8,\quad s\ge D_*+11.                     \tag{5}
\]

If instead \([A,M]=0\) everywhere, the literal recurrence applies through the last layer and gives nonzero \(N^{D_*}\mathbf1\) at the sole terminal stage. This vector is a nonzero multiple of the last coordinate vector, and belongs to \(E_{D_*}\). The latter coordinate vector cannot be in \(E_{p-3}\): the exact annihilator there is the line \(b^{\rm row}M\), whose terminal coefficient is \(-b_s\gamma^2\ne0\). Thus \(D_*\ge p-2\). No interior layer from one to \(D_*-1\) can be a singleton, by taking the first width drop after the two first-level siblings and using the bottleneck argument. Therefore
\[
  [A,M]=0\qquad\Longrightarrow\qquad
                    D_*\ge p-2,\quad s\ge 2D_* .                   \tag{6}
\]
The two alternatives are independent of a minimal residual level count, signed output assumptions, or any numerical tableau search. For example the nowhere-zero singleton no-mixing architecture at tied order eight or ten is impossible: (5) already needs nineteen stages, while (6) needs respectively twelve or sixteen, above their quadratic floors ten and fifteen. At tied order eleven, (5) is also impossible at the floor eighteen; (6) restricts any chart to exactly nine strict layers with width two at every interior layer and one at the ends. This does not assert such a chart exists. No conclusion about a chart with an actual mixed feed or repeated clock is obtained from these width exclusions.

## Prime-order terminal depth excludes the remaining order-eleven architecture

The odd tied case with prime \(p\) cannot occur in this nowhere-zero chart if \(D_*=p-2\). This applies in particular to the only order-eleven chart left by (5) and (6). The proof keeps the exact causal layer horizon rather than using a numerical polynomial solve.

The odd ordered-field sign price makes \(\kappa<0\), because positive \(\kappa\) would propagate one nonzero residual sign on all weighted stages. Put \(q=-\kappa>0\), \(D=D_*\). Choose the first zero of the square bracket in the two-ended level identity along \(\kappa^k\) starting at \(k=m-1\). Then \(B\) vanishes at \(\kappa,\ldots,\kappa^k\) and at \(-1\), distinct numbers, so \(k\le D-1\). Equation (2) of the forced-star note holds. As \(D\) is odd, an even \(k\) would make its right side positive and its left side negative. Thus \(k\) is odd and (2) becomes
\[
             q^D+1-2(q^k+q^{D-k})=0 .
\]
The polynomial in \(q\) is reciprocal, has odd degree and is divisible by \(q+1\). After division by \(q+1\), multiply by \(q^{-(D-1)/2}\): the resulting nonzero symmetric Laurent polynomial is a polynomial of degree \((D-1)/2\) in \(T=q+q^{-1}\). This last assertion follows directly from \(q^{r+1}+q^{-r-1}=T(q^r+q^{-r})-(q^{r-1}+q^{-r+1})\). The necessary relation \(P_\gamma(-\kappa^{-j})=0\) from the two-ended level identity has the form
\[
        (2+\kappa^j+\kappa^{-j})\gamma^2-3\gamma+\tfrac12=0 .
\]
Its coefficients lie in \(\mathbb Q(T)\), so \(\gamma\) has algebraic degree at most \(D-1=p-3\).

Conversely strict chronological degree gives \(N^{p-1}\mathbf1=0\) at this layer horizon. The original paid chain moments, whose formal operator is \(J-\gamma I\), require
\[
 0=\sum_{\ell=0}^{n}\binom n\ell
              \frac{(-\gamma)^{n-\ell}}{(\ell+1)!}
   =\frac{(-\gamma)^n}{n+1} L_n^{(1)}(1/\gamma),
 \qquad n=p-1 .
\]
Here \(L_n^{(1)}(x)=\sum_{\ell=0}^n(-1)^\ell\binom{n+1}{\ell+1}x^\ell/\ell!\). The monic integer scaling \((-1)^n n! L_n^{(1)}(x)\) is Eisenstein at \(p=n+1\): all nonleading binomial coefficients are divisible by the prime, the factors \(n!/\ell!\) are prime to it, and the constant coefficient is \(\pm p\,n!\). Thus \(1/\gamma\) and hence \(\gamma\) have degree \(p-1\), a contradiction. For order eleven this eliminates the width-two chart without making any assertion about mixed or repeated-clock tableaux. At larger prime tied orders the premise \(D=p-2\) still has to be earned separately.

## The zero branch: actual second-level clocks are Laguerre nodes

Use instead \(\kappa=0\) in the forced-star conclusion. The two literal silent donors 2 and 3 have clocks \((2\pm\sqrt2)\gamma\); no later stage reads row 1 and all later stages are exactly clean through rooted degree three. Define the monic node product
\[
 Q_2(x)\coloneqq(x-c_2)(x-c_3)=x^2-4\gamma x+2\gamma^2 .
\]
A later row fed strictly only by those two stages, in particular row 4, pays the exact scalar primitive of \(Q_2\), because its degree-three rooted defect vanishes. The preceding entries in this scalar read vanish, so
\[
           \gamma Q_2(c_i)=\int_0^{c_i}Q_2(x)\,dx.
\]
With \(t=c_i/\gamma\) this is the explicit ordinary Laguerre cubic
\[
                       t^3-9t^2+18t-6=0.                         \tag{7}
\]
This is an actual diagonal consistency equation at each such literal row, not a model stage introduced only for the calculation.

More precisely, \(F_4\) consists of the first three coordinate directions plus \(M\mathbf g\). Indeed the first three coordinate vectors are already paid pure in the star branch; \(F_4=ME_2\) has dimension four; and \(M\mathbf g\) is nonzero at row four. To check the latter and to identify precisely the support, at every \(i>3\),
\[
 (M\mathbf g)_i=-g_1\sum_{j=2,3}a_{ij}(c_j-\gamma),
\]
because row 1 has no direct tap there and rows 2 and 3 are the only other taps to row 1. At a row fed only by 2 and 3, the degree-two exact primitive and row sum make this \(-g_1\gamma^2(1-2t+t^2/2)\). The latter polynomial has no common root with (7): reduction of (7) modulo \(t^2-4t+2\) is \(4-4t\), and \(1\) is not a root of that quadratic. Thus all these direct second-level rows have first rooted defect exactly at degree four. Any row not reading 2 or 3 has no degree-four defect by the same formula. Rows which also mix several zero-residual predecessor types need not satisfy the cubic; no unearned propagation beyond this grade is assumed.

This also excludes the \(\kappa=0\) singleton/no-mixing branch at the order-six floor. Stages 1, 2 and 3 are silent, leaving just three possible output sites; order-six quadrature requires all three distinct sites, and they must be the three Gauss nodes \(1/2,1/2\pm\sqrt{15}/10\) by the ordinary degree-five polynomial orthogonality. Since \(c_6=1-\gamma\), both \(c_4\) and \(\gamma\) lie in \(\mathbb Q(\sqrt{15})\). But (7) is irreducible of degree three over \(\mathbb Q\) by Eisenstein at \(3\), so \(c_4/\gamma\) cannot satisfy it. This separate branch proof has no numerical solver arithmetic and does not assert an unrestricted stage bound or elimination at higher zero-residual orders.
