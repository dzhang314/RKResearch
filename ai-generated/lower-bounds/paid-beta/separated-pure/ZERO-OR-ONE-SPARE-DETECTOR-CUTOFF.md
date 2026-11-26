# A literal early output cutoff with zero or one spare rank

Let \(A\) be strictly lower triangular and let the actual last nonzero coordinate of an output row \(\boldsymbol\beta\) be \(s\), truncating behind it if necessary. Assume it is exact on all rooted profiles through tree size \(r\) for
\[
 \ell_m(P)\coloneqq\frac1{m!}\int_0^1 (1-X)^mP(X)\,dX,\qquad m\ge0,
\]
over a field in which \((m+r)!\ne0\). Use \(E_i\) for the actual rooted span through size \(i+1\), with nominal polynomial from the usual normalized Butcher profile. Define the actual clock diagonal \(C=\operatorname{diag}(A\mathbf1)\), \(Y=I-C\), and \(D=CA-AC-A^2\). Put
\[
 \begin{split}
 \mathbf h_1&\coloneqq(m+1)\boldsymbol\beta A-\boldsymbol\beta Y,\qquad
 \mathbf h_2\coloneqq(m+2)\boldsymbol\beta YA-\boldsymbol\beta Y^2,\\
 \epsilon&\coloneqq[\mathbf h_1\ne0],\qquad
 \eta\coloneqq[c_s=1],\\
 H_i&\coloneqq
   \begin{cases}E_i+K\mathbf e_s&\eta=1,\\E_i&\eta=0.\end{cases}
 \end{split}
\]
If \(\eta=1\), both \(A\) and \(Y\) kill the auxiliary direction \(\mathbf e_s\). It is not required to be outside \(E_i\) in this theorem.

Choose an actual anchor degree \(g\ge0\), and set
\[
 L\coloneqq r-1-g,\qquad k\coloneqq s-L-1,\qquad
 \omega\coloneqq s-\dim H_g-(L-1+\epsilon).
\]
Assume \(L\ge5\), \(k\ge1\), \(\omega\in\{0,1\}\), and \(r-2\ge5\). If the order-eleven threshold extension of the penultimate theorem is not used, assume \(L\ge6\). Let \(N_*\) be an available stage lower bound for each weighted size \(r-1\) and \(r-2\) used below, with the corresponding shifts. A sufficient common choice is
\[
                         N_*=\lceil3(r-2)/2\rceil-2
\]
from the old paid weighted rank baseline. Assume \(k+1<N_*\).

**Theorem.** If \(\omega=0\), or if \(\omega=1\) and the following measured inequality holds for all \(1\le j\le L-1\),
\[
                       \dim H_{g+j}\le\dim H_g+j,                 \tag{1}
\]
then every positive weighted tap \(\boldsymbol\beta A^a\), \(1\le a\le L\), factors on \(H_g\) through the first \(k\) physical coordinates. Equivalently it is zero on every member of \(H_g\) that is zero through row \(k\). Hence at one spare rank, any genuine late positive read forces at least one actual rank spike
\[
                       \dim H_{g+j}=\dim H_g+j+1
                    \quad(1\le j\le L-1).
\]
The theorem does not require model separation at the anchor, a globally singleton clock population, or a prior assertion that any such clock closure is short.

The proof uses the paid penultimate-tap theorem of f5986589… (budget five via 172152e6…), and the Newton word and reweighting calculations of e73766c3… / be02d3f6…. The new point is which actual terminal flags remain when one nominal surplus is present but has not appeared in this band.

## Rank budgets and the short clock closure

Define the reverse row flag by
\[
 R_0\coloneqq K\mathbf h_1,\qquad
 R_{u+1}\coloneqq R_u+R_uA+R_uY+K\mathbf h_2 .
\]
As in the weighted rank proof, \(R_u\) has dimension at least \(u+\epsilon\) and annihilates \(E_i\) whenever \(i+u+2\le r\). It also kills the auxiliary direction whenever it is present. The lower dimension follows from strict growth: a plateau would contain \(\boldsymbol\beta Y\) by the paid second seed and nilpotence of \(A Y^\dagger\), contradicting its nonzero read on \(\mathbf1\). Thus
\[
       \dim H_{g+j}\le \dim H_g+j+\omega\qquad(0\le j\le L-1).
\]
In particular (1) is automatic when \(\omega=0\).

Let \(W_j=\sum_{a=0}^j C^aH_g\), and let \(\delta\) be the first \(j\) at which it stabilizes. Every unstabilized step adds at least one, so under (1)
\[
 H_{g+j}=W_j,\qquad \dim H_{g+j}=\dim H_g+j
                    \quad(0\le j\le\min(\delta,L-1)).              \tag{2}
\]
If \(\delta\le L-2\), any late vector \(\mathbf v\in H_g\) and its iterates \(A^j\mathbf v\), \(0\le j\le\delta\), lie in the invariant \(W_\delta\); they vanish through rows \(k+j\). For a clock component in \(H_{g+\delta}\) with clock different from 1 and nonzero \(\boldsymbol\beta\)-output, the bare last-path identity of length \(L-\delta\) forces its first nonzero coordinate by \(s-(L-\delta)=k+\delta+1\). Thus \(A^j\mathbf v\) has at most \(\delta+1-j\) nonendpoint clock charges. At \(j=\delta\) the penultimate tap \(\boldsymbol\beta A^{L-1}\cdot\mathbf v=0\) kills the sole possible charge, using the \(Y\)-moment of positive degree \(L-1-\delta\) on \(A^\delta\mathbf v\). Descend in \(j\): the already zero taps of lengths \(j+2,\ldots,L\) give at least \(\delta+1-j\) consecutive positive \(Y\)-moments and eliminate all charges by Vandermonde. Thus all positive taps on \(\mathbf v\) vanish.

It suffices to consider \(\delta\ge L-1\), so (2) holds through \(L-1\). Put
\[
                    q\coloneqq r-2,\qquad
                    \mathcal T\coloneqq H_q^\perp .
\]
Here and below \(\perp\) denotes the algebraic row annihilator. Its dimension is \(\epsilon+\omega\le2\). It contains \(\mathbf h_1\).

## What the terminal annihilators can be

If \(\delta=L-1\), \(\mathcal T\) is \(C\)-invariant. Choose a secondary detector \(\boldsymbol\lambda\) independent modulo \(\mathcal T\) in \(H_{q-1}^\perp\), which has dimension \(\dim\mathcal T+1\). Then
\[
 H_{q-1-u}^\perp=\mathcal T+\boldsymbol\lambda P_{\le u}(C)
              \qquad (0\le u\le L-2).                            \tag{3}
\]
All rows on the right annihilate \(H_{q-1-u}\) by the rooted \(C\)-inclusions. Their rank must increase at each step: a plateau would make the preceding row space invariant and hence make its annihilator at that degree invariant, contradicting (2) and that the closure has not stabilized there. This proves the equality by the measured dimensions.

If \(\delta>L-1\), \(\mathcal T\) is not invariant, and the same argument gives
\[
 H_{q-u}^\perp=\mathcal T+\mathcal TC+\cdots+\mathcal TC^u
              \qquad(0\le u\le L-1).                             \tag{4}
\]
Its rank increases by exactly one at each step. When \(\dim\mathcal T=1\), write it as \(K\boldsymbol\lambda\). When \(\dim\mathcal T=2\), there are just two possibilities:
* If it contains an invariant line \(U\), choose \(\boldsymbol\lambda\) outside it. Then (4) is \(U+\boldsymbol\lambda P_{\le u}(C)\).
* If it contains no invariant line, \(\dim(\mathcal T+\mathcal TC)=3\) gives a nonzero row \(\boldsymbol\lambda\in\mathcal T\) with \(\boldsymbol\lambda C\in\mathcal T\). The two rows are independent, since otherwise their line is invariant. Hence (4) is \(\boldsymbol\lambda P_{\le u+1}(C)\).

These are exact descriptions of measured row spaces, not a classification of putative polynomial models.

## A late positive read requires literal detector sites

For a detector \(\boldsymbol\lambda\), group its output on a vector by the physical clocks:
\[
            \Gamma_x(\mathbf v)\coloneqq\sum_{i:c_i=x}\lambda_i v_i.
\]
The common kernel of every \(\Gamma_x\) is \(C\)-invariant. In any of (3), (4), intersect it with the annihilator of the invariant row summand, if present. The result is still \(C\)-invariant and belongs to \(H_g\). On a vector late after \(k\) in that space every clock component is late, and any nonendpoint component has zero \(\boldsymbol\beta\)-output by the penultimate tap:
\(\boldsymbol\beta A^{L-1}\cdot\mathbf u=(m!/(m+L-1)!)(1-x)^{L-1}\boldsymbol\beta\cdot\mathbf u=0\).
The endpoint component has zero positive taps regardless. Thus a true late positive read has a nonzero \(\Gamma\)-response.

Under (3), normalize \(\lambda_s=0\). This is automatic when \(\eta=1\). If \(\eta=0\), then \((\mathbf h_1)_s=-\beta_s(1-c_s)\ne0\) supplies the required subtraction inside \(\mathcal T\). The \(L-1\) consecutive vanished moments on \(\Gamma\) in (3) force at least \(L\) distinct nonzero clock charges. There are just \(L\) physical positions \(k+1,\ldots,s-1\) before the final position. Thus these all support \(\boldsymbol\lambda\), have distinct clocks, and the particular late vector is nonzero at each of them. A clock-local row in \(\mathcal T\) having zero final coefficient must miss this entire tail, because there is only one site of each clock there and the row annihilates the late vector. Since an invariant row space decomposes into its actual clock components, the whole final-zero part of \(\mathcal T\) misses the tail.

If \(\eta=0\), one may therefore choose a single clock-local row \(\boldsymbol\lambda_0\in\mathcal T\) at clock \(c_s\) with nonzero last coordinate; it is the only terminal constraint that affects the tail. All other rows of \(\mathcal T\) are irrelevant there. This is the invariant terminal-hyperplane Newton case, with the last coordinate uniquely determined by the one local row.

If \(\eta=1\), all of \(\mathcal T\) misses the tail. The actual row \(\boldsymbol\zeta=\boldsymbol\beta A\) has weighted size \(r-1\), so its last position \(t>k\) by \(N_*>k+1\). Because \(\mathbf h_1\in\mathcal T\) is supported through \(k\), the row \(\boldsymbol\beta Y=(m+1)\boldsymbol\zeta-\mathbf h_1\) has exactly the same last position \(t\). Hence
\[
           (\mathbf h_2)_t=-\beta_t(1-c_t)^2
                          =-(m+1)\zeta_t(1-c_t)\ne0.
\]
Thus \(\mathbf h_2\in H_{q-1}^\perp\) is independent modulo \(\mathcal T\), and we can take it as the secondary detector in (3). Since the detector has support on the whole literal tail before \(s\), \(t=s-1\). This gives the ordinary augmented Newton case, with \(\mathbf e_s\) ignored by \(\boldsymbol\zeta\). This reasoning applies even if \(\mathbf h_1\ne0\) and the last clock is 1.

Now consider (4). If the row space has the generator with \(P_{\le u+1}\), then at the anchor a nonzero detector response needs at least \(L+2\) labels from only \(L+1\) rows, impossible. Otherwise it has \(\boldsymbol\lambda P_{\le u}\) and possibly one invariant line \(U\). At the anchor a nonzero response needs \(L+1\) labels, filling every physical tail row by a distinct detector support site. This is impossible if \(\eta=1\), when every row in the flag misses \(s\). If \(U\) has nonzero last coefficient, adjust \(\boldsymbol\lambda\) by \(U\) so that it misses \(s\), also impossible. Otherwise that local line must miss the entire tail by the same uniqueness of the clock sites. Thus \(\eta=0\), and the invariant summand, if present, has no effect on the tail. We can rescale \(\boldsymbol\lambda\) so \(\lambda_s=(\mathbf h_1)_s=-\beta_s(1-c_s)\): \(\mathbf h_1\in\mathcal T=U+K\boldsymbol\lambda\) and \(U\) misses \(s\). This is the single terminal-detector Newton case, with no augmentation.

## Why all surviving literal tail patterns are impossible

For clarity, the calculations invoked from the detailed detector proof have the following exact hypotheses and conclusions. If a detector fills \(J+1\) consecutive tail positions with distinct clocks, put \(\nu(X)=\prod_{a=0}^{J}(X-x_a)\), where \(x_a\) are those clocks in chronology. The genuine late line at each successive degree is given on those positions by
\[
   (v_j)_i=\frac{\prod_{a<j}(c_i-x_a)}{\lambda_i\nu'(c_i)}.
\]
This follows from precisely the \(J-j\) paid detector rows in (3) or (4) and the literal zeros. The cases above have \(J=L\) for (4) and \(J=L-1\) for (3). If there is an inactive auxiliary last coordinate, take it zero modulo its available line; if there is a local last-coordinate constraint, lift it uniquely. Any other invariant terminal row misses all those positions and makes no difference. The exact \(Y\)-action is \(Y\mathbf v_j=(1-x_j)\mathbf v_j-\mathbf v_{j+1}\) below the last stage, and \(A\) advances by a single scalar shift \(\alpha_j\) by strictness and the true next rooted space, modulo the auxiliary line only when present. In the full-tail case the terminal Newton vector belongs to the next rooted space by the same identity for \(C\) on its predecessor.

In (4) with no augmentation use terminal row \(\boldsymbol\zeta=\boldsymbol\beta\) and weight shift \(M=m\). In (3) with augmentation use \(\boldsymbol\zeta=\boldsymbol\beta A\), \(M=m+1\). In both cases the last terminal \(\boldsymbol\zeta\)-read is nonzero and the terminal detector is related by a nonzero scalar \(- (1-x_J)\) or \(-(m+1)(1-x_J)\). The paid single-\(Y\) words and the next-tap size floor \(N_*>k+1\) force all shifts \(\alpha_j\ne0\): an internal zero before a visible run would be crossed by \(Y\); a run followed by trailing zeros allows at most one nonzero shift since each preceding clock would have to be 1. In the latter event the actual \(\boldsymbol\zeta A\) ends by \(k+1\), contradicting its weighted size-\((r-1)\) or size-\((r-2)\) floor. The original penultimate \(\boldsymbol\beta A^{L-1}\) is the penultimate read for \(\boldsymbol\zeta\) on this tail. The single-\(Y\) word then gives \(\alpha_j=-1/(M+J-j)\). The pure \(D\)-comparisons force \(\boldsymbol\zeta\cdot\mathbf v_j=0\) for \(1\le j<J\), since the next-next coefficient \(\alpha_j-\alpha_{j+1}-\alpha_j\alpha_{j+1}\) cancels and consecutive clocks differ. The weighted Vandermonde argument makes \(\zeta_i/\lambda_i\) constant on the last \(J\) detector positions. Adding the proper multiple of \(\boldsymbol\lambda\) to \(\boldsymbol\zeta\) deletes all those output coordinates while preserving weighted exactness through size \(r-1\) or \(r-2\), respectively. It is supported by \(k+1\), contradictory to \(N_*\). These calculations are the ordinary and weighted portions of e73766c3… / be02d3f6…, with \(g,L,k\) in place of midpoint variables. They do not require model separation.

In (3) without augmentation, the genuine last lifted vector satisfies \(A\mathbf v_J=\omega_0\mathbf e_s\) with \(J=L-1\); no quotient is used. If \(\omega_0\ne0\), its own one-step paid word implies nonzero last read; any earlier missing shift is contradicted by a single \(Y\) followed by the nonzero run to \(s\). Then the original penultimate \(\boldsymbol\beta A^{L-1}\cdot\mathbf v_0\) is nonzero, contradiction. Therefore \(\omega_0=0\). If there is a last nonzero positive tap of length \(n\ge1\) on \(\mathbf v_0\), its first \(n\) shift coefficients are nonzero, and the one-\(Y\) words of total cost \(n+1\) show \(1-x_i=0\) for every \(i<n\): the \(Y\)-successor term has the zero \((n+1)\)-st response. Yet at the last nonzero \(\boldsymbol\beta\)-read \(\boldsymbol\beta\cdot\mathbf v_j\) (which is at \(j\ge n\)), the one-step exact word also forces \(x_j=1\). This contradicts distinctness of the detector clocks. This is the invariant-hyperplane tail calculation, unchanged by the presence of other invariant rows that have no physical tail read.

Thus every proposed late positive read gives a contradiction. This establishes the measured zero-or-one-spare cutoff. No output rows have been asserted to factor beyond this precise rank and size hypothesis.
