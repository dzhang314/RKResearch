# Eliminating stages by relations among stage derivatives

Let \(K\) be a field, and let \(A\) be lower triangular. Write \(N\coloneqq A^\mathsf T\). The Butcher weight vectors have the recurrences
\[
 \boldsymbol\Phi_{\bullet}(A)\coloneqq\mathbf1,\qquad
 \boldsymbol\Phi_{[t]}(A)\coloneqq A\boldsymbol\Phi_t(A),\qquad
 \boldsymbol\Phi_{t\#u}(A)\coloneqq\boldsymbol\Phi_t(A)\odot\boldsymbol\Phi_u(A).
\]
For the degree counts in these notes, set
\[
 d(t)\coloneqq |t|-1,\qquad
 E_h\coloneqq\operatorname{span}_K\{\boldsymbol\Phi_t(A):d(t)\le h\}.
\]
These are the unnormalized numerical tree vectors. Normalization by invertible tree factorials does not change the spaces or the tests below.

## One or several actual derivative relations

Suppose \(\mathbf q\cdot\boldsymbol\Phi_t(A)=0\) for all \(|t|\le p\). Let \(i\) be the last nonzero coordinate of \(\mathbf q\). Let \(R\) delete coordinate \(i\); let \(L\) restore a vector on the surviving coordinates by the formula
\[
 (L\mathbf x)_i\coloneqq -\frac{1}{q_i}\sum_{k<i} q_k x_k,
\]
where the surviving coordinates in \(\mathbf x\) retain their original labels. Set
\[
 A_*\coloneqq RAL,\qquad \mathbf b_*\coloneqq L^\mathsf T\mathbf b.
\]
Then \(\boldsymbol\Phi_t(A_*)=R\boldsymbol\Phi_t(A)\) and \(\mathbf b_*\cdot\boldsymbol\Phi_t(A_*)=\mathbf b\cdot\boldsymbol\Phi_t(A)\) for all \(|t|\le p\). In fact, preservation of the retained vectors needs the relation only through \(|t|\le p-1\); under this weaker hypothesis the output still agrees if \(b_i=0\), or more generally if the remaining output discrepancy \(\mathbf b\cdot(I-LR)\boldsymbol\Phi_t(A)\) vanishes at order \(p\).

Indeed, \(LR\boldsymbol\Phi_t(A)=\boldsymbol\Phi_t(A)\) for each child to which the relation applies. Thus the extension recurrence on the retained coordinates is \(RALR\boldsymbol\Phi_t(A)=RA\boldsymbol\Phi_t(A)\). Restriction \(R\) commutes with coordinatewise products, even though restoration \(L\) need not. This proves the retained-vector assertion by induction. The output assertion then follows from the definition of \(\mathbf b_*\). The only changed columns in retained row \(k\) are earlier than \(i\), and they can change only if \(A_{ki}\ne0\), so \(k>i\). The diagonal of each retained row is unchanged. Thus the result stays in ERK, DIRK or SDIRK, including any requirement that remaining diagonal entries be nonzero.

If a space \(W\subseteq E_{p-1}^{\perp}\) of relations has dimension \(m\), apply the same argument to a reduced-echelon basis with columns ordered from last to first. Each omitted pivot is expressed in earlier **retained** coordinates, since all other pivot entries in its expression are zero. This removes \(m\) stages at once. The statement and its proof hold over a commutative unital ring if the specified echelon pivots are units. No clock condition or invariance of the relation is needed once the required tree evaluations vanish.

Over a field there is a sharp weaker criterion when the output weights are free to change. Suppose the deletion relations annihilate \(E_{p-2}\), and write \(D\) for the set of deleted coordinates. The retained vectors through order \(p\) are still unchanged. Some \(\mathbf b_*\) preserves all the original output coefficients through order \(p\) if and only if
\[
 \mathbf b\cdot\mathbf z=0\qquad\text{for all }\mathbf z\in E_{p-1}\cap K^D.
\]
Indeed the output functional on \(E_{p-1}\) must descend through restriction \(R\), whose kernel there is exactly the indicated intersection. If it descends, extend the functional from \(R E_{p-1}\) to all retained coordinates. For a single deleted coordinate with \(b_i\ne0\), this is exactly the test \(\mathbf e_i\notin E_{p-1}\). It characterizes this deletion with unchanged retained tree values, not every way of finding a smaller tableau. In particular, a stage-minimal order-\(p\) tableau necessarily has \(E_{p-1}=K^s\), by the preceding direct elimination. Any rightmost pivot of a nonzero relation in \(E_{p-2}^\perp\) in such a tableau must occur in the support of \(\mathbf b\); otherwise it could be eliminated too.

With coefficients in a ring, descent is necessary but extension is a separate condition. It holds, for example, if the image \(R E_{p-1}\) is a direct summand of the retained coordinate module. To see why unit pivots alone do not suffice, work in \(\mathbb Z[1/2]\) and take a three-stage explicit order-two tableau with \(a_{21}=\ell\), \(a_{31}=1/2\), all other entries zero, and \(\mathbf b=\mathbf e_3\), where \(\ell\) is an odd prime. The relation \(\mathbf e_3-\mathbf e_1\) permits the third coordinate to be removed and the original output functional descends. A replacement output nevertheless requires \(\ell b_2=1/2\), which has no solution in this ring. See [the audit](COCLOCK-AUDIT.md) for the descent calculation.

## A finite two-sided cutoff

A relation may be available at fewer orders than the desired output order. A shortfall can be paid by an independent condition on how the affected stage contributes to the output. Assume \(\mathbf q\in E_h^\perp\), where \(0\le h<H\) and \(H\coloneqq p-1\). Set \(r\coloneqq H-h-1\). An output context is a vector obtained from \(\mathbf b\) by any sequence of the operations \(N\) and \(\operatorname{diag}(\boldsymbol\Phi_v(A))\). The cost of the first operation is one, and that of the second is \(d(v)\). Assume that the \(i\)-th entry of every output context of total cost at most \(r\) is zero. This includes \(b_i=0\). If
\[
 H<2(h+2),
\]
then the same chronological deletion preserves every output condition through order \(p\).

To prove this, it is convenient to work before the irrelevant row and column are physically removed. Define
\[
 T\coloneqq LR=I-\frac{\mathbf e_i\mathbf q^\mathsf T}{q_i},\qquad
 \widetilde A\coloneqq AT,\qquad
 \widetilde{\mathbf b}\coloneqq T^\mathsf T\mathbf b=\mathbf b,
\]
\[
 \mathbf u\coloneqq A\mathbf e_i,\qquad
 \rho_t\coloneqq\frac{\mathbf q\cdot\boldsymbol\Phi_t(A)}{q_i},\qquad
 \boldsymbol\Delta_t\coloneqq\boldsymbol\Phi_t(\widetilde A)-\boldsymbol\Phi_t(A).
\]
The \(i\)-th column of \(\widetilde A\) and the \(i\)-th entry of \(\widetilde{\mathbf b}\) are zero, so it gives the same output as the reduced tableau. The exact extension identity is
\[
 \boldsymbol\Delta_{[t]}=\widetilde A\boldsymbol\Delta_t-\mathbf u\rho_t.
\]
It implies inductively that \(\boldsymbol\Delta_t=0\) for \(d(t)\le h+1\). In a rooted sum of total degree at most \(H\), a product with two changed factors is zero: each nonzero changed factor has degree at least \(h+2\). Consequently the output discrepancy is a sum of individual terms, each propagated from some \(-\mathbf u\rho_t\) by \(\widetilde A\) along the path to the root and by original, unchanged side factors from the other branches. A nonzero \(\rho_t\) requires \(d(t)\ge h+1\). The remaining cost, including the extension at which \(\mathbf u\rho_t\) first appears, is at most \(r\).

For each term, move the operations along that path onto the output covector. The operations there are \(\widetilde A^\mathsf T\) and original tree diagonal multipliers. At the costs under consideration, \(\widetilde A^\mathsf T\) gives the same output contexts as \(N\): for any preceding context \(\mathbf z\),
\[
 \widetilde A^\mathsf T\mathbf z=N\mathbf z-\frac{(N\mathbf z)_i}{q_i}\mathbf q,
\]
and \((N\mathbf z)_i=0\) by the hypothesis at the next cost. The last pairing is \(\mathbf z\cdot\mathbf u=(N\mathbf z)_i=0\), since that final operation also lies within the cost budget. Every term is zero, as claimed.

If \(\mathbf q\) comes from a genuine reverse mark at cost \(j\), the order conditions give \(\mathbf q\in E_{p-1-j}^\perp\). The condition above therefore uses ordinary output contexts only through cost \(j-1\), and applies whenever \(2j<p+3\). If the reverse mark space used in an application contains *all* zero-model contexts of this cost, one may check \(b_i=0\) and vanishing of that measured mark space at \(i\): the polynomial model of an ordinary context is realized by \(\mathbf b\) times a clock polynomial, which vanishes at \(i\) when \(b_i=0\). A truncated word space need not contain all these discrepancies.

There are two variations without the inequality \(H<2(h+2)\).

* The exact telescoping identity for a product replaces one factor at a time, with changed factors to its left and original factors to its right. The proof goes through for arbitrary \(H\) if the low-cost output test includes diagonal multiplication by tree vectors from **either** \(A\) or \(\widetilde A\) at each step. The test still needs those sibling vectors only through cost \(r\), not through \(H\). Its conclusion is sufficient, not necessary; cancellations across paths have not been used.
* Let \(D_i\) be the shortest length of a strict dependency path from \(i\) to a surviving stage with a nonzero original output weight. The edges are \(j\to k\) for \(j<k\) and \(A_{kj}\ne0\). Include length zero if \(b_i\ne0\), and put \(D_i=\infty\) if no such path exists. If \(h+1+D_i>H\), the deletion is safe without any context test. Indeed, the first effect at a retained stage has traveled at least one edge from \(i\); further extension can move it only along a chronological dependency, and a coordinatewise product cannot move it to a different stage. Redirection to columns earlier than \(i\) creates no new path from the removed stage. An output error therefore has degree at least \(h+1+D_i\), including the direct output correction when \(D_i=0\).

Both statements concern preservation of the algebraic order conditions and leave the diagonal class unchanged. Neither claims stability properties or equality at orders not covered by its hypotheses.
