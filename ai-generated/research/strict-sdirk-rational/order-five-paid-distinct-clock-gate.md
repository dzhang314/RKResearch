# The remaining five-stage strict SDIRK order-five chart over \(\mathbb Z[1/30]\)

The [repeat exclusion](order-five-paid-all-repeated-clock-exclusion.md) leaves precisely the distinct-clock case. The following is an exact scalar search gate, not a proof of existence or nonexistence.

Use centered chronological nodes \(T=(a,u,v,w,-a)\) in \(S=\mathbb Z[1/30]\), all distinct and with \(\gamma=(a+1)/2\) a unit. For the monic hull \(P(t)=\prod_{x\in T}(t-x)\), let \(H_x=I(P/(t-x))\), with the same uniform centered functional as in the repeat proof. The weight at \(x\) must be \(b_x=H_x/P'(x)\), nonzero and in \(S\). Let \(\alpha t+\beta\) be the affine polynomial with value \(H_a\) at \(a\) and value \(H_u\kappa(u)\) at \(u\). The normalized quadratic defect values are forced:
\[
 \widehat q_x=(\alpha x+\beta)/H_x .
\]
Indeed the three moment equations give the two-dimensional barycentric null space, and the initial two rows fix it. The two remaining scalar equations are the reflected second-row relation and the defect square:
\[
 \widehat q_w=\kappa(-w)\widehat q_{-a},\qquad
 \sum_{x\in T}b_x\widehat q_x^2=0,\qquad
 \widehat q_{-a}\ne0.
\]
Here \(\kappa\) is the polynomial ratio from the repeat proof. They imply the rational normal-form data with \(\lambda=1/\widehat q_{-a}\). Use the archived unique triangular solve to recover \(A\), then check that each entry lies in \(S\). This last integrality condition is not guaranteed by the scalar equations over \(\mathbb Q\).

Two inexpensive architecture-independent filters precede these equations: \(b_{-a}\) and \((u-a)/2\) must be units in \(S\). Any prime outside \(\{2,3,5\}\) dividing the last output weight would make the final stage removable after reduction: lower triangularity ensures it does not feed earlier rows. A prime dividing the first strict-lower entry would make the first two rows independent copies with the same diagonal after reduction. Their rooted-tree columns agree coordinatewise there by induction; combine the two output weights and add their entries in every later row to merge them. In each case the putative specialization would give four stages of order five, contradicting the established common-diagonal floor in that field. Unlike weighted reflection, these two filters specialize the original integral \(A\) directly.

The [follow-up review](distinct-clock-review/README.md) proves new endpoint unit restrictions and excludes the fully reflection-symmetric case. It does not exclude general distinct clocks.
