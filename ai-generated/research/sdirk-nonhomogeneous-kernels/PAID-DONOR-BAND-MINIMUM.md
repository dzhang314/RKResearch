# Paid donor error ranks and sharp Laguerre-band stage counts

Use the elementary weights, grading, and invertible \(\Pi=MA-AM-A^2\) of `DENSE-POLYNOMIAL-DONOR-MINIMUM.md`. Let \(m\ge q\ge1\); assume the casts of \(1,\ldots,m-1\) are nonzero in the field. Consider **any** lower triangular prep tableau with every diagonal entry nonzero. Put \(P_n=K[X]_{<n}\). More generally, if a linear decoder \(D:K^s\to U\) lands in any coefficient space \(U\subseteq K[X]\) containing \(P_m\), define the paid error span in that common ambient space by
\[
 \mathcal E_n=\operatorname{span}_K\{g_t-D\Phi_t:|t|\le n\}\subseteq U.
\]
Only its actual intersection with the degree band enters the rank:
\[
 s\ \ge\ \sum_{j\ge0:\ m-2j>0}\big(m-2j-\dim(\mathcal E_{m-2j}\cap P_{m-2j})\big). \tag{A}
\]
Indeed, for each \(j\) choose polynomials \(P_{j,k}\) complementary to \(\mathcal E_{m-2j}\cap P_{m-2j}\) in \(P_{m-2j}\). Their images are independent in \(U/\mathcal E_{m-2j}\). In a relation among \(\Pi^jP_{j,k}(M)\mathbf1\), divide by the least power \(\Pi^j\) present. All remaining columns are paid at grade \(n=m-2j\). Applying \(D\) modulo \(\mathcal E_n\) kills all positive remaining powers (their exact polynomial profile is zero) and detects the independent least-power columns. This proves (A), with no sign, field-ordering, distinct-clock, or depth assumption. In the applications below \(D\) has range in \(P_q\) and is exact through grade \(q\). Then \(\mathcal E_n=0\) for \(n\le q\) and \(\mathcal E_n\subseteq P_n\) for \(n>q\) (a grade-\(a\) model has degree \(a-1\), while the decoded profile has degree at most \(q-1\)). Thus the intersection is the full error span in precisely that scope.
In particular suppose the only extra demand is a band in a fixed monic basis \(W_j\) of degree \(j\): for each tree \(t\) through \(m\), the error belongs to the span of the modes \(W_j\) with \(\max(0,2q+1-|t|)\le j\le |t|-1\). Neither the actual error coefficients nor the physical placement or height is prescribed. For \(q\le m\le2q\), this gives \(\dim\mathcal E_n\le\max(0,2n-2q-1)\) in (A), so
\[
 s\ge \sum_{j\ge0:\ n=m-2j>0}\min(n,2q+1-n)
 = L(m)-\binom{m-q+1}{2}
 =\sum_{k=1}^q\min(k,m+1-k). \tag{B}
\]
For the first equality of counts, set \(d=m-q\). The loss from \(L(m)\) is the sum of positive terms \(2d-1-4j\), namely \(d(d+1)/2\) in both parities of \(d\). For the second, in \(\sum_{k=1}^m\min(k,m+1-k)=L(m)\), the removed terms \(k>q\) equal \(m+1-k\). At caps above \(2q\), apply the bound at \(2q\) to obtain \(q(q+1)/2\). For the Laguerre \(W_j=j!(\mathcal I-\gamma)^j1\) over the split characteristic-zero fields in the companion note, the cached construction there meets (B) for every cap and meets the saturated bound above \(2q\). Thus this is the stage minimum for the paid band, not merely for reconstructing the nominal chart or for a class of adjacent/layered matrices.

At the first excess grade, (A) simplifies to \(s+\dim\mathcal E_{q+1}\ge L(q+1)\). In particular one extra-grade error direction costs at least \(L(q+1)-1\) prep rows. A fully dense minimum-width chart with \(s=L(q)\) must leak at least \(L(q+1)-L(q)=\lceil(q+1)/2\rceil\) independent polynomial directions in that grade. This quantifies the cost of treating the first terminal residual as a single shared mode. Changing chronological depth or admitting nonhomogeneous donors cannot remove that cost while keeping the same chart abstraction. There is no claim that the ordinary scalar endpoint requires this band; a design paying only the actually used ancestor functionals can escape it.
