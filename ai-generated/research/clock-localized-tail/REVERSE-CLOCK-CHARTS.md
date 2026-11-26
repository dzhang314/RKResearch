# The reverse rows of a maximal-delay explicit tableau form one clock chart

Use the stage-tight setting in the companion MAXIMAL-ODD-CLOCK-DELAY.md, with \(p=2d+1\), \(d\ge6\), \(s=3d+1\). For a row \(\boldsymbol\lambda\), write
\[
 \boldsymbol\lambda P_{\le r}(C)
 \coloneqq \operatorname{span}\{\boldsymbol\lambda C^a:0\le a\le r\}.
\]
Products of a vector \(\mathbf f\) and a numerical subspace mean componentwise products, given by \(\operatorname{diag}(\mathbf f)\) acting on that subspace. Every measured inclusion below concerns actual stage vectors.

## A single terminal detector

If \(\epsilon=0\), set
\[
 q\coloneqq2d-2,\qquad\boldsymbol\lambda\coloneqq\mathbf h_2=-\mathbf bD.
\]
If \(\epsilon=1\) and \(\delta=d\), set
\[
 q\coloneqq2d-1,\qquad\boldsymbol\lambda\coloneqq\mathbf h_1 .
\]
In either case \(H_q\) is a hyperplane with annihilator \(K\boldsymbol\lambda\). In the first case this follows from \(R_1\) of rank one and \(\mathbf bA=\mathbf bY\); the formula \(-\mathbf bD=\mathbf h_2\) results by substituting \(C=I-Y\). In the second case \(R_0\) is the nonzero hyperplane annihilator by definition. Neither hyperplane is clock-invariant, by the exact delay.

For every \(0\le r\le q-d\),
\[
                     H_{q-r}^{\perp}=\boldsymbol\lambda P_{\le r}(C).       \tag{1}
\]
Each displayed row is an annihilator since \(C^a H_{q-r}\subseteq H_q\) for \(a\le r\), and the right rank is exactly \(r+1\). Indeed at the first \(r\) where the orbit failed to grow, its previous span would be clock-invariant of dimension \(r\) and would equal \(H_{q-r+1}^\perp\) by the already proved previous equalities. This would contradict noninvariance of that earlier stage space. Equation (1) is thus valid by induction.

For every actual \(\mathbf f\in E_j\), \(0\le j\le q-d\), equation (1) implies
\[
           \boldsymbol\lambda\operatorname{diag}(\mathbf f)
                         =\boldsymbol\lambda P_{\mathbf f}(C),
           \qquad \deg P_{\mathbf f}\le j.                               \tag{2}
\]
Indeed \(\operatorname{diag}(\mathbf f)H_{q-j}\subseteq H_q\): root sum gives this on \(E_{q-j}\), and if there is an added final basis vector, the diagonal simply preserves its line. Equation (2) follows by moving the diagonal to the row in (1). At every actual stage \(i\) with \(\lambda_i\ne0\), cancellation of the nonzero field entry yields \(f_i=P_{\mathbf f}(c_i)\). In particular two such stages at the same clock agree on all rooted tests through size \(q-d+1\). This is equality of the actual data, not equality of the whole incoming rows.

There is also a reverse feed restriction. For \(0\le j<q-d\), the row \(\boldsymbol\lambda C^jA\) lies in \(\boldsymbol\lambda P_{\le j+1}(C)\) because \(AH_{q-j-1}\subseteq H_{q-j}\). For any column \(i\) not in the support of \(\boldsymbol\lambda\), one has
\[
              \sum_{\ell>i}\lambda_\ell\,c_\ell^j a_{\ell i}=0
              \quad(0\le j<q-d).
\]
If at most \(q-d\) different \(\boldsymbol\lambda\)-supported clocks occur after \(i\), the feeds in this sum vanish separately when pooled by clock, by Vandermonde. Repeated clock labels may still cancel within a group.

For the detector itself, \(\boldsymbol\lambda C^a\cdot\mathbf1=0\) for every \(0\le a\le q\), since \(\boldsymbol\lambda\) kills \(H_q\). Grouping the coordinates of \(\boldsymbol\lambda\) by clock, either all the aggregate values are zero or there are at least \(q+2\) nonzero aggregates, again by Vandermonde. If all aggregates are zero, each supported clock requires two or more actual detector entries, and at least \(q-d+1\) different clocks are supported by (1). These alternatives specify the extra stage information still needed to turn the catalogued reverse detector into an unrestricted exclusion.

## The invariant terminal hyperplane

The remaining case is \(\epsilon=1,\delta=d-1\). Set
\[
 q\coloneqq2d-2,\qquad
 \boldsymbol\lambda_0\coloneqq\mathbf h_1 .
\]
The full clock closure \(H_{q+1}\) is the invariant hyperplane with annihilator \(K\boldsymbol\lambda_0\). As a left eigenvector of the clock diagonal, \(\boldsymbol\lambda_0\) is supported at a single clock \(\theta\). The actual last clock is not 1: if it were 1, the final coordinate would lie outside \(E_d\) by the same paid Gram argument as in the augmented proof, but it would be killed by all \(R_{d-1}\) regardless of \(\epsilon\). The lower dimensions of \(E_d,R_{d-1}\) and that extra coordinate would exceed \(s\). Thus \(1-c_s\ne0\); since \(b_s\ne0\) the last coordinate of \(\boldsymbol\lambda_0=\mathbf bA-\mathbf bY\) is nonzero. It follows that \(\theta=c_s\ne1\). This detector has at least two nonzero entries because it kills \(\mathbf1\).

Choose \(\boldsymbol\lambda\in H_q^\perp\setminus K\boldsymbol\lambda_0\). Then for \(0\le r\le q-d\),
\[
                 H_{q-r}^\perp
                    =K\boldsymbol\lambda_0+
                          \boldsymbol\lambda P_{\le r}(C).               \tag{3}
\]
The proof is the same clock-orbit induction, now modulo the invariant line \(K\boldsymbol\lambda_0\). Each earlier \(H_{q-r}\) is noninvariant through the final one-step growth. In particular the quotient clock orbit supports at least \(q-d+1=d-1\) distinct labels. At least \(d-2\) of these labels differ from \(\theta\) and have nonzero actual \(\boldsymbol\lambda\)-entries.

For \(\mathbf f\in E_j\) with \(0\le j\le d-2\), one still has
\[
 \boldsymbol\lambda\operatorname{diag}(\mathbf f)
     =\boldsymbol\lambda P_{\mathbf f}(C)+a_{\mathbf f}\boldsymbol\lambda_0,
 \qquad \deg P_{\mathbf f}\le j,
 \qquad
 \boldsymbol\lambda_0\operatorname{diag}(\mathbf f)\in K\boldsymbol\lambda_0.  \tag{4}
\]
The first assertion is (3) applied to the rooted product as above. For the second, the row on the left kills \(H_{q+1-j}\). If \(j=0\) this directly gives the assertion. If \(j\ge1\), equation (3) expresses it as a multiple of \(\boldsymbol\lambda_0\) plus \(\boldsymbol\lambda\) times a polynomial of degree at most \(j-1\le d-3\). The latter must vanish on all the at least \(d-2\) distinct effective clocks away from \(\theta\), since the left side is still supported on \(\theta\). It is therefore zero.

In particular every stage in the repeated \(\boldsymbol\lambda_0\)-support at clock \(\theta\) has identical actual rooted data through size \(d-1\), and the \(\boldsymbol\lambda\)-supported rows outside that support obey the polynomial chart in (4). None of these facts alone establishes identical data through the full order, an exact stage deletion, or an unrestricted improved stage count.
