# Causal delays from complete output-clock groups

Let a real lower triangular Runge–Kutta tableau have ordinary rooted order \(p\). Write \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\), and use normalized vectors
\[
 \mathbf N_t\coloneqq
       \left(\prod_{u\text{ immediate subtree of }t}u!\right)
                           \boldsymbol\Phi_t(A).
\]
Their nominal stage value is \(X^{|t|-1}\). Thus \(\mathbf b\cdot\mathbf N_t=1/|t|\), adjoining a root leaf multiplies by \(C\), and \(\mathbf N_{[u]}=|u|A\mathbf N_u\).

Call a clock label **active** if any row at that clock has nonzero output weight. Call it **contributing** if the sum of the output weights at that clock is nonzero. Let \(\mathcal L\) be the set of the \(K\) distinct active labels and \(k\) the number of contributing labels. At each label put
\[
 \beta_x\coloneqq\sum_{i:c_i=x}b_i,\qquad
 e_t(x)\coloneqq
 \sum_{i:c_i=x}b_i\big((\mathbf N_t)_i-x^{|t|-1}\big),\qquad
 F(X)\coloneqq\prod_{x\in\mathcal L}(X-x).
\]
The definition pools actual output weights, not just labels with nonzero scalar mass.

## The full polynomial description of the unobserved grouped defect

For every tree \(t\) with \(d=|t|\le p\), the order tests with up to \(p-d\) additional root leaves give
\[
                  \sum_{x\in\mathcal L}x^j e_t(x)=0
                                \qquad(0\le j\le p-d).          \tag{1}
\]
If \(p-d+1\ge K\), all \(e_t(x)\) are zero. Otherwise the complete solution space of (1) is
\[
          e_t(x)=\frac{Q_t(x)}{F'(x)},\qquad
          \deg Q_t\le K-p+d-2 .                               \tag{2}
\]
For the proof, the coefficient of \(X^{K-1}\) in Lagrange interpolation gives \(\sum G(x)/F'(x)=0\) for every polynomial \(G\) of degree at most \(K-2\). It proves (1) for (2), and the dimension is exactly the nullity of the weighted evaluation conditions on \(K\) distinct nodes.

Thus the grouped stage sample is exact through \(p-K+1\), whether or not any one row in a group is exact. At the first missing grade \(d=p-K+2\), the residual polynomial in (2) is constant. One nonzero defect is then visible at every active label. Conversely a zero defect at any one fixed label proves that tree's aggregate is exact at every label. If the evidence holds for the entire grade, all groups advance one grade. Over an ordered field a nonzero first-grade defect alternates signs at the clock labels.

More generally, \(K-p+d-1\) independent scalar tests on the residual polynomial suffice, and are necessary to infer the whole grade from (1) alone when this dimension is positive. For example, that many proved zero defect labels suffice, by evaluation. In particular, to use the scalar support count \(k\) in place of \(K\), it suffices to know that the sum of the weighted numerical tree columns at each of the \(K-k\) zero-mass labels is actually zero through grade \(p-k+1\). Scalar cancellation of its weights does not prove this. The companion construction gives strict SDIRK counterexamples and shows why this missing information matters.

## Each complete group gives a lower-order numerical submethod

For a contributing label \(x\), let \(i_x\) be the **last physical index with a nonzero weight at label \(x\)**. Define \(\lambda_x\) as its actual weighted clock-group row divided by \(\beta_x\). It is supported in the leading block of \(i_x\) stages and has sum one. Suppose the group is certified exact through size \(r_x+1\); the unqualified guarantee is \(r_x=p-K\) if positive. Additional grades can instead come from (2) or actual numerical tests.

At nonzero \(x\), the scaled leading matrix \(A_{\le i_x}/x\), with output row \(\lambda_x A_{\le i_x}/x\), is an ordinary order-\(r_x\) submethod in the same triangular class. Indeed the aggregate unary column gives
\(\lambda_x A\mathbf N_u=x^{|u|}/|u|\) through \(|u|\le r_x\); this is exactly the scaled output condition. The output row is an affine combination of actual stage-value rows. Treating it as one physical stiffly accurate row is justified only for a singleton group.

This gives \(i_x\ge {\cal S}_{\rm class}(r_x)\) for any known lower bound on the same class. It also gives the causal bound \(i_x\ge r_x\) over the reals without a library of RK bounds. In fact the linear response before scaling is
\[
                    \lambda_x(\mathrm{Id}-zA_{\le i_x})^{-1}\mathbf1
                              =e^{xz}+O(z^{r_x+1}).
\]
Its numerator has degree at most \(i_x-1\); its denominator has degree at most \(i_x\) and only real roots. For \(x\ne0\) scale \(z\) by \(x\). If the agreement were through degree \(i_x+1\), the first two derivatives beyond numerator degree would force a repeated root of a polynomial \((1+\partial_z)^{i_x}D\) at zero, where \(D\) is the scaled denominator. But \(D\) is real-rooted, and \(P\mapsto P+P'\) reduces all repeated root multiplicities by one and creates only simple new roots. Off the roots this follows from the strictly decreasing logarithmic derivative on each complementary interval; there is one root between each neighboring pair and one before the first root. Thus the required repeated root is impossible.

At \(x=0\) the response instead agrees with \(1\) through degree \(r_x\). If all diagonal entries of the prefix are nonzero, the denominator has degree exactly \(i_x\) and the numerator is strictly smaller. The first \(r_x+1\) coefficients of their difference vanish, so \(i_x\ge r_x+1\). A genuine explicit origin can evade this bound, as it should.

The final indices \(i_x\) of different labels are distinct. Thus for any chosen lower thresholds \(T_x\le i_x\),
\[
             s\ \ge\ T+\#\{x\text{ contributing}:T_x\ge T\}-1
\]
whenever the set on the right is nonempty. This is the chronological group-support tradeoff. It counts a late completion of each label, not its first occurrence.

## Strict SDIRK arithmetic at the causal boundary

For a common diagonal \(\gamma\ne0\), a group of positive certified order \(r_x\) can finish at row \(i_x=r_x\) only if
\[
             L_{r_x}(x/\gamma)=0,\qquad
             L_r(Y)\coloneqq
              \sum_{j=0}^{r}(-1)^j\binom{r}{j}\frac{Y^j}{j!}.
                                                                    \tag{3}
\]
Indeed the coefficient of \(z^{r_x}\) in \(e^{xz}(1-\gamma z)^{r_x}\) is \((-\gamma)^{r_x}L_{r_x}(x/\gamma)\) and the numerator has no term of that degree. Equivalently, with \(N=A-\gamma\mathrm{Id}\), the group pays the actual strict-lower tall moments \(\lambda_x N^j\mathbf1=(-\gamma)^jL_j(x/\gamma)\) through \(r_x\). This follows by the formal substitution \(w=z/(1-\gamma z)\) in the same response. A nonzero such moment certifies a strict dependency path of length at least \(j\) terminating at a stage in that group.

For \(r\ge2\) the polynomial \(L_r\) has no rational root. After multiplying by \(r!\) it has unit leading coefficient, so any rational root is an integer. If that integer is divisible by a prime \(\ell\), the valuation of each nonconstant term is at least
\[
               v_\ell(r!)+j-v_\ell(j!)>v_\ell(r!)
\]
for its degree \(j\ge1\). The constant cannot cancel. The remaining candidates \(1,-1\) are ruled out modulo \(r\): every nonleading coefficient of \(r! L_r\) is divisible by \(r\), and the leading term at either candidate is a unit. Zero is not a root. Also no nonpositive real number is a root, immediately from the displayed alternating coefficients. Thus at those clock labels the causal threshold improves to \(r_x+1\).

This arithmetic can apply even when the clocks are irrational. Suppose \(p=2m\), there are exactly \(m\) contributing sites and no zero-mass active labels, and \(\gamma\) is rational. Those sites are all roots of the shifted Legendre polynomial of degree \(m\), by exact scalar quadrature. If a prime \(\ell\mid m\) does not divide \(\binom{2m}{m}\), every such site is an \(\ell\)-adic unit because the integer shifted Legendre polynomial has unit leading and constant coefficients there. Every root of \(L_m\) has \(\ell\)-adic valuation strictly between zero and one: reduction of \(m!L_m\) modulo \(\ell\) is just its leading monomial, giving positive valuation, and valuation at least one is excluded by the same term estimate above. Thus a Gauss site divided by rational \(\gamma\) cannot satisfy (3). This provides a strict causal delay for every group at this support size, including cases with multiple physical rows per group. Within the order-20 range the criterion applies at \(m=3,5,7,9,10\). It is not a new unrestricted minimum-stage claim.
