# Paid co-clock lines that do not suffice for stage removal

The examples use exact formal tree relations over a characteristic-zero field. All diagonal entries can be nonzero. They separate three facts: a co-clock linear relation can be invisible to many low tree orders; even a genuine first reverse residual need not give a full tree relation; and direct output substitution from an actual, split observed line can lose the last paid output order.

Fix \(d\ge2\). Begin with a DIRK tableau \((A_0,\mathbf b_0)\) of order at least \(2d+1\), with
\[
 A_0^\mathsf T\mathbf b_0=\mathbf b_0\odot(\mathbf1-A_0\mathbf1).
\]
Such bases exist for arbitrarily large \(d\) over the real algebraic numbers. For example, compose implicit midpoint with step fractions \(\alpha_i\) summing to one. Then \(b_{0,i}=\alpha_i\), the diagonal entries are \(\alpha_i/2\), and the entries left of each diagonal are the preceding step fractions. The displayed identity follows by summing the remaining fractions at each column. For completeness, the standard symmetric composition order induction follows directly in the formal one-step series: if a symmetric method has order \(2k\), composing three copies with fractions \(\alpha,\beta,\alpha\) multiplies its first possible error coefficient by \(2\alpha^{2k+1}+\beta^{2k+1}\) when \(2\alpha+\beta=1\). At that degree the exact flows compose and the three leading errors add, since transport through a step changes each leading error only at the next degree. Choose both fractions nonzero to make the sum of powers zero, for instance \(\alpha=1/(2-2^{1/(2k+1)})\), \(\beta=-2^{1/(2k+1)}\alpha\). A symmetric method cannot have a first local error of even degree: in the product with its negative-step copy such an error would appear twice, contradicting exact inversion. The symmetric threefold composition therefore has order at least \(2k+2\). Starting from implicit midpoint gives the desired bases and keeps every fraction nonzero.

## Put the first detectable contrast at a prescribed degree

Append \(d\) probe rows with distinct clocks \(z_1,\ldots,z_d\). Each probe has a fixed nonzero diagonal \(\gamma\) and reads only the first old stage, with coefficient \(z_i-\gamma\). Give these rows zero output weight. Let \(A_P\) be the resulting prefix. For each tree \(t\), its values on the probes are evaluations of a polynomial in the probe clock of degree at most \(d(t)=|t|-1\). The base vector is constant. Extension takes a probe polynomial \(P(X)\) to \((X-\gamma)(\boldsymbol\Phi_t(A_0))_1+\gamma P(X)\), and rooted sum multiplies the polynomials. This proves the degree bound.

Choose a vector \(\mathbf v\) supported on the probes with moments zero through degree \(d-2\) and moment one at degree \(d-1\). The independent clock labels give an invertible Vandermonde system. Then
\[
 \mathbf v\cdot\boldsymbol\Phi_t(A_P)=0\quad(d(t)\le d-2),
\]
and this pairing equals one on the bushy tree of degree \(d-1\), whose probe values are \(z_i^{d-1}\).

Now append a block of three receivers at a common clock \(c\), with common nonzero diagonal \(\eta\). A receiver labeled \(\theta\in\{0,1,2\}\) reads the physical prefix with coefficients \(\mathbf u+\theta\mathbf v\), where \(\mathbf1\cdot\mathbf u=c-\eta\), and has no other feed from receiver rows. Let \(\mathbf q\) have values \((1,-2,1)\) on this block and be zero elsewhere. Then \(\mathbf1\cdot\mathbf q=0\), \(A^\mathsf T\mathbf q=\eta\mathbf q\), and \(Y\mathbf q=(1-c)\mathbf q\). The first equality kills the common part of the prefix reads, and \(\sum_\theta q_\theta\theta=0\) kills their linear variation.

The receiver values for each tree are given by a polynomial \(P_t(\theta)\). They satisfy
\[
 P_{[t]}(X)=\mathbf u\cdot\boldsymbol\Phi_t(A_P)+X\bigl(\mathbf v\cdot\boldsymbol\Phi_t(A_P)\bigr)+\eta P_t(X),
 \qquad P_{t\#u}=P_tP_u.
\]
Induction gives \(\deg P_t\le\lfloor d(t)/d\rfloor\). The clock variation term in the extension is absent until the first admissible order, and the product bound follows by adding the two degree bounds. At degree \(d\), every nonzero linear coefficient comes from a single root extension whose child has degree \(d-1\). It is independent of both the block clock and the common diagonal. At degree \(2d\), a quadratic coefficient can come only from the product of two root factors, both of degree \(d\): an extension of any smaller child still has degree at most one. This quadratic coefficient is also independent of the block clock and diagonal.

The functional \(\mathbf q\cdot\boldsymbol\Phi_t(A)\) annihilates affine receiver polynomials and equals twice their quadratic coefficient through degree \(2d\). It is zero for all \(d(t)<2d\). It is two on the rooted sum of two copies of the extension of the indicated bushy tree. This is an actual same-clock invariant line whose first nonlinear failure can be arbitrarily late. Its three coordinates are distinguishable by tree vectors: the indicated extension gives three distinct affine values. A single such block with weights \(\delta\mathbf q\), \(\delta\ne0\), preserves all old orders through \(2d\), but is not an all-tree stage relation. If \(a\coloneqq1-c\) is nonzero and \(\eta=a/3\), the block also contributes zero to the primitive third reverse residual \(A^\mathsf T(\mathbf b\odot\mathbf y^{\odot2})-\mathbf b\odot\mathbf y^{\odot3}/3\). In contrast, it contributes a nonzero multiple of \(\mathbf q\) to the first reverse residual. Low primitive or clock tests alone cannot force equality of the three receiver stages.

## Two blocks: the genuine first mark can fail at the last paid order

Append two independent blocks of this form, neither reading the other. They use the same probe vector \(\mathbf v\), distinct clocks \(c_1,c_2\), and common diagonal \(\eta_\ell\) within block \(\ell\). Put \(a_\ell\coloneqq1-c_\ell\) and choose \(a_1,a_2\ne0\), \(\eta_1\ne0\), \(\eta_1\ne a_1\), and \(\eta_2=a_2\). Give the two blocks additional output weights \(\delta\mathbf q_1\) and \(-\delta\mathbf q_2\), respectively. Their output contributions cancel on every tree through degree \(2d\), since the first nonzero quadratic coefficients were proved independent of the block. Thus the combined method satisfies all order conditions through \(p=2d+1\). The actual first reverse residual is
\[
 A^\mathsf T\mathbf b-\mathbf b\odot\mathbf y
 =\delta(\eta_1-a_1)\mathbf q_1-\delta(\eta_2-a_2)\mathbf q_2
 =\delta(\eta_1-a_1)\mathbf q_1.
\]
The old base residual is zero and application of \(A^\mathsf T\) to its embedded old output cannot create a later coordinate. Therefore \(\mathbf q_1\) is a genuine first mark; it is supported on one clock, has an actual common eigenline, and annihilates all trees through order \(p-1\). Its rightmost pivot has nonzero output weight \(\delta\).

Apply chronological deletion with the output substitution induced by this relation. No surviving row reads the deleted receiver, so all surviving tree vectors remain unchanged even beyond the truncation. The output changes by \(-\delta\,\mathbf q_1\cdot\boldsymbol\Phi_t(A)\), which is \(-2\delta\ne0\) on the grade \(2d\) witness. Thus this output substitution loses order \(p\). Co-clock support, true operator invariance and genuine finite-order payment do not imply the final output condition. This does not rule out finding different output weights: for example, setting all the receiver weights to zero leaves the old order intact. The example does not assert minimality or occurrence in any near-equality chart.
