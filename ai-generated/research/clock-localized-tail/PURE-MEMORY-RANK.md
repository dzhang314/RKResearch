# Which reverse tests are still forced by summed rooted order?

This note concerns the exact summed-spine architecture of the paired tail, not a new lower bound for unrestricted Runge–Kutta methods. The point is to identify real tree combinations on which the early source disappears, so that separately measured reverse words become a **necessary** consequence of ordinary order on that part of the data. It does not assume any of the separated reverse tests on the individual injected sources.

## 1. Isolate the true late memory by cancelling all early data

Work over a characteristic-zero field. Let the common diagonal be \(\gamma\), possibly zero. Write \(B_E\) for the shifted strict matrix of the whole earlier block, which is closed under its own stage computation. Let \(T\) be the strictly lower triangular feedback on the contrasts of the plus rows against their older same-clock minus rows, \(C_+\) the diagonal of the actual plus clocks, and \(\mathbf w\) their output weights. The source into the plus rows must be an actual linear read of the closed early data, as in the paired architecture. The final shifted scalar is a fixed old row on early data plus \(\mathbf w\cdot\boldsymbol\delta(t)\), where \(\boldsymbol\delta(t)\) is the actual plus-minus contrast vector. The old row can be reweighted, provided the final method still has the claimed order.

Let \(\mathcal T_n\) be the formal vector space on trees through size \(n\). For \(u\in\mathcal T_n\), write
\[
 \mathbf e(u)\coloneqq\boldsymbol\Phi_u(B_E),\qquad
 G(u)\coloneqq\text{the shifted exact polynomial of }u,\qquad
 K_n\coloneqq G(\ker(\mathbf e|_{\mathcal T_n})).
\]
All reads here extend linearly from actual trees. In particular this is the image of the kernel of the **entire actual early block**, not a claimed independence of separate tree assignments or a kernel of only one chosen decoder.

For an early-null combination \(u\), unary extension and clock marking preserve its early zero. The shifted unary extension acts by \(T\) on \(\boldsymbol\delta\); the additional source vanishes precisely because \(\mathbf e(u)=0\). Adding a leaf at the existing root and adding \(\gamma\) times the old tree acts by the literal clock diagonals on the actual early and contrast data, and by multiplication by \(X\) on the exact polynomial. The two operations cost at most one grade and model \(J_\gamma=I_0-\gamma\) and \(X\), with \(I_0\) the lower primitive. These identities are exact even for formal linear combinations. The clock identity uses the plus and minus clocks actually agreeing, not just an assigned label.

Thus for every such \(u\), any word in these two letters of length at most \(p-n\) tests pure contrast memory. If the original tableau has order \(p\), the continued combination has zero early output, so its whole scalar comes from the contrasts. Its target is the formal polynomial integral. After reversing the word, the reverse numerical row is obtained from \(\mathbf w\) using \(T^{\mathsf T}\) and \(C_+\); the formal test is obtained from 1 using \(J_\gamma^*\) and \(X\). The exact read on \(\boldsymbol\delta(u)\) is
\[
                                 \ell(PG(u)),\qquad \ell(F)\coloneqq\int_0^1 F .
                                                                    \tag{1}
\]
This argument passes through actual rooted order and the formal integral adjoint. It does not require a collocation-owner adjoint outside its paid precision.

In particular any fully paid rectangle of these moments factors through the actual pure memory \(\boldsymbol\delta(\ker\mathbf e)\). Every matrix rank of this kind is a lower bound on the number of plus rows over both classes, including ERK. Choosing marks alone gives the exact map
\[
 \Gamma_k:\mathcal P_{<k}\longrightarrow K_{p-k+1}^*,\qquad
            \Gamma_k(P)(G)\coloneqq\ell(PG).                     \tag{2}
\]
This is linear on the images: evaluation of any relation among the actual contrast columns at this cap also kills all its paid moments. The effective source space can be much smaller than the independent source spans posited in the separated decoder. That is the relevant distinction for cross-grade cancellation.

## 2. The summed strict-SDIRK commutator bound

Assume \(\gamma\ne0\). If there are \(a\) physical plus rows, for every \(1\le s\le p\) one has
\[
                   a\ \ge\ \sum_{j\ge0:\ k_j>0}\operatorname{rank}\Gamma_{k_j},
                              \qquad k_j\coloneqq s-2j.          \tag{3}
\]
Indeed the numerical reverse operator
\[
     \Pi\coloneqq C_+T^{\mathsf T}-T^{\mathsf T}C_+
                                +(T^{\mathsf T}+\gamma I)^2
\]
is triangular with diagonal \(\gamma^2\), so it is invertible. Its formal action vanishes since \([X,I_1]=-I_1^2\) for the upper primitive \(I_1\); the identity component of \(J_\gamma^*\) commutes with the mark. Each application costs at most two letters. For each \(j\), select polynomials of degree less than \(k_j\) with independent images in (2). Apply \(\Pi^j P(C_+)\) to \(\mathbf w\) for each selected polynomial. Any relation among those vectors may be divided by its least positive or zero power of \(\Pi\). Test the resulting vectors on the actual early-null combinations through size \(p-k_j+1\) for that least \(j\). Every resulting word has length at most \(k_j-1\) and is paid by (1); the terms with remaining positive powers have zero formal polynomial, whereas the least-power terms have independent moments. This contradiction proves (3). It uses no separated source hypothesis.

At \(\gamma=0\), (1) and every ordinary matrix rank still apply, but inversion of \(\Pi\) is unavailable. In either class one can also use pure strict paths: if a tested seeded unary response at length \(\ell\) is nonzero, then \(T^\ell\) is nonzero and the contrast needs at least \(\ell+1\) actual rows.

## 3. A forced source set for the standard packed prefix

Suppose the old strict matrix has \(B_E^m\mathbf1=0\), for example because its early depth is at most \(m-1\) edges. This is true for the cached grade-\((m-1)\) donor plus one base owner layer. No individual late row is being mistaken for an old row. The shifted tall tree of size \(m+1\) is then truly early-null. Put
\[
                       W_j\coloneqq j!J_\gamma^j1.
\]
Its exact polynomial is \(W_m/m!\). The early-null subspace stays zero under the two letters, so through size \(m+1+b\) it contains the generated model band
\[
 \begin{cases}
 \operatorname{span}(W_{m-b},\ldots,W_{m+b}) & \text{if }\gamma\ne0,\\
 \operatorname{span}(X^m,\ldots,X^{m+b}) & \text{if }\gamma=0,
 \end{cases}                                                    \tag{4}
\]
for \(0\le b\le m\). In the nonzero case, \(J_\gamma W_j=W_{j+1}/(j+1)\) and the three-term relation
\[
           XW_j=W_{j+1}+\gamma(2j+1)W_j+\gamma^2j^2W_{j-1}
\]
exhibit each new upper and lower mode successively. Their construction uses only actual graded operations preserving the early kernel. In ERK both letters raise the power and the stated band follows directly.

Let \(p=m+r\), \(1\le r\le m\). On the \(b\)-th band, the rank of integration against \(\mathcal P_{<k}\) is \(\min(k,2b+1)\) for every \(\gamma<0\) over the reals and for generic nonzero \(\gamma\). For the negative case, Laguerre orthogonality is on the negative ray. Any combination of the lowest \(h\) consecutive band members is orthogonal there to all degrees below \(m-b\), so has at least \(m-b\) sign-changing roots on that ray. Its degree is at most \(m-b+h-1\); it therefore has at most \(h-1\) sign changes in \((0,1)\). Multiplication by the product of those interior sign-changing factors gives a polynomial test of degree at most \(h-1\) with nonzero integral. Taking \(h=\min(k,2b+1)\) proves the rank. For general signs, scale a fixed normalized consecutive band. A basis with distinct lowest powers of \(X\), after rescaling as \(1/\gamma\to0\), gives a Cauchy matrix \(1/(1+i+e_j)\) of full rank with the first corresponding monomials. Its determinant was therefore a nonzero polynomial after scaling, so has only finitely many exceptional nonzero diagonals. This choice of band is independent of the scalar owner grid; it is not a genericity assertion about some hidden adaptive decoder. In ERK the monomial band gives the exact Cauchy rank \(\min(k,b+1)\) at every paid rectangle.

Use \(s=r\) in (3), so the old-kernel cap is \(m+1+2j\) and (4) has \(b=2j\). Under those diagonal hypotheses, even a genuinely summed strict tail must have at least
\[
                            \sum_{j\ge0:r-2j>0}\min(r-2j,4j+1)       \tag{5}
\]
physical plus positions. This is \(r^2/6+O(r)\), weaker than the full reverse-decoder cost \(L(r)\) but stronger than just a raw depth count for many grades. For example the value is 12 at \(r=8\) and 18 at \(r=10\). At any diagonal where the paid shifted tall scalar \(\ell(J_\gamma^{p-1}1)\) is nonzero, the same pure source also forces a genuine \((r-1)\)-edge contrast path, hence at least \(r\) rows; this includes ERK and every negative diagonal. A previously constructed parallel tail using a much stronger long-prefix quotient is not a counterexample: such an early block need not satisfy \(B_E^m\mathbf1=0\).

### A complementary test on the early kernel itself

For \(\gamma\ne0\), the invertible **early** commutator also gives an architecture-independent identity of ranks for this chosen early block size \(s_E\):
\[
               s_E\ \ge\ \sum_{j\ge0:n-2j>0}\bigl(n-2j-\dim K_{n-2j}\bigr).
                                                                    \tag{6}
\]
Indeed through each grade the exact polynomial modulo \(K_i\) is a well-defined linear image of the actual early data, by definition of the kernel image. The polynomial target before quotient is all \(\mathcal P_{<i}\) by the bushes. Apply the same division by least power to the ordinary lower-primitive commutator \([C_E,B_E+\gamma I]-(B_E+\gamma I)^2\), whose diagonal is \(-\gamma^2\), now on the early block and with those actual quotient reads. No assumption of dense pointwise exactness over the whole grade is made. Thus actual additional early-kernel modes may strengthen (3); (5) used only the one source with a verified structural reason to vanish. Gaining below the separated bound is not license to discard these residual tests.
