# Ordinary quadrature also fixes local stage accuracy at sparse weighted clocks

Work over a field in which \(p!\) is a unit and assume ordinary order \(p\). The actual distinct labels with some \(b_i\ne0\) are the **visible** clocks. For each visible \(\theta\), define its actual nonzero-weight rows and its aggregate weight by
\[
 I_\theta\coloneqq\{i:c_i=\theta,\ b_i\ne0\},\qquad
 \bar b_\theta\coloneqq\sum_{i\in I_\theta}b_i .
\]
A visible label with zero aggregate need not disappear from a rooted output. Let \(q_*\) count the visible labels of the entire tableau, and \(q_{\rm agg}\) count only the nonzero aggregates. The distinction is essential in applying the tail inequality.

## The local constraint from a paid clock isolator

If \(q_*\le p\), let \(L_\theta\) be the Lagrange cardinal at \(\theta\) on all \(q_*\) actual visible labels, so its degree is at most \(q_*-1\). For a tree \(t\) define its scalar stage model by
\[
                  P_t(x)\coloneqq |t|\,x^{|t|-1}/t! .
\]
The rooted clock multiplications give exact moments for the actual read \(\mathbf b L_\theta(C)\) on \(\boldsymbol\Phi_t(A)\) whenever \(|t|-1\le p-q_*\). By the ordinary bushy conditions the exact scalar integral of \(L_\theta P_t\) is also its quadrature sum on the same visible labels; its degree is at most \(p-1\). Hence
\[
             \sum_{i\in I_\theta}b_i\bigl(\boldsymbol\Phi_t(A)\bigr)_i
                        =\bar b_\theta P_t(\theta)
            \quad (|t|-1\le p-q_*).                               \tag{1}
\]
This identity applies even when the aggregate is zero and uses no sign assumption. A two-row fibre with opposite nonzero weights therefore has exactly equal numerical rooted profiles on those **two** rows through this degree. It does not license their replacement through higher grades or a change to the actual incoming or outgoing taps.

If \(I_\theta=\{i\}\), (1) says that stage \(i\) has the exact stage derivative coefficients through degree \(p-q_*\). In particular with \(a\coloneqq p-q_*\), for every tree \(u\) of size at most \(a\),
\[
            A_i\cdot\boldsymbol\Phi_u(A)
                 =(\boldsymbol\Phi_{[u]}(A))_i
                 =\theta^{|u|}/u! .                              \tag{2}
\]
If \(\theta\ne0\) and the tableau is lower triangular, the leading tableau through row \(i\), divided by \(\theta\), is an ordinary order-\(a\) tableau with output row \(A_i/\theta\) restricted to that prefix. Indeed its derivative weights are scaled by \(\theta^{-(|u|-1)}\) and (2) is exactly the resulting order condition. The prefix retains both nonsingularity and any common diagonal property. Thus a singleton nonzero weighted clock at \(\theta\ne0\) cannot occur at an index below the known ordinary order-\(a\) floor for its prefix class. In particular \(i\ge Q(a)\) for a nonsingular prefix with \(a\ge1\). A clean row at \(\theta=0\) instead gives the vanishing incoming tests (2); division by its clock is not allowed. The same tail placement constraints now apply to the actual **incoming** weights of this normalized prefix. In particular if \(i=Q(a)\ge2\), its last two weights must be nonzero at distinct clocks. Thus the original incoming coefficient \(a_{i,i-1}\) cannot be zero and \(c_{i-1}\ne c_i\) at a singleton clean provider placed exactly at its nonsingular stage floor.

## Using minimal quadrature support without losing the literal cancellation information

The paid Hilbert moment matrix on polynomials of degree at most \(\lfloor(p-1)/2\rfloor\) is nonsingular. Factoring it through evaluations on the aggregate quadrature nodes gives \(q_{\rm agg}\ge\lceil p/2\rceil\), even when individual coefficients are signed. The nonsingularity follows from the factorial Vandermonde argument or the standard paid rational Cauchy determinant. All denominator indices are at most \(p\).

In even order \(p=2m\), if \(q_{\rm agg}=m\), the monic product of the \(m\) aggregate clock roots is orthogonal to all polynomials of degree less than \(m\) for integration from zero to one. This follows by evaluating its product with a polynomial of degree at most \(m-1\) in the exact ordinary scalar quadrature. These are the Gaussian nodes. Neither endpoint \(0\) nor \(1\) is one of them: a root at zero or one would leave a polynomial of degree \(m-1\) orthogonal to all such polynomials in the weighted Gram with weight \(x\) or \(1-x\), respectively. These matrices are nonsingular over the same paid fields. Thus a *visible* endpoint in this minimal-aggregate regime must belong to a cancelling fibre and consumes at least two literal nonzero weights. In particular there must be at least \(m+2\) nonzero stage weights if a visible endpoint is used. A zero aggregate must not be counted as absent in the physical suffix bound.

Suppose in particular that an order-\(2m\) method has **exactly \(m\) nonzero stage weights**. The preceding scalar rank shows that all these weights are on different active clocks and hence all are nonendpoint Gaussian nodes. If \(i_1<\cdots<i_m\) are the nonzero-weight rows and the method is nonsingular, the suffix strictly after \(i_1\) has \(m-1\) visible clocks. The absolute staircase in TRAILING-WEIGHT-CLOCK-PLACEMENT.md gives \(i_1\ge Q(2m)-T_{m-1}=m\). Each of these stages is a singleton and (2) pays a genuine order-\(m\) nonsingular prefix at it. Consequently
\[
              i_\ell\ge \max\{m,Q(m)\}+\ell-1
                   \quad(1\le \ell\le m).
\]
The rest of the staircase can be combined row by row with this linear spacing. If the prefix class has a stronger known local ordinary lower bound, use it in place of \(Q(m)\). For an arbitrary mixed prefix, use its proper lower bound or keep the measured prefix kernel penalty rather than declaring it nonsingular.

As another scalar scope check, in odd order \(p=2m+1\) with the minimal \(m+1\) active aggregate labels, both endpoints cannot be active together. Otherwise factor the monic root polynomial as \(x(1-x)\) times a polynomial of degree \(m-1\). Ordinary quadrature gives its orthogonality to every degree at most \(m-1\) polynomial, contradicting the paid Gram for weight \(x(1-x)\). A visible zero-aggregate endpoint remains possible and still consumes actual support.

These constraints separate what the RK order conditions force at singleton or cancelling clock fibres from the independent chronological suffix restriction. They do not assume positive weights, a particular construction architecture, or that any unrestricted stage minimum has minimal quadrature support. No stage-count table is changed.
