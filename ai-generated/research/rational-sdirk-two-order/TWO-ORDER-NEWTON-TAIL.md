# Two orders at once by a reflected odd Newton ladder

Let \(p\ge3\). Start from a lower triangular tableau \(A_0,\mathbf b_0\) of ordinary rooted order at least \(p-2\). We do not change its stage equations. Suppose it supplies a linear polynomial decoder through tree size \(q\), where
\[
  \left\lfloor\frac{p-1}{2}\right\rfloor\le q\le p-2,\qquad
  a\coloneqq p-q-1 .
\]
For an order-\((p-2)\) seed alone one can always take \(q=\lfloor(p-1)/2\rfloor\), by the old paid Hilbert matrix. An additional true dense decoder may be used instead. Let \(\gamma\) denote the desired common diagonal for the appended rows; keep the old diagonal in a strict SDIRK application.

If the new quadrature has precision \(p-1\) and includes the \(a\) distinct clocks
\[
                    \eta_i\coloneqq1-(2i-1)\gamma,
                         \qquad 1\le i\le a,                  \tag{1}
\]
there is a Newton tail raising ordinary order to at least \(p\). Place these clocks last, in reverse index order, so \(\eta_1\) is the final clock. The output is reassigned to that tail. Other clocks and weights may be signed or exterior; the reconstruction needs unit differences and at least one unit physical output weight at each clock. If the quadrature fails the degree-\(p\) monomial moment, the resulting tableau is of *exact* ordinary order \(p\), with the next bushy tree as witness.

In the proof below take at most p distinct nodes, so all Newton denominators are paid. Over a field use one row per quadrature node with nonzero weight, including every required ladder node. Over a nonzero commutative ring with \(p!\) and \(\gamma\) units, extend (1) to the \(p\)-site ladder. It has unit differences \(2(j-i)\gamma\), and the paid Vandermonde gives quadrature weights. Using two output rows \(1,\beta_i-1\) at each site pays a unit pivot without assuming \(\beta_i\) is a unit. This gives a \(2p\)-row two-order extension, instead of two general one-order tails of upper counts \(2(p-1)\) and \(2p\). No polynomial root extraction, nonunit inversion, or change to a common physical unit diagonal is needed. The real-algebraic and rational improvements below use one row per nonzero weight.

## Exact high-degree action

Normalize the stage column of \(t\) by multiplying the elementary weight by \(\prod_{u\text{ child of }t}u!\), and write the resulting column as \(\mathbf N_t\). Its formal polynomial is \(X^{|t|-1}\). Unary extension satisfies \(\mathbf N_{[u]}=|u|A\mathbf N_u\), while rooted sum acts by coordinatewise multiplication. Put
\[
   I f\coloneqq\int_0^1 f(X)\,dX,\quad
   J f(X)\coloneqq\int_0^X f(Z)\,dZ,\quad
   J^*f(X)\coloneqq\int_X^1 f(Z)\,dZ .
\]
All integrations are polynomial primitives in a paid degree range. Let \(\mathcal D\) be the decoder, so \(\mathcal D(\mathbf N_t^0)=X^{|t|-1}\) for \(|t|\le q\). For a decoder obtained from the old method alone, take \(q=\lfloor(p-1)/2\rfloor\), solve the Hilbert moment system of size \(q\) on old observations, and use \(2q-1\le p-2\). The Hilbert determinant is a paid unit, as in the audited one-order method.

Use the reverse Newton covectors from the one-order proof. In chronological order the quadrature nodes are \(\xi_1,\ldots,\xi_k\), and \(P_j\) is the monic polynomial with roots the last \(j\) distinct nodes (\(P_0=1\)). If \(L_f=(w_i f(\xi_i))_i\) is the actual weighted row on the new stages, including any repeated-site weights, choose the strict lower \(S\) so
\[
 L_{P_j}S=-L_{P_{j+1}}/(j+1)\qquad(0\le j<k).
\tag{2}
\]
For the last \(j=k-1\), \(L_{P_k}=0\) because the full hull vanishes at all new clocks; this is exactly the last-zero equation of the one-order construction. That proof gives the literal lower triangular solves using unit pivots at later clock blocks, including repeated-clock blocks; it does not require access to a new independent covector \(L_{P_k}\). This boundary observation permits using all \(a\) rows of moments even if \(a=k\). Put \(B=\gamma I+S\), with diagonal exactly \(\gamma\). On monic basis polynomials set
\[
                     G P_j\coloneqq\gamma P_j-P_{j+1}/(j+1).
\]
Then \(L_f B=L_{Gf}\) on the span of \(P_0,\ldots,P_{k-1}\), using the displayed polynomial representative even at the boundary. The new fact is
\[
      h_j(X)\coloneqq J^*(X^j)-G(X^j),\qquad
      h_0=0,\quad \deg h_j\le j-1 \quad(1\le j<a).             \tag{3}
\]
Indeed the degree \(j+1\) coefficient already matches by (2). On \(P_0\) the difference is \(1-\gamma-\eta_1=0\). At \(j\ge1\), write \(s_j=\eta_1+\cdots+\eta_j\), so the coefficient at \(X^j\) in \(J^*P_j-GP_j\) is
\[
                         s_j/j-\gamma-s_{j+1}/(j+1).
\]
The ladder (1) makes \(s_j/j=1-j\gamma\), giving the claimed second cancellation. Change from the monic Newton basis back to powers; the lower basis polynomials already have the stronger degree caps. All these coefficient computations take place over the paid ring.

## Exact old-to-new feed and ordinary order

Use evaluation \(T_{\rm ev}\) at the new physical clocks and start the feed at
\[
                 U_0=(T_{\rm ev}J-B T_{\rm ev})\mathcal D .
\]
Require for \(0\le j<a\) the actual row identities
\[
                    L_{X^j}U=(\mathbf b_0\odot h_j(\mathbf c_0))^\top ,
                         \qquad \mathbf c_0=A_0\mathbf1 .    \tag{4}
\]
Here transposes only indicate a displayed row when \(\mathbf b_0\) is a column. On every old column with \(|u|\le q\), both sides of (4) already agree for \(U_0\): with \(f=X^{|u|-1}\), the former side is \(I(h_j f)\) by quadrature and the adjoint. The quadrature uses degree at most \(j+|u|\le p-2\). The latter side agrees by old order since its costs are \(|u|+\deg h_j\le p-2\), with \(h_0=0\). Thus the difference row block vanishes on those actual low columns. Multiply this difference by any Vandermonde right inverse of \((L_{X^j})_{0\le j<a}\) to correct \(U_0\), keeping its entire low feed unchanged. One can choose the inverse using only the \(a\) paid pivots on the last ladder clocks. In particular it need not alter a reserved early row.

The completed matrix is \(\begin{pmatrix}A_0&0\\U&B\end{pmatrix}\), and its output is the new quadrature weights. Low feed agreement gives every new stage the exact profile \(X^{|u|-1}\) through size \(q+1\) by induction on rooted size. More precisely, for a child of size at most \(q\) the actual primitive has the exact value \(T_{\rm ev}J(X^{|u|-1})\), so products of paid children are correct; taking the leaf gives the prescribed clocks. At every output tree of size at most \(p\), there can be at most one child \(u\) of size \(m>q\), as \(2(q+1)+1>p\). Let \(j\) be the sum of the other child sizes. The readout when \(u\) occurs is
\[
            m L_{X^j}\bigl(U\mathbf N_u^0+B\mathbf N_u^{\rm new}\bigr).
\]
Here \(0\le j<a\). By (3)–(4) the first term is \(m I(h_jX^{m-1})\): the largest old tree size needed is \(m+j-1\le p-2\). The second term is \(m L_{G(X^j)}\mathbf N_u^{\rm new}\); each polynomial monomial in it has degree \(k'\le j+1\), and its output is an actual tree \(u\) with \(k'\) extra leaves at its root. This decorated tree has size at most \(m+j+1\le p\) and smaller largest root-child size than \(m\). Thus the induction by largest child, starting at all children of size \(\le q\), gives \(m I(G(X^j)X^{m-1})\). The two terms add to \(m I(J^*X^j\,X^{m-1})=1/(m+j+1)\). No equality for unsupported new samples on high trees is used here. This proves full ordinary order and the claimed first unpaid bush witness.

## The prescribed-node quadrature

Let \(F(X)=\prod_{i=1}^a(X-\eta_i)\) and \(n=\lceil(p-a)/2\rceil\). If all the pinned nodes are outside \((0,1)\), \(F\) has constant nonzero sign on \((0,1)\). This holds for every negative real \(\gamma\) or every real \(\gamma\ge1\). For each fixed \(p,q\), the same finite polynomial argument below also works for sufficiently small nonzero \(\gamma\) by continuity from \(F=(X-1)^a\). Choose the monic degree-\(n\) polynomial \(Q_n\) orthogonal through degree \(n-1\) for \(F(X)dX\). Multiplication by an overall sign makes its Gram positive definite in the exterior case. A monic orthogonal polynomial of degree \(n\) has \(n\) simple interior roots by the sign-changing-root argument. They and their required nonzero evaluations persist in the near-endpoint case by the continuity of a nonsingular moment system and sign brackets at the limiting simple roots.

Use the pinned nodes and all \(n\) roots of \(Q_n\). By division against \(FQ_n\), their interpolatory weights integrate through degree \(a+2n-1\ge p-1\). All those weights are nonzero. At a pinned node \(\eta\), the numerator of its cardinal weight is \(I((F/(X-\eta))Q_n)\), nonzero because
\[
 I\!\left(\frac{F}{X-\eta} Q_n^2\right)
     =Q_n(\eta)\,I\!\left(\frac{F}{X-\eta}Q_n\right)
\]
by orthogonality on writing \(Q_n=Q_n(\eta)+(X-\eta)R\) with \(\deg R<n\). The left side has constant sign in the exterior case, or nonzero limit at a coalescing endpoint. At a free node \(x\), use the isolating polynomial \(F(X)\bigl(Q_n(X)/(X-x)\bigr)^2\) of degree \(a+2n-2\); its nonzero integral and nonzero value there show that the weight is nonzero. In the exterior case the free weights are positive after the factor \(F(x)\) is canceled.

When \(a+2n=p\), the degree-\(p\) polynomial \(FQ_n^2\) has nonzero integral and zero readout. When \(a+2n=p+1\), perturb the hull by using \(Q_n+\theta Q_{n-1}\) in place of \(Q_n\), with a sufficiently small nonzero real-algebraic \(\theta\). Orthogonality of this new hull is only needed through degree \(n-2\); this pays precisely \(p-1=a+2n-2\). Real split roots, disjointness and all needed nonzero weights persist. Multiplying the new full hull by \(Q_{n-1}\) gives a zero readout of degree \(p\) and nonzero integral \(\theta I(F Q_{n-1}^2)\). In either case exactness at lower degrees ensures that the first monomial mismatch is at degree \(p\). The total count is \(a+\lceil(p-a)/2\rceil\), and all coefficients are real algebraic for real-algebraic \(\gamma\).

## Bare reverse Newton action cannot match three leading degrees

This limitation applies even with separate diagonal entries, over ordered fields. For a scalar row basis with distinct nodes, a chronological map of the row \(L_{P_j}\) whose polynomial degree is at most \(j+1\) and whose leading integration coefficient is matched must act on it as \(d_j P_j-P_{j+1}/(j+1)\). The first \(j\) trailing locations must remain zero, and at the next pivot its action is its literal diagonal \(d_j\). Take \(2\le j<k-1\) (or allow the displayed \(P_k\) representative at the counted boundary). Let \(s_j,t_j\) denote the sum and sum of pairwise products of the last \(j\) knots. Matching the coefficients of degrees \(j\) and \(j-1\) in the adjoint would require, on eliminating \(d_j\) and the next knot,
\[
                 s_j^2/j=2t_j/(j-1),
          \quad\text{or}\quad
                 j\sum_{i=1}^j\eta_i^2=s_j^2 .
\]
Indeed the two coefficient equations are \(s_j/j-d_j-(s_j+\eta_{j+1})/(j+1)=0\) and
\(-t_j/(j-1)+d_j s_j+(t_j+\eta_{j+1}s_j)/(j+1)=0\). The asserted equality contradicts the positive sum of squared differences of distinct real nodes. For the common nonzero diagonal the obstruction is already at \(j=1\): a two-degree match fixes \(\eta_1=1-\gamma\), and the difference at that node is \(J^*(X-\eta_1)(\eta_1)=\gamma^2/2\), which cannot be zero. This is a restriction of the single Newton polynomial action, not a lower bound for general coupled or repeated-site extensions.
