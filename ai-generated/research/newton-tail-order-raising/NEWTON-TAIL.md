# A linear-size triangular extension raising Runge–Kutta order by one

Given a triangular tableau of order \(p-1\), we construct an order-\(p\) tableau without modifying any of the old stage equations. The new output is supported on the appended rows. Their mutual coefficients form a triangular integration operator in a reverse Newton basis. Matching the leading coefficient of the exact integration adjoint makes the remaining data available from the old order-\((p-1)\) method.

The construction works for ERK, DIRK, and common-diagonal SDIRK. Over a field with \(p!\) a unit it appends at most \(p\) rows, or \(\lceil p/2\rceil\) over the real algebraic numbers. Over every commutative ring with \(p!\) a unit it appends at most \(2p\) rows. These are extension costs for a specified old tableau and do not assert new unrestricted stage minima.

## 1. Normalization and available readouts

Let \(p\ge3\), let \(R\ne0\) be a commutative ring with identity in which \(p!\) is a unit, and let \(A_0,\mathbf b_0\) denote the old tableau. Put \( \mathbf c_0\coloneqq A_0\mathbf1\). For any tableau \(A\) define the normalized tree column
\[
 \mathbf N_t\coloneqq \left(\prod_{u\text{ child of the root of }t}u!\right)
                  \boldsymbol\Phi_t(A).
\]
It has the recurrences
\[
 \mathbf N_\bullet=\mathbf1,\qquad
 \mathbf N_{[u]}=|u|A\mathbf N_u,\qquad
 \mathbf N_{t\mathbin{\#}v}=\mathbf N_t\odot\mathbf N_v .
\]
Thus the order condition for \(t\) is \(\mathbf b\cdot\mathbf N_t=1/|t|\). Use the algebraic polynomial integrals
\[
 I(X^a)\coloneqq\frac1{a+1},\qquad
 J_\xi(X^a)\coloneqq\frac{\xi^{a+1}}{a+1},\qquad
 J(X^a)\coloneqq\frac{X^{a+1}}{a+1}
\]
only within their paid ranges. For \(j\ge0\) the polynomial
\[
 v_j(X)\coloneqq\frac{1-X^{j+1}}{j+1}
\]
satisfies \(I(X^j Jf)=I(v_j f)\) whenever the needed denominators are paid, as is seen on each monomial.

Let \(m_0\coloneqq\lfloor p/2\rfloor\). The old tableau supplies a linear map
\[
 \mathcal D:R^s\longrightarrow R[X]_{\le m_0-1},\qquad
 \mathcal D(\mathbf N_u^0)=X^{|u|-1}\quad(|u|\le m_0),
\tag{1}
\]
where the superscript \(0\) means the old coordinates. To define it, prescribe its polynomial's moments of degrees \(0,\ldots,m_0-1\) to be the actual linear readouts \((\mathbf b_0\odot\mathbf c_0^{\odot j})\cdot\mathbf z\) on an arbitrary old vector \(\mathbf z\). The corresponding Hilbert matrix is invertible: its Cauchy determinant has only paid integer differences and denominators, the largest denominator index being \(2m_0-1\le p-1\). On \(\mathbf z=\mathbf N_u^0\), the prescribed moments of \(X^{|u|-1}\) follow from old order \(p-1\) by adding \(j\) leaves at the root. This proves (1).

## 2. Reverse Newton integration on the new stages

Choose distinct quadrature clocks \(\xi_1,\ldots,\xi_r\) with pairwise unit differences and \( \lceil p/2\rceil\le r\le p\). Their quadrature weights must integrate every polynomial through degree \(p-1\). A clock may be represented by more than one physical row, the weights there summing to its quadrature weight. Require at least one physical row of unit weight at each clock. Order all rows of clock \(\xi_i\) before all rows of clock \(\xi_{i+1}\). Let \(\mathbf w\) be the vector of these physical weights and \(C\) the diagonal matrix of their clocks, with repetitions included.

For a polynomial \(f\), define the covector \(L_f\) by \(L_f(\mathbf z)\coloneqq (f(C)\mathbf w)\cdot\mathbf z\). Let
\[
 P_j(X)\coloneqq\prod_{i=r-j+1}^r(X-\xi_i),\qquad
 W_j\coloneqq L_{P_j}\quad(0\le j<r).
\]
The empty product is one. We construct a strictly lower triangular block \(S\) on the new rows satisfying
\[
 W_j S=-\frac{W_{j+1}}{j+1}\quad(0\le j<r-1),
 \qquad W_{r-1}S=0 .
\tag{2}
\]
When there is one row of unit weight per clock, \((W_j)_{j=0}^{r-1}\) is a basis of row covectors: \(W_j\) is supported on the first \(r-j\) rows and has a unit at the last of them. Hence (2) defines \(S\). It sends any row covector supported in the first \(k\) rows into the first \(k-1\), so \(S\) is strictly lower triangular.

For multiple rows per clock there is an explicit alternative that does not divide by any nonunit weight. Fix a donor column \(i\) in clock block \(\alpha\). Only later clock blocks \(\beta>\alpha\) may receive in this column. Choose one unit-weight pivot row \(k_\beta\) in each such block. Determine \(z_{\beta i}\) by
\[
 \sum_{\beta>\alpha} P_j(\xi_\beta)z_{\beta i}
       =-\frac{w_iP_{j+1}(\xi_\alpha)}{j+1},
       \qquad 0\le j<r-\alpha .
\tag{3}
\]
The polynomials \(P_j\) are monic of consecutive degrees and the later clock differences are units, so this is an invertible evaluation matrix. Put \(S_{k_\beta i}=z_{\beta i}/w_{k_\beta}\), leaving every other entry in that column zero. For \(r-\alpha\le j<r-1\), both sides of (2) in this column are zero by the factors of \(P_j,P_{j+1}\); the last equation in (2) also vanishes. This verifies (2) in all columns. There are no couplings within a clock block, and every nonzero entry lies below the diagonal.

Choose a common diagonal \(\gamma\) for the new rows and put \(B\coloneqq\gamma I+S\). In ERK take \(\gamma=0\); in SDIRK take the old common diagonal. For \(0\le j<r-1\) the Newton basis and (2) give a polynomial \(g_j\) such that
\[
 L_{X^j} B=L_{g_j},\qquad
 g_j(X)=-\frac{X^{j+1}}{j+1}+\text{a polynomial of degree at most }j .
\tag{4}
\]
In fact \(X^j=P_j+\sum_{k<j}a_kP_k\), and only the \(P_j\) term produces degree \(j+1\) under (2). In particular \(h_j\coloneqq v_j-g_j\) has degree at most \(j\).

## 3. Feeding the unchanged old stages

The full matrix and output will have the form
\[
 A=\begin{pmatrix}A_0&0\\ U&B\end{pmatrix},\qquad
 \mathbf b=\begin{pmatrix}0\\\mathbf w\end{pmatrix}.
\]
For a polynomial \(f\), let \(f(\boldsymbol\xi)\) be its evaluations on the physical new rows and define \(J_{\boldsymbol\xi}(f)\) in the same way. The preliminary feed is
\[
 U_0\mathbf z\coloneqq J_{\boldsymbol\xi}(\mathcal D(\mathbf z))
                       -B\,\mathcal D(\mathbf z)(\boldsymbol\xi).
\tag{5}
\]
The desired additional identities are, for \(0\le j\le p-m_0-2\),
\[
 L_{X^j} U\mathbf z
      = (h_j(C_0)\mathbf b_0)\cdot\mathbf z ,
       \qquad C_0\coloneqq\operatorname{diag}(\mathbf c_0).
\tag{6}
\]
They do not alter the low-tree feed from (5). To check this, take an old tree column \(\mathbf z=\mathbf N_u^0\), with \(m=|u|\le m_0\), and put \(f=X^{m-1}\). By (4), (5) and the new quadrature,
\[
 L_{X^j}U_0\mathbf N_u^0
    =I(X^j J f)-I(g_j f)=I(h_j f).
\]
Both quadrature uses are for degrees at most \(j+m\le p-2\). The right side of (6) is the same by old order \(p-1\), because \(\deg h_j\le j\).

Let \(T\) be any right inverse of the row block \((L_{X^j})_{0\le j\le p-m_0-2}\). It exists using just the unit-weight pivot rows at distinct clocks, by a square Vandermonde inverse. Add to \(U_0\) the composition of \(T\) with the row block of differences between the desired right sides in (6) and \(L_{X^j}U_0\). The result \(U\) satisfies (6), and its added part annihilates every old \(\mathbf N_u^0\) of size at most \(m_0\).

## 4. All rooted trees pay

First, the entries of \(\mathbf N_u\) on the new rows equal \(\xi^{|u|-1}\) through size \(m_0\). Indeed (5) makes
\[
 U\mathbf N_u^0+B(\xi^{|u|-1})_{\xi}
             =J_{\boldsymbol\xi}(X^{|u|-1})
                  \qquad (|u|\le m_0).
\]
Starting with \(\bullet\), the normalized tree recurrences prove the assertion by induction. They also show that each branch whose child has size at most \(m_0\) has the exact clock power \(\xi^{|u|}\) on the new rows. In particular \(A\mathbf1\) really has the chosen new clocks. Every root made only of such branches is paid through size \(p\) by quadrature.

Proceed by increasing largest child size. At most one child \(u\) can have size \(m>m_0\), since \(2(m_0+1)>p-1\). Let \(j\) be the sum of the other child sizes. They have the exact small clock powers, so the normalized output is
\[
 m L_{X^j}\bigl(U\mathbf N_u^0+B\mathbf N_u^{\rm new}\bigr).
\]
By (6) and old order \(p-1\), the first contribution is \(m I(h_j X^{m-1})\): every exponent in \(h_j\) is at most \(j\), and \(m+j\le p-1\). For the second contribution, (4) gives \(m L_{g_j}(\mathbf N_u^{\rm new})\). Each power \(X^k\) in \(g_j\) has \(k\le j+1\). Its readout is the already paid tree \(u\) joined with \(k\) extra root leaves: its size is at most \(m+j+1\le p\), and its own largest root child is smaller than \(m\). Thus the second contribution is \(m I(g_j X^{m-1})\). Their sum is
\[
              m I(v_j X^{m-1})=\frac1{m+j+1},
\]
as required. This inducts on largest root-child size, not on just the total number of vertices; the decorated \(u\) may have the same total size as the tree being paid. All order-\(p\) tests, including tall trees and roots with no leaves, are accounted for.

## 5. Choosing the quadrature and counting rows

Over any paid ring use the \(p\) integer clocks \(0,1,\ldots,p-1\) and the Vandermonde weights \(\beta_i\) for the moments \(1/(j+1)\), \(0\le j<p\). Represent each clock by weights \(1,\beta_i-1\), so each has a unit pivot and the sums retain the quadrature. Equation (3) and the construction give at most \(2p\) rows. This construction does not assume the \(\beta_i\) are units. It is universal over \(\mathbb Z[1/p!]\) when the old entries are there.

Over a field, discard zero weights and keep one row for each remaining clock. There are at least \(\lceil p/2\rceil\) distinct nonzero-weight nodes: the paid square Hilbert matrix \((I(X^{a+b}))_{0\le a,b<\lceil p/2\rceil}\) is nonsingular and factors through the weighted node evaluations. Thus the field construction uses at most \(p\) rows. Over the real algebraic numbers take \(r=\lceil p/2\rceil\) Gauss nodes. To recall the existence argument, the monic degree-\(r\) polynomial orthogonal to lower degrees is obtained by rational Hilbert inversion. If its sign-changing roots in \((0,1)\) were fewer than \(r\), multiplying by their product would contradict orthogonality, so all its roots are simple interior real algebraic numbers. Integrating the Lagrange polynomials gives weights integrating through degree \(2r-1\) by polynomial division and orthogonality. They are nonzero, for integrating the square of a Lagrange polynomial gives its weight. The exact added count is then \(r\).

The old output can be left fixed if one is willing to pay separately for its cancellation. A new row with the off-diagonal coefficients of an old stage and its same diagonal has exactly the old stage's tree entries, by the normalized recurrence. Add such copies with opposite weights for the old output-active rows. These can be placed in the first new layer and are not used by the proof of (1)–(6). They cancel the original output in every tree even after adding the Newton tail, so the final readout is still the one proved above. This costs up to the number of old output-active rows; the linear-in-\(p\) count without this extra term uses freely reassigned output weights.
