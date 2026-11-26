# Transfer to ERK and DIRK, and the exact obstruction in between

The old frontier row depends only on the numerical old rooted columns and their known readouts. It is not an SDIRK identity. The chronological head construction also transfers: given earlier pure polynomial information through size \(d\), a later stage at time \(\xi\) with diagonal \(\delta\) has strict feed
\[
                       E_\xi(J-\delta\,\mathrm{Id})\mathcal D_d .
\]
It is then locally exact through \(d+1\), and it may occupy an output row rather than a dedicated preparation row. For a literal merge choose its diagonal equal to that of the old representative and preserve its old strict row. Neither assertion requires a common diagonal. The distinction between classes is the ability to choose the backward pivot diagonals.

## Variable DIRK diagonals remove the fixed clocks

Order the final \(a\) distinct clock sites in reverse chronological notation \(\eta_1,\ldots,\eta_a\). Put
\[
 s_j\coloneqq\sum_{i=1}^j\eta_i,\qquad
 P_j(X)\coloneqq\prod_{i=1}^j(X-\eta_i),
\]
and let \(d_j\) be the diagonal at the pivot \(\eta_{j+1}\). Chronology and the leading integration coefficient force the same dual polynomial form, now
\[
                    G P_j=d_j P_j-\frac{P_{j+1}}{j+1}.
\]
The second-leading coefficient of \(J^*P_j-GP_j\) is zero if
\[
 d_0=1-\eta_1,\qquad
 d_j=\frac{s_j/j-\eta_{j+1}}{j+1}\quad(j\ge1).
\]
In arbitrary DIRK these equations prescribe diagonals, not clock locations. Choose the adjustable clock sites below \(1\) and in strictly decreasing order \(\eta_1>\cdots>\eta_a\). Every displayed diagonal is then positive. Other new unmerged diagonals may be chosen positive freely, while every old or merged diagonal is retained.

The triangular solve permits these unequal diagonals. Writing \(D_{\rm tail}\) for the diagonal matrix of new diagonals and \(S\) for the strict part, impose
\[
 L_{P_j}S= -\frac{L_{P_{j+1}}}{j+1}
               +L_{P_j}(d_j\,\mathrm{Id}-D_{\rm tail}).
\]
For a column with \(n<a\) later rows, the equations with \(j>n\) vanish by their trailing factors. The equation with \(j=n\) also vanishes because its pivot diagonal is exactly \(d_n\). The earlier equations use precisely \(n\) distinct later sites. Thus the same columnwise weighted evaluation solve applies and the early strict coefficients remain arbitrary. All high old terms now have polynomial degree at most \(j-1\) after adjoint residual subtraction, so ordinary old order \(p-2\) alone suffices. The two-order all-rooted proof transfers verbatim.

Consequently ordinary unconstrained DIRK gains the protected-head and donor-sharing mechanism but does not need the frontier to free receiver locations. For example, choose real-algebraic exact quadrature with exterior donor clocks and all free sites interior; these free sites can contain the last \(a\) adjustable pivots if capacity holds. Or use the rational \(p-1\)-site exterior construction with any additionally adjustable clocks chosen below \(0\), and the one solved clock inside \((0,1)\). In these cases the physical budget is the no-fixed-pin case of PHYSICAL-COUNT-TRANSFER.md. The restriction is important only if the DIRK diagonals are prescribed or shared in a way that removes the displayed freedoms.

## ERK fails the generic two-order Newton specialization

For ERK every \(d_j=0\). If the old frontier is unresolved at \(j=0\), the terminal clock is forced to be \(1\). If it is unresolved at \(j=1\) as well, its next distinct pivot is also forced to be \(1\). Thus an ERK suffix with a single polynomial adjoint action and two or more unresolved frontiers is impossible in this architecture. The reason is literal chronology at distinct last weighted clocks; grouping signed repeats or allowing a zero aggregate at a weighted site does not make two distinct clock labels out of the one clock \(1\). Co-site contrast constructions that do not preserve the single-polynomial action are outside this obstruction.

If at most one frontier is unresolved, the protected-head construction does transfer. With one missing frontier the last site is the endpoint \(1\); with none the old stage equations already admit some output of order \(p-1\), even if the old chosen output has only order \(p-2\). A single-polynomial ERK two-order step with at most one pin therefore requires actual old information through at least grade \(m=p-2\), not merely the half-order old decoder.

The built-in explicit origin is always an exact local sample, since its row is zero. It is exterior as a sampling point for the sign test, so it does not substitute for an interior reflection sensor. If one attempts to pay the necessary grade-\((p-2)\) frontier using only ordinary old moments and pure old stage samples, the output-sample theorem requires \(r+i\ge p-3\), with \(r\) the number of distinct samples and \(i\) the interior count. At most one of the samples can be the origin. A nonzero-clock ERK sample pure through \(m\) must occur no earlier than row \(m\), because its tall tree of size \(m\) is nonzero, whereas \(A^{m-1}\mathbf1\) vanishes in all preceding rows. If \(\varepsilon\) denotes whether the origin sample is used, the old stage count in this certification route is therefore at least
\[
                  (p-3)+\left\lceil\frac{p-3-\varepsilon}{2}\right\rceil .
\]
When \(p-3\) is even, the theoretical minimum sample count \((p-3)/2\) itself requires shifted Legendre roots. For rational samples it is unavailable when that minimum is at least two. These are preparation limits for the indicated transfer proof, not global ERK lower bounds.

The practical distinction is therefore specific. SDIRK benefits from partial frontier recovery because it cannot vary the diagonal. DIRK shares the head but can move its diagonals instead. ERK shares the head but must first remove all but one frontier obstruction, or leave the single-polynomial adjoint model entirely.
