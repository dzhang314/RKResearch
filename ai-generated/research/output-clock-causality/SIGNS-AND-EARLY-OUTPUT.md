# A signed chronology bound for ordinary DIRK output stages

Use the notation and normalization of GROUP-DEFECTS-AND-CAUSALITY.md. This argument works regardless of how many diagonals are zero, and does not assume distinct physical clocks or that a complete clock group is already exact.

Let \(P_+\) and \(P_-\) count actual positive and negative output weights, and restrict numerical vectors to coordinates of nonzero output weight. For \(0\le j\le q\), where
\[
                            q\coloneqq\lfloor(p-1)/2\rfloor,
\]
let \(\mathcal D_j\) denote the span on these active coordinates of the difference vectors
\[
                     \mathbf N_t-\mathbf c^{\odot(|t|-1)}
                                \qquad(|t|\le j+1).
\]
Adjoining a root leaf gives \(C\mathcal D_j\subseteq\mathcal D_{j+1}\). The symmetric form
\[
              \langle\mathbf x,\mathbf y\rangle_b
                     \coloneqq\sum_{i:b_i\ne0}b_i x_i y_i
\]
vanishes identically on pairs from \(\mathcal D_q\). Indeed expand the product of two such differences; the rooted sum, the two trees dressed with root leaves, and the scalar clock power all have the same paid output. Their size is at most \(2q+1\le p\). Also \(\mathcal D_q\) is perpendicular to the constant vector, whose norm is \(1\). On that perpendicular space the positive and negative indices are \(P_+-1\) and \(P_-\). In particular
\[
                     \dim\mathcal D_q\ \le\
                        w\coloneqq\min(P_+-1,P_-).             \tag{3}
\]
No sign claim is made about the other stage coefficients.

Fix an integer \(1\le r\le q\). Let \(e_r\) be the number of distinct active labels for which some active physical row is not individually exact through size \(r+1\). Then
\[
                             \min(e_r,q-r+1)\le w .            \tag{4}
\]
To prove this, take one such physical row from each of those clock labels. A vector in \(\mathcal D_r\) can be chosen to be nonzero at all those selected coordinates, since its failure at one selected coordinate is only a proper hyperplane. Its first \(q-r+1\) clock-power multiples are in \(\mathcal D_q\) and have rank \(\min(e_r,q-r+1)\) on those selected rows by Vandermonde. This proves (4). The same argument with a specified subset of defective labels is valid even if the other labels are unknown.

For any nonzero clock, a physical row individually exact through \(r+1\) must have index at least \(r\), by its leading-block real-pole stiff response. Thus (4) bounds the number of active nonzero labels with **any** occurrence before \(r\). In particular, if \(w<q\) take \(r=q-w\). At most \(w\) such distinct active labels can occur before \(r\). If \(k_*\) denotes the number of contributing nonzero clocks and \(k_*>w\), at least \(k_*-w\) distinct labels must therefore have active rows at or after \(r\), giving
\[
                            s\ge q+k_*-2w-1.                  \tag{5}
\]
The main information in (4) is the distribution of the early active labels, not just (5). It holds despite arbitrary zero-mass labels and repeated physical clocks.

In strict SDIRK, the same cutoff \(r\) works for zero clocks without exception because invertibility of the leading nonzero diagonal forces a pure zero-clock row to have index at least \(r+1\). If also \(r\ge2\) and every considered ratio \(c_i/\gamma\) is rational, the Laguerre test excludes exact local size \(r+1\) at index exactly \(r\). With that hypothesis at most \(w\) distinct active labels can occur at or before \(r\), and (5) strengthens by one (now counting the zero label too). One can impose this extra delay only on the subset of clocks for which the arithmetic test is known, maintaining the separate thresholds rather than imposing it on other labels.

## Nonnegative output

In the special case \(P_-=0\) the defect vectors in \(\mathcal D_q\) are all zero. Every physically supported row is individually exact through size \(q+1\), not just its aggregate. This recovers the positive-square fact, but now the physical causal bound counts *every* positive output row, not only distinct clocks. If \(B_*\) is the number at nonzero clocks, one needs \(s\ge q+B_*-1\) over real DIRK. More generally any proved same-class lower bound at order \(q\) can replace \(q\), using the scaled stiffly accurate submethod at each such row. If all relevant diagonals are nonzero, zero-clock rows can be included in the count via their stronger linear causal condition. For rational strict SDIRK the no-rational-root criterion gives one more stage when \(q\ge2\) and every ratio is rational.

All these tradeoffs apply to ordinary RKOC, with no claim of positivity of the strict entries, no chosen append-only family, and no reliance on a purported active stage merely repeating another clock. They give restrictions on placements and signs even when they do not strengthen an unrestricted bound. No existing numerical stage endpoint has changed.
