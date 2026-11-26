# Delete an actual plus row using its paid chronological read

This source test applies to ERK and to strict SDIRK with any prescribed nonzero diagonal. It uses the ordinary rooted conventions of the summed-spine construction. It can reduce literal stage count even when a decoder that insists on separate reverse-word equality cannot be compressed. It is a sufficient certificate for the scalar problem, not a necessary classification of every possible new tableau.

## 1. Exact deflation using only earlier numerical signals

Keep the actual closed early data \(\mathbf e(t)\), the plus-minus contrasts \(\delta_i(t)\), their chronological order, and the strict contrast taps \(T_{ij}\) from \(j\) to later \(i\). Assume the architecture has the exact single-large-child recurrence through the paid order \(p\), with each source linear in \(\mathbf e\). Fix a plus row \(j\). An allowed early covector \(h\) and chronological coefficients \(u_i\), \(i<j\), give the proposed relation
\[
                  \delta_j(t)=h\mathbf e(t)+\sum_{i<j}u_i\delta_i(t).       \tag{1}
\]
If (1) holds on all trees through size \(p\), delete the physical plus stage \(j\), but retain its older minus. In each later plus row substitute (1) for its feed from \(\delta_j\). Thus the row acquires the old numerical read \(T_{ij}h\), and each earlier contrast coefficient receives \(T_{ij}u_\ell\). All newly referenced posts are earlier; the old source remains a literal numerical read. Since every contrast vanishes on the leaf and the old leaf column is \(\mathbf1\), equation (1) gives \(h\mathbf1=0\). The rewritten strict rows have unchanged clocks and unchanged diagonal. The final output term \(w_j\delta_j\) is replaced by \(w_jh\mathbf e+\sum_{i<j}w_ju_i\delta_i\), which reweights only existing rows. This preserves the exact scalar and all surviving rooted contrast columns through size \(p\), by recursion. It also preserves any specified next-order witness if the required substitutions and direct output relation are checked on that witness and its descendants. Exact order beyond a checked degree is not inferred from the old depth or from equality of clocks.

There is a smaller safe cutoff for a single deletion. Let \(d_j\) be the least number of nonzero strict feedback edges from the row to any nonzero contrast output weight, with length zero permitted. If none exists, the row is unused by this tail and can be dropped without a substitution. Otherwise it suffices to know (1) through size \(p-d_j\). Any discrepant substituted input at a larger size needs at least \(d_j\) additional rooted extensions to reach the scalar, and each extension costs at least one vertex. The contrast recurrence is exactly linear on this active branch, so no other path can send the discrepancy to a paid output. All earlier rows in (1) are unchanged because the rewrite is strictly downstream of row \(j\). If the cutoff is below the first possible active size, the deleted row can be ignored on that range. When performing several deletions with these smaller cutoffs, recompute the reachability after each change; arbitrary new direct taps can shorten old paths. The full degree-\(p\) version does not need that proviso.

The existence of a relation (1) on a fixed cap is an exact row-space test on the real tree data. The kernel of the matrix comprising the allowed earlier reads and the earlier contrast rows must be contained in the kernel of the deleted contrast row. This condition is both necessary and sufficient for direct substitution of this signal. In particular it does not presume a separate coefficient recovery for the virtual layers. If one forbids reweighting any early output, require additionally \(w_jh=0\) as an allowed old read; if the original source width is to be preserved, restrict \(h\) to the previously measured early covectors. Those are explicit extra constraints, not consequences of the paid relation. A new old output covector with the unrestricted version still preserves the paid scalar identities, because it exactly substitutes the removed value.

With all early covectors permitted and full cap \(p\), pass once through the original chronological plus list and keep only a signal independent modulo the early reads and already kept signals. The forward substitution is legal at each deletion. The resulting number of plus rows is exactly
\[
        \dim\boldsymbol\delta\bigl(\ker(\mathbf e|_{\mathcal T_p})\bigr).
                                                                    \tag{2}
\]
This follows from the rank difference of the stacked \((\mathbf e,\boldsymbol\delta)\) map and the \(\mathbf e\) map. It is the smallest possible number **if all old contrast values on that cap must remain recoverable** by linear reads from the old block and the new states: restricting to early-null combinations gives the matching lower bound. It is not the minimum when only the final scalar is preserved. Since the rewritten stages are still a genuine contrast architecture, the pure-memory commutator bound of the companion note applies also to the number in (2), without needing to divide by a commutator on an artificial capped quotient.

## 2. A necessary clock condition for cross-clock covectors

Let \(C_E\) be the diagonal of old actual clocks and \(\xi_i\) the actual clock of the plus and minus at coordinate \(i\). Suppose (1) holds through cap \(n\). For every combination through size \(n-1\), apply a leaf at the root and add \(\gamma\) times the original combination. Subtract \(\xi_j\) times (1). This yields the exact annihilator
\[
 h(C_E-\xi_j I)\mathbf e(t)
           +\sum_{i<j}u_i(\xi_i-\xi_j)\delta_i(t)=0 .                  \tag{3}
\]
Thus if those earlier measurements span their full coordinate space on this smaller cap, all supported coefficients must have clock \(\xi_j\). A cross-clock deletion is possible only when its marked covector is in the **actual** paid annihilator. This explains why pure endpoint equality of clock labels is neither required nor enough, and why an ambient Vandermonde count can overcharge when the numerical span has a genuine grade deficit.

There is also a finite decorated-root verification that avoids assuming more numerical equality than needed. Let \(Y(t)\) be the stacked old data and earlier contrasts. For a list of short siblings \(\mathcal S\), put \(P_{\mathcal S}=\prod_{v\in\mathcal S}J_\gamma G_v\) and let \(D_{\mathcal S}\) be the actual diagonal of the product of the old sibling primitives. On the large child \(u\), the exact continuation of \(Y\) is the block row action
\[
     \mathcal A_{\mathcal S}=
           \begin{pmatrix}
               D_{\mathcal S} B_E & 0\\
               P_{\mathcal S}(C_{<j}) S_{<j} & P_{\mathcal S}(C_{<j})T_{<j}
           \end{pmatrix},
\]
where \(S\) here denotes the already composed source read on old numerical coordinates. The corresponding next read for row \(j\) is
\[
                     g_{j,\mathcal S}\coloneqq
                              P_{\mathcal S}(\xi_j)(S_j,T_{j,<j}).
\]
For the proposed row \(\lambda=(h,(u_i)_{i<j})\), condition (1) through cap \(n\) is equivalent to \(\lambda Y=0\) on the actual core trees with no large child, and
\[
              (\lambda\mathcal A_{\mathcal S}-g_{j,\mathcal S})Y(u)=0
\]
for all large children \(u\) with \(|u|+1+\sum_{v\in\mathcal S}|v|\le n\). The same chronological row must work for every cap. Necessity and sufficiency follow by the unique active-child decomposition. The old sibling diagonal is the numerical product, not a model substituted solely from its clocks. This makes the criterion applicable to a genuine ERK early/late covector as well as common-diagonal stages, without assuming the ERK or SDIRK donor can be replaced by its formal polynomials on all coordinate rows.

## 3. A reusable cross-clock sufficient case, with a sharp rank

Suppose several actual plus rows use one **identical contrasted input read** \(H(u)\) in their strict primitive: the same linear read of the old numerical data and of contrasts earlier than all these rows. Their old minus baselines can differ; their small sibling factors are certified exact, as in the paired architecture. Then for any nonzero contrast, on the unique active child they have the form
\[
                         \delta_i(t)=P_t(\xi_i)H(u).
\]
Let \(e\) be the first size with \(H(u)\ne0\) on an actual tree. Through cap \(n\), these rows have the rank of evaluation on polynomials of degree at most \(n-e-1\), at their distinct clocks. The upper bound follows by the formula. The lower bound follows by taking such a child of size \(e\) and attaching \(j\) extra leaves, which gives the actual nonzero scalar \(H(u)\) times each \((X-\gamma)^j\) for \(0\le j\le n-e-1\). Thus once \(n-e\) distinct sites of this common-input group already occur earlier than row \(j\), its contrast at any new clock is an explicit cardinal combination of those earlier contrasts on the whole cap. It can be deleted by §1, with \(h=0\). If the cap is below activation the row is silent. If all clocks in the group are distinct and one uses only the earlier rows in this identical-input group, fewer than \(n-e\) sites cannot in general replace a new site: the paid powers give the exact evaluation rank. Different early covectors can of course change that answer, as measured by (1).

This case exhibits stage sharing across physical clocks, with a direct exact test and no assumed freedom to reorder active rows. One can set \(n=p-d_j\) when the row is only a downstream signal. It does not claim that the existing reflected Laguerre receiver arrays have such identical input cohorts, nor does it remove the genuine pure-memory obstruction from an early block of insufficient depth. It identifies a concrete chronological way for a summed solution to have fewer states than a separately matched decoder.
