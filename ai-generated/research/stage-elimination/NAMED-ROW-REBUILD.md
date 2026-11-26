# Replacing actual reads across a chronological cut

Work over a field \(K\). Let \(A\) be lower triangular with output vector \(\mathbf b\), and let \(p\) be the required order. Write
\[
 d(t)\coloneqq |t|-1,\qquad H\coloneqq p-1,\qquad
 E_h\coloneqq\operatorname{span}_K\{\boldsymbol\Phi_t(A):d(t)\le h\},\qquad
 \varepsilon_i(\mathbf x)\coloneqq x_i.
\]
Set \(E_{-1}\coloneqq0\). The tree extension and rooted sum give \(AE_h\subset E_{h+1}\) and \(E_h\odot E_k\subset E_{h+k}\). Original coordinate labels are used even after stages are omitted. The tests involve numerical tree evaluations; no assumption about a well-defined polynomial model of a numerical vector is needed.

## A necessary and sufficient row test with prescribed horizons

Choose a set \(S\) of retained stages. For \(i\in S\), prescribe a horizon \(h_i\) between \(-1\) and \(H\): the new stage is to have its original tree values through degree \(h_i\). Require its diagonal coefficient to stay unchanged. Allow it to read only certain earlier retained stages \(J_i\subseteq S\cap\{1,\ldots,i-1\}\), all satisfying \(h_j\ge h_i-1\) when \(h_i\ge1\). For \(h_i\ge1\), define the original strict read as the functional
\[
 \lambda_i(\mathbf x)\coloneqq\sum_{j<i}A_{ij}x_j\qquad (\mathbf x\in E_{h_i-1}).
\]
There exists a new lower-triangular tableau with the prescribed diagonal and retained signatures, with these strict read restrictions, if and only if
\[
 \lambda_i\in\operatorname{span}\{\varepsilon_j|_{E_{h_i-1}}:j\in J_i\}
 \qquad\text{for every } i\in S \text{ with }h_i\ge1. \tag{1}
\]
There is no row constraint for a horizon of \(0\) or \(-1\). The same test allows fixed read coefficients: subtract their contribution from \(\lambda_i\) first, provided those fixed donors are within the horizon.

Indeed, coefficients representing \(\lambda_i\) make every extension agree, since a child in the required range is evaluated correctly at all the permitted donors. The unchanged diagonal term is correct by induction on the tree degree. The trivial tree has weight one at every stage; rooted sum preserves agreement by coordinatewise multiplication. This proves sufficiency. Conversely, apply the extension recurrence to the retained and original versions of each child of degree at most \(h_i-1\). All permitted donors agree there and the identical diagonal terms cancel. The new strict read must represent \(\lambda_i\). This gives (1) on the entire linear span.

Now permit new output weights supported only on the retained stages with horizon \(H\). With the row signatures fixed as above, the output agrees through order \(p\) if and only if
\[
 \bigl(\mathbf x\mapsto\mathbf b\cdot\mathbf x\bigr)\big|_{E_H}
   \in\operatorname{span}\{\varepsilon_j|_{E_H}:j\in S,\ h_j=H\}. \tag{2}
\]
This follows simply by evaluating both output functionals on the spanning trees. If \(E_H=K^s\), (2) says that every originally weighted stage must be retained at horizon \(H\), and the permitted output weights are then unchanged. It does not claim that a different construction, with some altered weighted-stage histories, is impossible.

Unlike single-stage linear restoration, (1) can use donors later than a deleted stage, provided they are still earlier than the **consumer**. It can also use cancellation among several omitted reads. It tests exactly the forced combined read, not each deleted stage signature separately. The unchanged surviving diagonal entries preserve ERK, DIRK, strict DIRK, and SDIRK classes.

## Backward distances give a concrete choice of horizons

Place an edge \(j\to i\) if \(j<i\) and \(A_{ij}\ne0\). Let \(D_i\) be the length of a shortest path from \(i\) to a nonzero \(b\) coordinate. Set \(D_i=\infty\) if none exists, and count length zero for an originally weighted stage. Set \(h_i\coloneqq\max(-1,H-D_i)\), with the convention \(H-\infty=-\infty\). Any original edge into a row with \(h_i\ge1\) has donor horizon at least \(h_i-1\), because \(D_j\le D_i+1\). The same statements hold with any nonnegative distance potential having this inequality on each actual edge and value zero at weighted stages.

Suppose the original tableau is stage-minimal at order \(p\) in a fixed diagonal class. Take any nonempty inactive set \(D\), meaning \(b_j=0\) at all its indices, and retain its complement \(S\). Set \(J_i\coloneqq\{j\in S:j<i,\ h_j\ge h_i-1\}\) for rows with \(h_i\ge1\). Then some surviving row \(i\) has an actual witness
\[
 \mathbf x\in E_{h_i-1},\quad \mathbf x|_{J_i}=0,\quad
 \sum_{j\in D,\ j<i}A_{ij}x_j\ne0. \tag{3}
\]
Otherwise every deleted part of an original read lies in the corresponding donor span. All original retained reads were admissible and the old outputs are still retained at horizon \(H\), so (1) and (2) remove all of \(D\), a contradiction. The witness is a linear combination of actual tree columns; it is not merely a path or an abstract full-rank statement. For a singleton inactive stage \(j\), a witness must occur at an actual consumer with \(A_{ij}\ne0\). Its evaluation at the requested degree is independent of all the admissible surviving predecessors of that consumer. Those include later-than-\(j\) stages when available. Formula (3) applies equally to a named fibre, a specified subset of rows, or an inactive initial prefix.

## Simultaneous chronological restoration with nested horizons

There is a separate convenient sufficient rule requiring individual rather than combined read preservation. Restore each omitted row \(i\) through \(h_i\) by a combination of earlier retained rows of horizon at least \(h_i\); when \(h_i=-1\), restore it as zero. For any required original read of a removed row, replacing it by its restoration uses only earlier retained rows at the needed child horizon. Output weights attached to removed rows have horizon \(H\), so their restorations also preserve the outputs. Thus the usual matrices \(A_*=RAL\), \(\mathbf b_*=L^\mathsf T\mathbf b\), with deletion \(R\) and this restoration \(L\), preserve order \(p\). This is safe for simultaneous deletion: the horizon restriction prevents a restoration from creating an uncompensated shortcut in the dependency graph.

For this individual rule and fixed horizons, the earliest-row greedy selection is optimal: retain \(i\) precisely when its evaluation through horizon \(h_i\) is not spanned by earlier retained evaluations with horizon at least \(h_i\). To verify this, any earlier omitted admissible donor was itself reconstructed through at least \(h_i\) from still earlier admissible donors. Consequently the span of admissible retained donors equals the span of all earlier admissible original donors. The forced-retention decision is intrinsic to the original list and any admissible selection must retain those forced rows. This is not a claim of optimality for the more flexible combined-read rule (1).

## A strict example over the rational numbers

Consider the four-stage ERK tableau with only the following possibly nonzero coefficients and weights:
\[
 A_{21}=\tfrac14,\qquad A_{31}=\tfrac12,\qquad A_{41}=-3,\qquad A_{42}=4,\qquad
 \mathbf b=\bigl(\tfrac16,0,\tfrac23,\tfrac16\bigr).
\]
Its clocks are \((0,\tfrac14,\tfrac12,1)\), and \(A\mathbf c=(0,0,0,1)\), where \(\mathbf c\coloneqq A\mathbf1\). The four order-three conditions follow from the Simpson output moments and \(\mathbf b\cdot A\mathbf c=1/6\). The first three coordinates make \(\mathbf1,\mathbf c,\mathbf c^{\odot2}\) independent, while \(A\mathbf c\) vanishes there and not at the fourth. Hence the terminal space \(E_2\) is full. Stage 2 is already independent from the earlier stages on \(E_1\), and its graph distance to output equals one, so the elementary forward-degree-plus-distance test is tight and does not delete it.

Nevertheless, at its sole consumer, row 4, the stage-2 read on \(E_1\) is the average of the stage-1 and stage-3 reads. Therefore replace \(A_{41},A_{43}\) by \(-1,2\) and delete stage 2. The row and output tests hold, yielding a three-stage RK method with all retained signatures and outputs preserved through order three. This example has full terminal rank and no chronological restoration of stage 2 through \(E_1\) using only earlier donors; the named consumer test is genuinely stronger.
