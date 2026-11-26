# Weighted first-consumption tests for unread stage histories

Let \(A\) be a lower-triangular RK tableau over a field \(K\), with output vector \(\mathbf b\). Set \(H\coloneqq p-1\) and \(d(t)\coloneqq |t|-1\). For each \(k\), define
\[
 E_k\coloneqq\operatorname{span}_K\{\boldsymbol\Phi_t(A):d(t)\le k\}
\]
with \(E_{-1}=0\). The ordinary output-context space \(\mathcal C_k\) is the span of the vectors obtained from \(\mathbf b\) by applying \(A^\mathsf T\) at cost one and diagonal multiplication by \(\boldsymbol\Phi_t(A)\) at cost \(d(t)\), with total cost at most \(k\). No zero-model or pure-vector condition is imposed on these spaces.

Fix a literal prefix \(I=\{1,\ldots,m\}\). Let \(D\subseteq I\) be a nonempty collection of unread unweighted stages: \(b_i=0\) and \(A_{ki}=0\) for \(i<k\le m\) whenever \(i\in D\). Let \(P_D\) insert a vector on the omitted coordinates, and choose a matrix \(Q\) supported in the prefix with \(QP_D=I\) and \(QE_h=0\), \(h\ge-1\). This is a prescribed linear restoration of each omitted coordinate from the other prefix coordinates through degree \(h\). The donors can be later than the omitted row, since no surviving prefix row reads an omitted stage. Set
\[
 U\coloneqq(A-\operatorname{diag}A)P_D,
 \qquad c\coloneqq h+2,\qquad
 \rho_t\coloneqq Q\boldsymbol\Phi_t(A).
\]
The temporary full matrix \(A_\epsilon\coloneqq A-\epsilon UQ\) changes only suffix rows' reads into the prefix. At \(\epsilon=1\) all omitted columns are zero in retained rows, so the output of \((A_1,\mathbf b)\) is the output of the actual reduced tableau. No diagonal changes or nonchronological feeds occur. Its prefix histories remain identical for every \(\epsilon\), including those of rows temporarily left in the notation. This gives the exact recurrence
\[
 \boldsymbol\Phi_{[t]}(A_\epsilon)
   = A\boldsymbol\Phi_t(A_\epsilon)-\epsilon U\rho_t.
\]
In particular there is no feed of a changed child back into \(Q\).

## A deficit charges an entire branch, and errors form an antichain

Expansion of the recurrence and of the rooted-sum products expresses the output polynomial in \(\epsilon\) through the ordinary tree, with some branches \([t]\) replaced by \(-U\rho_t\). A replaced branch contains no further replacement, so the selected branches are disjoint below any common ancestor. Each such occurrence consumes at least \(c\) degrees: its child must have \(d(t)\ge h+1\), and extension consumes one more. All remaining operators are actual original \(A\) and actual original tree multipliers.

Let \(d_i\) be the shortest length of a strict dependency path from \(i\) to \(\operatorname{supp}(\mathbf b)\), and let \(d\coloneqq\min_{i\in D}d_i\), with infinity for no path. If \(d=\infty\), all such replacements are harmless. Otherwise \(d\ge1\). A term with \(q\ge1\) replacements cannot affect a nonzero output at degree less than
\[
                         q c+d-1. \tag{1}
\]
Indeed a nonzero numerical summand gives a literal stage path from any one replaced column to an actual weighted row. Above that occurrence at least \(d-1\) strict extension edges are required; these lie outside all \(q\) disjoint replacements. Diagonal edges can only add edges to the same route, not reduce the number of strict ones. This proves (1) without identifying shortest graph paths with actual nonzero weighted sums.

If \(\mathcal C_{H-c+1}|_D=0\), all single-replacement terms vanish through degree \(H\). Their pairing is \(\mathbf z\cdot U\rho_t\), up to sign, for a context \(\mathbf z\) of cost at most \(H-c\). Both \(\mathbf z|_D\) and \((A^\mathsf T\mathbf z)|_D\) vanish, so it is zero. If \(H<c\) even the unweighted degree budget already rules out an occurrence. Thus a restoration is safe whenever the linear invisibility holds and \(H<2c+d-1\). This gains the actual downstream delay over the unqualified two-branch cutoff.

## At the first possible quadratic degree, an exact weighted Gram test

Suppose \(H=2c+d-1\) and \(\mathcal C_{c+d}|_D=0\). No term with three replacements is paid. Equality in the degree budget for a two-replacement output means both replaced children have degree \(c-1\). All remaining \(d-1\) edges belong to the strict path above one occurrence. Consequently the other replaced branch attaches at some row of that path with no additional transport. It must attach to the same first receiver, since attaching after even one edge would make a strict path to a weighted row of length less than \(d\) from the other omitted stage. The shared path above the product has exactly \(d-1\) unary extensions. There is no budget for any other positive-size branch.

Put
\[
 \mathbf w\coloneqq(A^\mathsf T)^{d-1}\mathbf b,\qquad
 \mathcal R\coloneqq Q E_{c-1},\qquad
 Y\coloneqq U\mathcal R.
\]
The deletion preserves all order conditions through \(p\) **if and only if**
\[
              \mathbf w\cdot(\mathbf x\odot\mathbf y)=0
                       \qquad(\mathbf x,\mathbf y\in Y). \tag{2}
\]
Sufficiency follows from the classification and disappearance of linear terms. For necessity take any two child trees \(t,v\) of degree \(c-1\) and apply \(d-1\) unary extensions to \([t]\#[v]\). Its two replacements can occur only at the tops of those two branches: each branch has the minimum cost already, and there is no alternative disjoint location along the unary path. Its output discrepancy is exactly \(\mathbf w\cdot(U\rho_t\odot U\rho_v)\); the other terms are zero. Since these child readouts span \(\mathcal R\), a nonzero pairing in (2) is a certificate that this cut loses order. This is an iff for the specified restoration, not for existence of a different smaller method.

The proof works over any field in which the relevant RK conditions are stated, including paid fields. The direct zero tests give sufficient identities over a commutative unital ring with supplied restoration; field rank and minimality deductions are kept separate. Both ERK and DIRK, including fixed common-diagonal subclasses, retain all their constraints on the remaining rows.
