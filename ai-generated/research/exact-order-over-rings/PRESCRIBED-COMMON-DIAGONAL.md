# Exact Runge–Kutta order with a prescribed common diagonal

**Theorem.** Let \(R\) be a nonzero commutative ring with identity, \(p\geq 1\), and \(\gamma\in R\) prescribed. There is a lower triangular Runge–Kutta tableau over \(R\) with every diagonal entry equal to \(\gamma\) and with exact order \(p\) if and only if \(p!\) is a unit of \(R\). The construction below uses at most \(p(p+3)/2\) stages. In particular, it gives a genuine SDIRK with a prescribed common **unit** diagonal when \(\gamma\in R^\times\). The same algebra works for \(\gamma=0\), when the tableau is explicit. The stage count is an upper bound, not a minimum.

Write \(\lvert t\rvert\) for the vertex count of a rooted tree \(t=[t_1]\#\cdots\#[t_r]\), and put
\[
F(t)\coloneqq\prod_{\nu=1}^r t_\nu!,\qquad t!=\lvert t\rvert F(t).
\]
The leaf has factorial and forest factorial both equal to \(1\). Equivalently, \(t!\) is the product of the subtree sizes over all vertices, and \(F(t)\) excludes the root. The raw stage columns obey
\[
\boldsymbol{\Phi}_{\bullet}(A)=\mathbf 1,\qquad
\boldsymbol{\Phi}_{[t_1]\#\cdots\#[t_r]}(A)
 =\bigodot_{\nu=1}^r A\boldsymbol{\Phi}_{t_\nu}(A),
\]
 Order at least \(p\) means \(t!\,(\mathbf b\cdot\boldsymbol{\Phi}_t(A))=1\) whenever \(\lvert t\rvert\leq p\). The \(p\)-vertex tall tree has factorial \(p!\), so its condition already makes \(p!\) a unit. This proves necessity.

## 1. Interpolation and a common diagonal

Assume \(p!\) is a unit. Every integer from \(1\) to \(p\) is then a unit. For \(1\leq m\leq p\), evaluation at \(0,1,\ldots,m-1\) is an isomorphism from \(R[X]_{<m}\) to \(R^m\): the Vandermonde determinant is a product of unit differences, even when \(R\) has zero divisors. Denote the inverse interpolation map by \(P_m\). On polynomials of degree below \(p\) define the zero-constant formal primitive \(\mathcal I\) by
\[
\mathcal I(X^k)=\frac{X^{k+1}}{k+1}.
\]
All divisions used here are by units.

Take layers \(\ell=0,\ldots,p-1\), with \(\ell+1\) stages in layer \(\ell\), indexed by \(i=0,\ldots,\ell\). For \(\ell\geq 1\) and \(v\in R^\ell\), set
\[
(E_\ell v)_i=P_\ell(v)(i),\qquad
(K_\ell v)_i=(\mathcal I P_\ell(v))(i),\qquad 0\leq i\leq\ell.
\]
Use the common diagonal \(\gamma\) on every stage. The only off-diagonal block into layer \(\ell\) is \(K_\ell-\gamma E_\ell\) from layer \(\ell-1\). Thus the tableau \(A_0\) is lower triangular in layer order, with
\[
(A_0 v)_0=\gamma v_0,\qquad
(A_0 v)_\ell=\gamma v_\ell+(K_\ell-\gamma E_\ell)v_{\ell-1}.
\]
Here \(v_\ell\) denotes the entire vector on layer \(\ell\). Give only the last layer output weights: its weight vector \(\mathbf w\in R^p\) satisfies
\[
\mathbf w\cdot v=(\mathcal I P_p(v))(1).
\]

## 2. Exactness of the paid tree columns

For a tree of size at most \(p\), let \(f_t(X)=X^{\lvert t\rvert-1}/F(t)\). The tree factorial relation gives
\[
\mathcal I f_{t_\nu}=\frac{X^{\lvert t_\nu\rvert}}{t_\nu!},
\qquad
\prod_{\nu=1}^r\mathcal I f_{t_\nu}=f_t .
\]
We claim that whenever \(\lvert t\rvert\leq\ell+1\), the raw column of \(t\) on layer \(\ell\) is the vector of samples \(f_t(i)\), \(0\leq i\leq\ell\).

Induct on tree height, simultaneously for the eligible layers. The leaf is constant \(1\). In a nonleaf tree each child has smaller height, so its samples on the **same** layer are already known: the diagonal term does not create a circular induction. Also \(\lvert t_\nu\rvert\leq\lvert t\rvert-1\leq\ell\), so the preceding layer has exact child samples and enough nodes to interpolate \(f_{t_\nu}\), whose degree is below \(\ell\). The same-layer \(\gamma\) term and the resampled \(-\gamma E_\ell\) term therefore cancel exactly. The action of \(A_0\) on the child, on this layer, gives the samples of \(\mathcal I f_{t_\nu}\). Multiplying the child samples proves the claim.

On the last layer every tree through order \(p\) is covered. With \(\mathbf b_0\) the full output vector supported on that layer,
\[
\mathbf b_0\cdot\boldsymbol{\Phi}_t(A_0)=(\mathcal I f_t)(1)=\frac1{t!}.
\]
This proves order at least \(p\) with \(p(p+1)/2\) stages.

## 3. An exact next-tall correction without new inverses

Let \(A_{\mathrm{path}}=\gamma I+S\) on stages \(0,\ldots,p\), where \(S\) has \(1\) on the adjacent subdiagonal and zero elsewhere. At root position \(i\), an expansion of the raw tree column chooses, on each edge, either a stay (factor \(\gamma\)) or a step back by one (factor \(1\)). A choice contributes exactly when no root-to-vertex path takes more than \(i\) steps. Thus once \(i\) is at least the tree height, the boundary at stage \(0\) has no effect: all edge choices contribute with the same weights regardless of \(i\).

Let \(\tau_{p+1}\) be the \((p+1)\)-vertex tall tree. Both positions \(p-1,p\) are past the boundary for every tree through order \(p\). For \(\tau_{p+1}\), only the choice taking a step on all \(p\) edges is new at position \(p\), and its weight is \(1\). Hence
\[
(\mathbf e_p-\mathbf e_{p-1})\cdot\boldsymbol{\Phi}_t(A_{\mathrm{path}})
=\begin{cases}
0,&\lvert t\rvert\leq p,\\
1,&t=\tau_{p+1}.
\end{cases}
\]
Append this block and give it output vector \(-\rho(\mathbf e_p-\mathbf e_{p-1})\), where \(\rho=\mathbf b_0\cdot\boldsymbol{\Phi}_{\tau_{p+1}}(A_0)\). In the combined tableau, the paid outputs remain unchanged and \(\mathbf b\cdot\boldsymbol{\Phi}_{\tau_{p+1}}(A)=0\). The next denominator-cleared tall condition thus fails by \(-1\), even if \((p+1)!\) is a nonunit. No new inverse was used.

The first stage of each block is a pure \(\gamma\) stage, with no off-diagonal entries in its row. Each has the same tree values \(\gamma^{\lvert t\rvert-1}\). They may be replaced by one first stage: keep its diagonal equal to \(\gamma\), redirect references, and sum the two output weights. Induction on the tree recursion preserves all other stage values and all raw outputs. This gives the stated \(p(p+1)/2+p=p(p+3)/2\) bound.

## Remarks on coefficient rings and width

All coefficients belong to \(R\) using only the inverses supplied by \(p!\). In particular, taking \(\gamma=1\) gives a common unit diagonal over \(\mathbb Z[1/p!]\), and the proof works after any base change to a nonzero ring. In positive characteristic \(N\), an integer \(a\) represents a unit exactly when \(\gcd(a,N)=1\): Bézout gives the inverse in that case; otherwise \(a\) annihilates the nonzero scalar \(N/\gcd(a,N)\). Thus the criterion is that \(p\) be smaller than the least prime divisor of \(N\).

Over the universal ring itself the uncorrected construction already has exact order for \(p\geq2\): the order-\((p+1)\) bush reads the samples of \(X^p\), so over \(\mathbb Q\) its normalized error is
\[
-(p+1)\int_0^1 \prod_{j=0}^{p-1}(X-j)\,dX\ne0 .
\]
The integrand has constant nonzero sign on \(0<X<1\); the error is an element of \(\mathbb Z[1/p!]\) by its original paid-width expression. This does not by itself prove failure in positive characteristic. The path correction gives one witness valid uniformly over all the stated rings and all prescribed diagonals.

The [Euler extrapolation bounds](EULER-EXTRAPOLATION.md) are smaller when no common diagonal is prescribed: \(1+p(p-1)/2\) stages for ERK with merged origins and \(p(p+1)/2\) for DIRK with variable unit diagonal. Here the extra flexibility is an arbitrarily prescribed **single** diagonal value, not an improved minimum stage count.
