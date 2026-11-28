# DIRK12/15: the anchored grade-five rank-four face has at most two active cubic-dirty labels

For an ordinary real lower triangular Runge–Kutta tableau of order twelve in fifteen physical stages, assume \(C(2)\) and \(\dim F_5=4\), where \(F_j\) is the genuine rooted zero-profile space through grade \(j\) (tree order minus one). Put
\[
 \mathbf h=A\mathbf c^{\,2}-\mathbf c^{\,3}/3,\qquad
 r=\#\{c_i:b_i h_i\ne0\}.
\]
Then \(r\le2\). This is a necessary equality restriction, not a sixteen-stage lower bound. The \(C(2)\) condition and grade-five rank four are the **only additional forward hypotheses** on this face; no condition on signs, repeated node values, zero weights, or any independently normalized adjoint is assumed. In particular the weighted transpose is not asserted to be a Runge–Kutta method.

## What order and equality already give

Use \(T_j\) for actual numerical rooted spans, distinct from \(F_j\). The known grade-six surplus, strict forward/reverse growth, and paid midpoint separation give
\[
 \dim T_5=10,\quad (\dim T_6,\dim T_7,\dim T_8,\dim T_9)=(12,13,14,15),\quad
 \dim F_6=5.
\]
The [equality frame](../dirk12-fifteen-frame/README.md) proves that the two leading reversed rows vanish. The last physical weight is nonzero (otherwise trim against the established fifteen-stage floor). The terminal \(t\) has clock \(1\), literal zero column of \(A\), and \(\mathbf e_t\in T_6\setminus T_5\). The last exclusion uses the degree-five unanchored debit, paid at \(2\cdot5+2=12\). It does not use a degree-six terminal debit. The true zero origin comes from \(C(2)\). Also all \(F_5\) vanish at the terminal, by the actual rooted product with \(\mathbf e_t\) at total grade \(5+6=11\).

The unit gain \(F_5\to F_6\) forces \(F_5\) noninvariant under multiplication by the clock matrix \(C=\operatorname{diag}(\mathbf c)\); otherwise two inclusive opposite-primitive detections cost two dimensions. This uses the distinct quadrature-active clocks supplied by scalar order, not distinctness of all physical rows. Thus
\[
                 F_6=F_5+CF_5.
\]
It follows that **all** \(F_6\) vanish at the literal terminal too. In its unique anchored scalar-plus-defect decomposition, \(\mathbf e_t=H(\mathbf c)+\mathbf f_6\), the scalar satisfies \(H(0)=0\) and \(\int_0^1 x^jH(x)\,dx=b_t\) for \(0\le j\le5\). These six tests have grades \(6+j\le11\). Let \(L_6\) be shifted Legendre, normalized by \(L_6(1)=1\). The six moments of \(x L_6'(x)\) equal 1 by integration by parts. The \(x\,dx\) Hilbert Gram uniquely fixes \(H=b_t xL_6'(x)\); evaluating at the clean terminal gives
\[
               H(x)=xL'_6(x)/42,\qquad b_t=1/42.
\]

## A single adjoint plane controls fiber uniformity

Let \(\beta\mathbf v=\mathbf b\odot\mathbf v\) denote pointwise weighting. Genuine rooted products give \(\beta F_5\subset U_0:=\operatorname{Ann}T_6\), whose dimension is three. The three weighted columns \(\beta\mathbf h,\beta C\mathbf h,\beta C^2\mathbf h\) belong to this space, with actual grades 3, 4, 5. If \(r\ge3\) they are independent by interpolation on the three or more active dirty labels. Therefore
\[
  U_0=\beta F_5=\beta\mathbf h\,P_2(\mathbf c),
  \qquad
  \beta F_6=U_0+CU_0\subset\beta\mathbf h\,P_3(\mathbf c).
\]
In particular \(\mathbf h^{\,2}\in F_6\) implies the existence of a fixed \(P\in\mathbb R[X]\), \(\deg P\le3\), with \(h_i=P(c_i)\) on every active dirty row. This follows by dividing only \(b_i h_i\) at those rows. Thus all active members of each dirty fiber have the same nonzero defect value. The assertion does not constrain unweighted ghosts.

The genuine \(\mathbf h\)-moments through scalar degree eight are zero (grade \(3+8=11\)). For \(3\le r\le9\) this gives a zero \(\beta\mathbf h\) aggregate on each dirty label, hence a zero ordinary mass there. Such a label has at least two active physical rows. After discarding all dirty rows the degree-eleven scalar quadrature is carried by the clean rows. It still needs at least seven distinct active labels, because an at-most-six-site rule containing the live terminal \(1\) would annihilate \((1-x)V(x)^2\), where \(V\) vanishes on the other at most five labels. This polynomial has degree at most eleven and positive integral. Hence \(r\le4\). If \(r=4\) exactly four opposite-weight equal-defect pairs and seven distinct active clean rows use all fifteen slots.

## Inclusive reverse cut: three and four labels are impossible

Read physical rows backwards and let \(N=A^{\mathsf T}\) in this reflected order, with \(y=1-c\). For a scalar polynomial \(Q\), write \(\mathbf W(Q)=\mathbf b\odot Q(\mathbf y)\), and \(\mathbf W_d(Q)\) for its restriction to active cubic-dirty physical rows. Define \(Z=\{\mathbf v\in\operatorname{Ann}T_5:v_t=0\}\), of dimension four because \(\mathbf e_t\notin T_5\). It contains \(U_0\). If \(\deg Q\le5\), the genuine reverse discrepancy \(N\mathbf W(Q)-\mathbf W(JQ)\) belongs to \(Z\): the primitive grade is at most six, tests against \(T_5\) are paid at \(5+6=11\), and the literal terminal column is zero. Here \(JQ(x)=\int_0^xQ\). If \(\mathbf W_d(Q)\in U_0\), then \(N\mathbf W_d(Q)\in Z\) by \(A T_5\subset T_6\) and the literal terminal column.

Let \(u,v\) be the first two distinct nonzero active **clean** reverse clocks. Use \(S=X(X-u)(X-v)\). For \(Q=S M\), subtract the actual dirty restriction as above. The input then vanishes through the second detector inclusive: after removal it is supported on active clean rows only, and all possible earlier clean clocks are \(0,u,v\). The two output samples are exactly \(-b_i J(SM)(y_i)\), with both weights nonzero.

For \(r=3\), \(\mathbf W_d(Q)\in U_0\) for **every** \(Q\) by the three uniform fibers and quadratic interpolation of \(Q(1-c)/P(c)\) on the labels. Use \(M\in P_1\). The two sampled primitive values are independent because their simultaneous vanishing would give an antiderivative of degree at most five with three distinct double roots. The sampled rows kill \(U_0\), so \(Z\) would have dimension at least \(3+2=5\), impossible.

For \(r=4\), the four physical pair contrasts span **all** of \(Z\): their grades through \(\beta C^3\mathbf h\) are at most six, and interpolation realizes all four. They vanish at the terminal. Their three-dimensional subspace \(U_0\) has codimension one. Use \(M\in P_2\) in the same inclusive cut. Asking \(\mathbf W_d(SM)\in U_0\) spends at most one linear condition, leaving at least two dimensions. The two primitive reads have simultaneous kernel of dimension at most one, by the same three double roots now for degree at most six. Thus some resulting vector in \(Z\) has a nonzero clean sample, impossible for a linear combination of four dirty pair contrasts. The highest input degree is five; it is not necessary to request a forbidden degree-seven primitive.

## High support and the possible unweighted ghost

Suppose \(r\ge10\). From the actual terminal decomposition and \(\beta F_6\subset\beta\mathbf h P_3(\mathbf c)\), a polynomial \(R\) of degree at most three satisfies \(H(c_i)+P(c_i)R(c_i)=0\) on the \(r\) active dirty labels. The polynomial has degree at most six, so
\[
                         H=-P R .
\]
In particular \(\deg P=3\) and \(P(1)\ne0\). Every active nonterminal clean clock is a root of \(H\).

Let \(k\) count distinct active clean clocks outside \(\{0,1\}\). If \(k\le1\), take their nodal hull \(V\), of degree at most one. The actual weighted \(\mathbf h\) test against \(x(1-x)V^2P\) equals the ordinary scalar integral of \(x(1-x)V^2P^2\): active dirty rows satisfy \(h_i=P(c_i)\), and at all active clean rows the scalar prefactor vanishes. This is paid, since the test has degree at most seven, grade \(3+7\le11\), and the ordinary product has degree at most ten. Its integral is strictly positive. Thus \(k\ge2\). Counting the physical origin and terminal plus \(r+k\) required rows leaves at most one other physical row.

In fact **one nonorigin unweighted ghost is necessary**: \(\dim F_5=4\) while \(\beta F_5=U_0\) has rank three. A nonzero kernel vector is supported on zero-weight rows and is zero at the true origin. Hence precisely one ghost \(g\) remains outside the origin, \(r=10,k=2\), and the kernel is the actual coordinate \(\mathbf e_g\in F_5\). Then \(A\mathbf e_g\in F_6\), whose weighted profiles are supported on cubic-dirty active rows. It follows that **every active clean row has literal tap \(A_{ig}=0\)**. This is not a hypothetical folding or an assumption that the ghost itself is a clone.

Now let \(\mathbf z=\mathbf c\odot(P(\mathbf c)-\mathbf h)\), of actual grade at most four. Its terminal entry is \(P(1)\ne0\). At the first nonzero **active** entry, a clean row \(i\) of nonzero clock \(u\) has no earlier nonzero active input, and it ignores the one nonorigin ghost by the literal tap result. The true origin coordinates are zero in \(\mathbf z\). The primitive errors of \(\mathbf z\) and \(C\mathbf z\) belong to \(F_5,F_6\), respectively, and both vanish at this active clean row. Therefore
\[
       A_{ii}uP(u)=J[xP](u),\qquad
       A_{ii}u^2P(u)=J[x^2 P](u).
\]
We have not refunded an implicit diagonal in an unpaid grade. If the pivot is nonterminal, \(H(u)=0\), \(P(u)\ne0\), and eliminating the diagonal gives \(J[x(x-u)P](u)=0\). If it is the terminal \(u=1\), its own diagonal is actually zero, so \(J[x^2P](1)=0\).

## Exact mod-43 certificate

Clear polynomial coefficients for \(H\) by 42 and clear primitive denominators by 60. Modulo 43, \(H\) has exactly the six distinct roots \(0,2,9,22,35,42\) and nonzero leading coefficient; \(1\) is not a root. Enumerate all monic cubic root factors \(P\).

- All 50 **nonterminal** cases \(u\ne0\) a root of \(H\) outside \(P\) give \(J[x(x-u)P](u)\ne0\).
- All 20 cases \(u=1\) give \(J[x^2P](1)\ne0\). For comparison, the diagonal-eliminated test itself has two terminal exceptions; it is not used there.
- The stronger auxiliary receipt \(J[x^2P](u)\ne0\) also holds in all 70 cases, but a general nonterminal pivot need not be explicit.

To infer the characteristic-zero nonvanishing, take the product of the corresponding cleared values over all ordered choices of a root triple and pivot, with \(0\) distinguished. This product is symmetric in the five nondistinguished roots, hence belongs to the rational coefficient ring after inverting the leading coefficient. Its mod-43 specialization is nonzero. A zero complex (in particular real) root-factor case would make that same rational product zero. No arbitrary tableau coefficient is reduced modulo 43.

The finite arithmetic checks in the dependency-free core Lean module leave the genuine rooted/rank reductions above as mathematical arguments. The scope of all conclusions is the \(C(2)\), \(f_5=4\) face only.

## Replay

    python3 -B check.py
    sha256sum -c sources.sha256
