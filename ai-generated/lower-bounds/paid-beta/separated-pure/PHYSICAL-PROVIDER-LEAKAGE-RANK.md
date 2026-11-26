# Physical provider rank with genuine leakage

Let \(A\) be strictly lower triangular over a field. Let \(E_j,F_j\) denote actual rooted and pure spaces through tree degree \(j\) (tree size \(j+1\)). The clock \(C\) multiplies coordinatewise by \(\mathbf c=A\mathbf1\). Unary extension applies \(A\) numerically and the zero-origin primitive \(J\) on the formal polynomial. Assume paid integers and separation through at least degree \(b-1\), where \(b\ge2\). No ordinary final output is needed.

For a physical set \(S\), identify the coordinate space on \(S\) with vectors padded by zero elsewhere. Write \(S^{\rm c}\) for the other physical positions and \(V\subseteq K^S\) for any numerical subspace containing every literal clock polynomial of degree at most \(b-1\) restricted to \(S\). Define
\[
    g\coloneqq\dim(F_{b-1}\cap V),\qquad
    e\coloneqq\operatorname{rank}(F_b\longrightarrow K^{S^{\rm c}}),\qquad
    q\coloneqq\dim V+e-g .
\]
**Cut inequality.** The actual ranks satisfy
\[
                         q\ge \lfloor b/2\rfloor .                \tag{1}
\]
It neither assumes a flat run nor identifies \(V\) with an invariant core. In particular each actual pure leakage direction is counted only once.

## Correcting the physical off-cut primitive

Let \(Q\) be the actual quotient of \(F_b\) by its vectors zero off \(S\), of dimension \(e\). For any physical stage \(i\notin S\), let \(\boldsymbol\alpha_i\) be its incoming row read on \(V\); let \(\boldsymbol\delta_i\) be the coordinate evaluation at \(i\) on \(Q\). For \(\mathbf g\in F_{b-1}\cap V\),
\[
        \boldsymbol\alpha_i\cdot\mathbf g
                        = \boldsymbol\delta_i\cdot[A\mathbf g].
\]
Indeed the numerical vector \(\mathbf g\) is supported on \(S\) and \(A\mathbf g\in F_b\). The space of possible pairs \((\boldsymbol\alpha_i,\boldsymbol\delta_i)\) therefore has dimension at most \(\dim V+e-g=q\). These \(g\) equations are independent since any functional on \(F_{b-1}\cap V\) extends to \(V\).

For \(\deg P\le b-1\) define its actual primitive error
\[
                     \mathbf R(P)\coloneqq AP(\mathbf c)-(JP)(\mathbf c)
                          \ \in F_b .
\]
At \(i\notin S\) the corresponding exact primitive up to its own clock satisfies
\[
 (JP)(c_i)
   =\boldsymbol\alpha_i\cdot P(\mathbf c)|_S
     -\boldsymbol\delta_i\cdot[\mathbf R(P)]
     +\sum_{\substack{j<i\\j\notin S}} a_{ij}P(c_j).
\]
The first two terms together form a scalar row on \(P_{\le b-1}\) in one fixed space of dimension at most \(q\). The error read and the failure of the incoming row to kill captured pure directions are the **same** \(Q\)-coordinate in this equation. Adding their ranks separately would give a weaker statement.

If the dimension of the actual corrected scalar row space is \(r\) and \(b\ge2r+2\), there can be at most \(r\) distinct nonzero clocks off \(S\). Indeed, otherwise let \(x_1,\ldots,x_{r+1}\) be the first such labels in physical order. Restrict the \(r+1\) rows \(P\mapsto(JP)(x_i)\) to polynomials vanishing at \(0,x_1,\ldots,x_r\); their rank would be at most \(r\). They are independent by the same Hermite interpolation as in 41ea72fa…: a primitive of degree at most \(2r+2\) can have arbitrary values at those \(r+1\) clocks, value zero at 0, and derivative zero at the \(r+1\) earlier evaluation labels. Thus in the range \(r<\lfloor b/2\rfloor\) the actual off-cut evaluation rank is at most \(r+1\).

If \(q<\lfloor b/2\rfloor\), then \(r\le q\) is in that range. The space
\[
        P_{\le b-1}(\mathbf c)\oplus(F_{b-1}\cap V)
\]
has dimension \(b+g\) by genuine separated data. On \(S\) its restriction is in \(V\); off \(S\) it has rank at most \(q+1\), from the labels just counted. Thus \(b+g\le\dim V+q+1=g+2q-e+1\le g+b-1\), a contradiction. This proves (1). Notice that the proof did not need model separation at degree \(b\), where the genuine primitive errors live.

A direct version of (1) takes \(V\) to be \(F_{b-1}\cap K^S\) plus the literal clock reads on \(S\) through degree \(b-1\). The term \(\dim V-g\) is then precisely the rank of those literal reads modulo the pure directions actually supported on \(S\). One may keep the stronger measured \(r\): if \(r<\lfloor b/2\rfloor\), then \(b+g\le\dim V+r+1\). These are physical observation inequalities, not bounds inferred from the number of nominal clock values alone.

## Producing such a cut from a nonflat numerical flag

Let \(U\) be the maximal \(C\)-invariant subspace of \(F_a\), using its direct sum of actual clock-local intersections, with \(a\ge b\). At each clock \(x\) compare the local intersections of \(F_a\) and \(F_{a+b}\). Call a clock exceptional if the latter intersection is strictly larger. This definition uses actual numerical supports. When \(x\) is not exceptional and \(\mathbf u\) is in the \(x\)-part of \(U\), the product \(\mathbf f\odot\mathbf u\) for \(\mathbf f\in F_b\) belongs to the same \(x\)-part of \(U\): it is in \(F_{a+b}\) and is supported on that clock.

Put
\[
  G_j^0\coloneqq
      \{\mathbf f\in F_j\cap U:\mathbf f\text{ is zero on the exceptional clock fibres}\},
  \qquad \ell_j\coloneqq f_j-\dim G_j^0 .
\]
These losses can be read as the rank outside \(U\) plus the rank of the captured part restricted to the exceptional clock fibres; neither is an assumed number of heads. For \(S\) take the actual support of \(G_b^0\). For each member \(\mathbf f\) of \(G_b^0\), multiplication by \(\mathbf f\) preserves \(U\): on the other clock fibres use the preceding equality; on exceptional fibres it is zero. Interpolating its support indicator and taking unions now puts \(\mathbf1_S\) in \(U\) and makes the projection onto \(S\) preserve \(U\). With \(V=U|_S\), padded by zero, this provides all required literal polynomial data. The captured \(G_{b-1}^0\) lies in \(F_{b-1}\cap V\) and \(G_b^0\) is zero off \(S\), so (1) gives the nonflat bound
\[
     \dim U
          \ge f_{b-1}+\lfloor b/2\rfloor-\ell_{b-1}-\ell_b .       \tag{2}
\]
No relation between the actual pure ranks at consecutive grades was imposed. If the usual outgoing Hermite rank rent on \(U\subseteq F_a\) is also available, then
\[
 f_{a+1}\ge f_{b-1}+\lfloor b/2\rfloor+\lfloor(a+1)/2\rfloor
                          -\ell_{b-1}-\ell_b .
\]
The two losses are concrete measured restrictions, not clock counts guessed from a plateau. If they are large, the argument gives no unconditional pure surplus. If they are zero, this reduces to the fully captured off-core argument of 41ea72fa…. The next note gives a different way to force extra numerical rank from measured polynomial matrix clock profiles instead of assuming such captures.
