# DIRK12/15: three active cubic labels on the fixed seven-node grid

In the real ordinary order-twelve fifteen-stage \(C(2), f_5=3\) equality face let \(r=3\) be the number of distinct active cubic-dirty clock labels. Write \(q\) for the number of its dirty labels with nonzero aggregate ordinary dirty weight. The following are excluded:

- \(q=2\), without any extra scalar-grid hypothesis;
- \(q=1\) with exactly seven candidate scalar clock labels, including signed repeats and one possible zero weight;
- \(q=0\) with exactly seven candidate scalar clock labels and at most one zero weight. The [nonuniform amplitude case](../dirk12-fifteen-rank3-three-active-nonuniform-cancelling/README.md) is covered even without a fixed-grid hypothesis.

Here the candidate labels are the active clean labels, the \(q\) noncancelling dirty labels and the two actual boundary clocks \(0,1\), as a union. The remaining \(q=0\) fixed-grid case with two zero-weight rows, and variable eight- or nine-site scalar grids, are not excluded by this note. The real stage interval remains **15–16**.

## Real counts and the actual grade-five profiles

Put \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\). Dirty means \(h_i\ne0\), active dirty means \(b_i h_i\ne0\), and an active clean row has \(b_i\ne0,\ h_i=0\). Three dirty labels are distinguished by the genuine power probes \(\mathbf h^\ell\), \(\ell=1,2,3\), times \(1,\mathbf c,\mathbf c^2\), all in grade at most eleven. Thus \(m_\ell(z)=0\) separately on each dirty label for these three exponents. Every dirty label has at least two active dirty physical rows. If its aggregate ordinary weight \(m_0(z)\) is nonzero then it must have at least four distinct nonzero amplitudes: otherwise the three vanishing weighted powers already force aggregate weight zero at each amplitude. The total active dirty row count is at least \(6+2q\).

The candidate union always has at least seven labels. With at most six, the exactly paid polynomial \((1-X)\) times the squared hull of the other candidate labels vanishes on the quadrature but has positive integral; degree is at most eleven. An upper bound on this union is \(15-(6+2q)+q=9-q\), because the \(q\) noncancelling dirty labels already have their own rows and every other candidate requires a separate stage off the active dirty rows (including a potentially unweighted literal origin). Thus \(q\le2\), and \(q=2\) forces the seven-node case.

When the candidate union has seven labels, it is the fixed Lobatto grid. Indeed its five-interior monic hull is orthogonal to \(P_4\) for \(X(1-X)\,dX\) by exactly paid nodal tests, hence proportional to \(L_6'\). Every candidate label has **nonzero scalar aggregate weight**: at an interior label test \(X(1-X)\) times the square of its four other interior factors, and at either endpoint use the opposite endpoint factor times the square of all five interior factors. Their integrals are positive, and only the corresponding candidate node contributes. In particular, none of the other candidate labels can be supplied solely by a zero-weight row.

Let \(E\) be the set of the \(q\) noncancelling dirty labels and \(C\) the remaining \(7-q\) fixed-grid labels. Every label of \(C\) has an active clean row. Even if an active clean row also occurs at a label in \(E\), it will automatically vanish on the profiles used here. The count leaves at most \(2-q\) spare rows after accounting for the minimum dirt and one clean row for each of the \(7-q\) labels of \(C\). In the \(q=1,2\) cases, this implies every cancelling label has just one active amplitude: two amplitudes would consume at least four rows by the \(m_0,m_1,m_2,m_3\) probes, using two extra rows at that label. In the \(q=0\) case also assume uniform active amplitudes, as the alternative is already excluded.

For any scalar polynomial \(S\in P_5\) vanishing at \(E\), there is a polynomial \(Q\in P_2\) such that the actual grade-five vector
\[
                     \mathbf v_S=S(\mathbf c)-\mathbf hQ(\mathbf c)
\]
vanishes on **all active dirty rows**. Choose \(Q(z)=0\) on \(E\), and \(Q(z)=S(z)/h_z\) at each cancelling label; the three labels are distinct, hence quadratic interpolation works. The construction is linear in \(S\) and uses the genuine \(F_5=\mathbf hP_2\) by rank. At each active clean row the vector reads \(S\) on its actual clock; at every zero-weight row its value is a known linear constraint in \(S\) if needed. No deweighting at such a row is used.

## One exact cut, including unweighted rows

Let \(g\) be the **total number of zero-weight physical rows**. Choose the physical cut after the \(m\)-th active clean physical row with label in \(C\), where \(m=2,3,4\) for \(q=2,1,0\), respectively. Let \(U,V\subseteq C\) be the distinct clean labels from \(C\) occurring before and after the cut, allowing a shared label if there are repeated rows. Then
\[
 U\cup V=C,\quad 1\le |U|\le m,\quad
 1\le |V|\le 15-(6+2q)-g-m .
\]
The final count excludes every active dirty row and every unweighted row, and spends \(m\) actual relevant active clean rows before the cut.

Take \(S\) vanishing at \(E\cup U\), so the only additional constraints for the actual \(\mathbf v_S\) to vanish up to the cut are at most \(g\) zero-weight rows there. The resulting scalar subspace has codimension at most \(g\) in \(P_5\cap \operatorname{hull}(E\cup U)\mathbb R[X]\). Independently choose \(R\in P_5\) vanishing at \(E\cup V\). The weighted earlier test \(\beta\mathbf v_R\), with \(\beta\mathbf v=\mathbf b\odot\mathbf v\), is automatically zero after the cut, including any later zero-weight rows without constraints. Lower triangularity gives zero actual core pairing \(\langle \beta\mathbf v_R,A\mathbf v_S\rangle\). Its genuine rooted scalar value is \(I(R J S)\), paid at \(5+6=11\).

Therefore the linear map \(S\mapsto (R\mapsto I(R J S))\) on the unrestricted scalar hull spaces must have rank at most \(g\). Matrix entries are monomial primitives and integrals of the hull multiples. The exact fixed-grid check below instead gives rank greater than \(g\) for all admissible \(U,V,E\) in the stated cases, even with arbitrary overlap, dirty chronology and placements of the unweighted rows. The allowed cases of \((q,g)\) here are \((2,0),(1,0),(1,1),(0,0),(0,1)\).

## Fixed arithmetic

Using all split root labels modulo \(1013\), the dependency-free checker verifies the ranks for respectively \(210,665,140,546,210\) set triples. It allows \(E\) to contain an endpoint in the finite cases, a harmless enlargement of some actual count cases. The ranks transfer through the same fixed-grid prime as in the [four-singleton packet](../dirk12-fifteen-rank3-four-singleton-end-exclusion/README.md). The only coefficients reduced are from rational polynomial integrals on the seven fixed clock labels, not unknown DIRK tableau entries. This analytic reduction is not an end-to-end native Lean stage-lower theorem.

    python3 -B check.py
