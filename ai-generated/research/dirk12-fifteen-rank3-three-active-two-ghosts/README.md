# DIRK12/15: three all-cancelling labels and two zero weights on the fixed grid

This excludes the remaining **fixed seven candidate clock** case with three active cubic-dirty labels in a real ordinary fifteen-stage order-twelve \(C(2), f_5=3\) tableau. The [small fixed-grid cut](../dirk12-fifteen-rank3-three-active-fixed-grid/README.md) proves all other fixed seven cases. The real stage interval remains **15–16**; three active dirty labels with a genuinely variable eight- or nine-site scalar grid are not excluded here.

Work in the all-cancelling case \(q=0\) with exactly two zero-weight physical rows. The seven active clean labels are the fixed Lobatto nodes. Every such label is represented, because its scalar aggregate weight is positive by the nodal-square tests. Each of the three active dirty labels has at least two active dirty rows. Thus all fifteen positions are accounted for: seven distinct live clean rows, six active dirty rows in three uniform-amplitude opposite-weight pairs, and the two unweighted physical rows. Either the literal origin is live or one of those unweighted rows is the literal origin; the terminal is live. No restriction is placed on the clock or cubic defect of the other unweighted rows.

Write \(T_j,F_j\) for the genuine numerical and pure forward spaces, at tree grade \(j\). The \(T_6\) separation and exact saturation in the actual equality frame give \(\dim T_6=12\). The three weighted tests \((\beta\mathbf h)C^j\), \(j=0,1,2\), with \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\), \(C=\operatorname{diag}(\mathbf c)\), \(\beta\mathbf v=\mathbf b\odot\mathbf v\), annihilate \(T_6\) by the paid grades three to five. By interpolation on the three labels they span the three supported pair-difference functionals. Hence \(T_6\) is exactly the full twelve-dimensional space of vectors equal within every active dirty pair. In particular the coordinate vector \(\mathbf e_g\) of either unweighted row belongs to actual \(T_6\), not just to some larger abstract span.

For a nonorigin unweighted row \(g\), take an actual grade-six scalar profile \(P\in P_6\) for \(\mathbf e_g\). Its weighted pairings with \(1,\mathbf c,\ldots,\mathbf c^5\) are zero because \(b_g=0\). Rooted order through grade eleven gives \(I(PX^j)=0\) for \(j=0,\ldots,5\). Therefore \(P\) is proportional to the sixth shifted Legendre polynomial \(L_6\). The literal zero origin implies each genuine pair satisfies vector value \(=P(0)\) on that row, and \(\mathbf e_g\) vanishes there. Since \(L_6(0)=1\), \(P=0\). Thus each nonorigin unweighted coordinate is genuinely in \(F_6\). No such assertion is made about an unweighted origin.

## The asymmetric cut pays for the unweighted coordinates

Choose the physical cut after the fourth live clean row. Let \(U,V\) be the sets of the four earlier and three later clean labels, respectively, and \(G\) the monic cubic hull of \(V\). Let \(F\) be the monic hull of \(U\), adjoining the scalar factor \(X\) if the actual origin is unweighted and \(0\notin U\). In particular \(\deg F\le5\).

For any \(S\in F P_1\), choose the degree-two correction \(Q\) interpolating \(S(z)/h_z\) at the three active dirty labels. The actual grade-six vector \(S(\mathbf c)-\mathbf h Q(\mathbf c)\) vanishes at all active dirty rows and at the first four live clean rows. If the origin is unweighted, it also vanishes there by the root \(S(0)=0\) and \(h_o=0\). Now subtract the independently earned pure coordinate vectors of all other unweighted rows, with their appropriate scalar coefficients. This keeps the exact scalar profile \(S\), and the resulting actual grade-six state vanishes through the physical cut.

For \(R\in G P_1\), the degree bound is four. There is at most one scalar constraint on this two-dimensional space to make \(\mathbf v_R=R(\mathbf c)-\mathbf h Q_R(\mathbf c)\) with \(Q_R\in P_1\) vanish at all three live dirty labels: the three values \(R(z)/h_z\) must agree with an affine polynomial. Thus a nonzero scalar line of such \(R\) exists. The actual weighted grade-four test \(\beta\mathbf v_R\) is supported before the cut, since \(R\) vanishes on the later live clean rows and all unweighted coordinates of this test are zero automatically.

Pair that grade-four test with \(A\) applied to the genuine grade-six late-supported state. Lower triangularity gives zero, and rooted order pays \(7+4=11\), identifying it with \(I(R JS)\). With the stated two scalar bases this would require the existence of a nonzero left kernel of the fixed two-by-two matrix
\[
                      M_{ij}=I(GX^i J(FX^j)),\qquad 0\le i,j<2.
\]
The exact checker finds rank two for every four-versus-three split of the grid and both origin possibilities. Its coefficients are only the fixed Lobatto roots and rational primitive values, so the [same mod-1013 full-rank transfer](../dirk12-fifteen-rank3-four-singleton-end-exclusion/README.md) is applicable with no reduction of unknown stages. This contradiction closes the fixed-grid two-unweighted-row case.

    python3 -B check.py

This analytic conclusion is mathematical and is not an end-to-end native Lean lower-bound theorem.
