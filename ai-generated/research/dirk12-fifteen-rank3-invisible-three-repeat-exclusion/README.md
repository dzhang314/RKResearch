# DIRK12/15: three repeats with reverse cubic supported on all three are impossible

Work in the [invisible four-distinct-ghost, fixed seven-site chart](../dirk12-fifteen-rank3-invisible-four-ghost-fixed-grid/README.md) on the real ordinary order-twelve fifteen-stage \(C(2), f_5=3\) equality face. Assume exactly three repeated live scalar labels, of multiplicities \(3,2,2\), and that the true weighted reverse cubic \(\mathbf G\) is supported at all three repeated labels. **This complete subcase is impossible.** The localized reverse cubic alternative and four repeated pairs are not excluded here. The overall real stage interval remains **15–16**.

Use the true reverse physical order, \(N=A^{\mathsf T}\) in that ordering, reflected clock \(\mathbf y=\mathbf 1-\mathbf c\), and \(J R(X)=\int_0^X R\). The actual forward cubic is \(\mathbf h\), zero at every live row. All four unweighted rows have nonzero physical \(\mathbf h\) at distinct numerical labels; their clocks may coincide with any live scalar clock. Write \(\mathbf W(R)=\mathbf b\odot R(\mathbf y)\). The true weighted reverse flags through grade five have ranks \(1,2,3\) at grades three to five and are \(\mathcal B_j=\mathbf G P_{j-3}(\mathbf y)\) there, by generation, clock lifts and three-label independence. They vanish at all singleton live rows and all unweighted rows. The aggregate of \(\mathbf G\) at each repeated live label is zero, whereas the ordinary scalar quadrature weight sum there is positive.

The literal reverse origin \(0\) is singleton. Denote the other three singleton live labels in physical order by \(a,b,c\), and the repeated labels by \(z_1,z_2,z_3\). Call a group **spent** if all its physical live rows have occurred. Call it **split** if two already observed live rows at its label have different values \(G_i/b_i\). Each multiplicity-two group is spent whenever split. Each group ultimately splits: if the normalized amplitudes were always some one number \(\rho\), its weighted \(\mathbf G\) aggregate would be \(\rho\) times its strictly positive ordinary quadrature mass, contrary to aggregate zero and the nonzero support. These terms refer only to the actual prefix, not to any choice of scalar ordering of the nodes.

By the [preceding chronological proof](../dirk12-fifteen-rank3-invisible-three-repeat-chronology/README.md), all three repeated labels start before \(a\), and at least two have split before \(b\). We additionally need that **the first observed normalized amplitude at every repeated group is nonzero**. Indeed at such a live debut there were at most two other earlier nonzero live labels (no nonzero singleton has yet appeared). If \(G_i=0\) then the actual \(\mathcal B_5\) vanishes there, so the actual scalar primitive is exact through degree four. With at most one earlier nonzero node, the true primitive on \(X(X-y_i)(X-u)^2\), using that node \(u\) if present, has nonzero integral and zero numerical input. With two earlier distinct \(u,v\), the nodal polynomial \(X(X-y_i)(X-u)(X-v)\) asks
\[
                         3y_i^2-5(u+v)y_i+10uv=0,
\]
excluded by the [portable fixed-grid arithmetic](../dirk12-fifteen-rank3-one-active-third-debut/README.md). This covers a possibly zero normalized value in the triple: it cannot be the first observed value, but later rows need not be nonzero.

## One true causal pairing with two independent profile spaces

For \(S\in P_5\) in the reflected scalar variable, the actual forward state
\[
                   \mathbf v_S=S(\mathbf y)-\mathbf h\,Q_S(\mathbf y)
\]
is supported on live rows if the four ghost ratios \(S(y_i)/h_i\) are values of a quadratic \(Q_S\). This is one linear constraint on \(S\), not four independent losses of rank: interpolate the four ratios by a cubic, and impose zero leading coefficient. The state is genuine forward grade five since \(F_5=\mathbf hP_2(\mathbf c)\) and reflection preserves degrees. At every live row it reads \(S\) at that row's clock. At every ghost it is zero, regardless of clock overlap.

Independently, for \(R\in P_5\), \(Q_R\in P_2\), the weighted state
\[
                     \mathbf w_R=\mathbf W(R)-\mathbf G Q_R(\mathbf y)
\]
is a genuine reverse grade-five state with scalar profile \(R\). Its actual reverse primitive is \(\mathbf W(JR)\) plus a genuine pure error in \(\mathcal B_6\). For a physical cut in the reversed chronology, take \(\mathbf v_S\) supported strictly before the cut, and \(\mathbf w_R\) supported on or after it. Then the actual \(N\mathbf w_R\) is still supported on or after the cut by lower triangularity. The genuine weighted error in \(\mathcal B_6\) annihilates the full forward \(T_5\) by paid grade \(6+5=11\). Hence scalar quadrature at the same paid total degree gives the exact cut
\[
                   0=\langle\mathbf v_S,N\mathbf w_R\rangle
                     =\int_0^1 S(X) J R(X)\,dX .
\]
This uses an actual weighted reverse grade-five state, not a presumed reverse rooted-order theorem or a deweighting at an unweighted ghost.

## Cut immediately before \(a\): at most one repeated group can be spent

Suppose two or three repeated groups have been spent strictly before the physical row \(a\). For the late weighted state take \(Q_R=0\) and
\[
                 R\in F P_1,\qquad F=X\prod_{i=1}^{3}(X-z_i).
\]
Both independent profiles are admissible since every prior live row is at \(0\) or a repeated label. For the early ordinary state, all three singleton labels \(a,b,c\) still occur on the late side, and at most one repeated group \(r\) still occurs. Thus use the unrestricted scalar hull subspace \(G P_{5-\deg G}\), with \(G=(X-a)(X-b)(X-c)\), multiplied by \(X-r\) if that group is still present. Its dimension is respectively three or two, and one ghost-mask equation gives codimension at most one. Any allowed \(S\) yields the actual early support.

The cut matrix on the unrestricted scalar spaces above has rank two by the fixed arithmetic below. Vanishing when \(S\) ranges over a codimension-at-most-one subspace and all two-dimensional \(R\) are allowed would instead force rank at most one. This proves the spent-group prohibition at the first singleton, with no assumptions on amplitudes of a still-unspent triple.

## Cuts strictly after \(a\) and before \(b\): exactly two split groups are impossible

Suppose a physical cut in this interval has exactly two split labels \(d,e\), and the remaining label \(r\) is unsplit. The third group has started and its common observed normalized amplitude \(\rho\) is nonzero by the first-debut guard. For each scalar profile in
\[
                       R\in F P_1,\qquad F=X(X-a)(X-d)(X-e),
\]
choose \(Q_R\) to be a scalar multiple of \((X-d)(X-e)\), scaled so that \(R(r)=\rho Q_R(r)\). This is always possible since the three repeated labels are distinct and \(\rho\ne0\). At split sites both scalar values are zero, so the correction matches every observed row regardless of its amplitude, including a zero normalized value. It also vanishes numerically on the earlier singleton rows \(0,a\), and on every earlier unweighted row automatically. Thus **all two** independent late weighted profiles are available.

For early forward profiles, the late live labels include \(b,c\), and the unsplit \(r\) still has a later row because every group ultimately splits. Each split multiplicity-two group is spent, and only the triple can be split but unspent. Thus \(G=(X-b)(X-c)(X-r)\), with at most one additional factor \(X-e\) after naming the possibly unspent split label \(e\). Again \(G P_{5-\deg G}\) has dimension at least two before the one ghost-mask equation. The same two fixed matrix shapes have rank two, contradicting the true causal pairing.

There are at least two split labels just before \(b\). If exactly two, the second cut is a contradiction. If all three, their final first-split event has taken place **after** \(a\), since splitting all three before \(a\) would already spend both pairs, forbidden by the first cut. A physical cut immediately before that final first-split event, with \(a\) already on its early side, has exactly two split groups and \(b\) still on its late side. The second cut is again a contradiction. This exhausts the chronological possibilities of the stated subcase.

## Arithmetic

In every cut the late-input hull \(F\) consists of \(0\) and a three-element subset of the other six fixed Lobatto labels. The early-test hull \(G\) consists of the complementary three labels, with optionally one extra factor from the nonzero labels in \(F\). The coefficient matrices have rows
\[
                 M_{ij} = \int_0^1 G(X) X^i J(F(X)X^j)\,dX,
                 \qquad 0\le j<2,\quad 0\le i<6-\deg G .
\]
Polynomial multiplication and monomial integration at \(1013\) show rank two in all \(20\) no-overlap and all \(60\) one-overlap choices. The two shapes account for all four physical cut patterns; the overlap choice ranges over **every** possible shared label, not only one ordered position of the potentially unspent triple. The degree budget is eleven. At the simple split prime \(1013\), the five interior residues are \(347,468,507,546,667\). Full rank transfers by a nonzero minor at a prime of the fixed Lobatto splitting field above \(1013\), using only small monomial integration denominators; no unknown ghost clock, moment, amplitude or tableau coefficient is reduced.

    python3 -B check.py

The optional Python output reconstructs the literal portable Lean matrix source:

    python3 -B check.py /tmp/DIRKOrderTwelveFifteenInvisibleRepeatSpentCut.lean

The Python replay verifies all 80 fixed-role matrices by computing nonzero two-row minors. It also emits a candidate Lean source; no Lean verification of that generated source or of the actual paid support argument is claimed here.
