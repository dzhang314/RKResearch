# Physical support of the five-node defect space at ERK order eight

Let \(A\) be a strictly lower triangular tableau, \(\boldsymbol{b}\) the output-weight column, \(\boldsymbol{c}=A\boldsymbol{1}\), and \(C=\operatorname{diag}(\boldsymbol{c})\). For \(m\ge1\) let \(V_m\) be the span of the stage defects
\[
 \boldsymbol{\Phi}_t(A)-\frac{|t|}{t!}\boldsymbol{c}^{|t|-1},
 \qquad |t|\le m,
\]
where powers are coordinatewise. Over a field in which the relevant orders are units, this is exactly Lean's zeroSpace A (m−1): normalize each tree by its forest factorial and subtract the normalized bush. The denominator-free Lean definition applies over arbitrary commutative rings as well. Call \(S=\{i:\exists \boldsymbol{v}\in V_5,\ v_i\ne0\}\) its *physical support*. Complementary stages are called pure. Stage 1 is pure with clock zero. No prescribed head, sign on weights, distinctness of clocks, or ordering of clock values is assumed.

For an eleven-stage rational order-eight tableau the following necessary conditions hold:

| \(\dim V_5\) | Physical defect support | Further necessary conditions |
| ---: | --- | --- |
| 3 | At least four stages | If exactly four, they must all occur before the second distinct nonzero pure clock. The first nonzero pure clock has at least three defective predecessors. Pure rows genuinely use two independent restrictions to the four defective columns. The output can use at most one clock from those columns, with at least five distinct pure clocks required. |
| 4 | At least five stages | First reverse balance is pointwise exact, and the terminal clock is one. If exactly five stages are defective, the terminal stage must be pure. |

This does **not** settle unrestricted rational 11-stage existence. No new lower or upper numerical bound for that problem is claimed.

## 1. Native rank split and at least four defective physical rows

For order 8 the explicit midpoint rank is \(5+\dim V_5\), and its reverse budget is
\[
 7+\dim V_5+\dim\operatorname{span}(\boldsymbol{\lambda}_B)\le11,
 \qquad
 \boldsymbol{\lambda}_B=\boldsymbol{b}^{\mathsf T}A-\boldsymbol{b}^{\mathsf T}(I-C).
\]
Forward growth gives \(\dim V_4\ge2,\ \dim V_5\ge3\). It follows that the only ranks of \(V_5\) are 3 and 4, and rank 4 forces \(\boldsymbol{\lambda}_B=\boldsymbol{0}\), over every field of admissible characteristic.

The support exclusion uses already order 5. If all of \(V_5\) is supported in at most three physical rows, their number is exactly three and \(V_5\) is the entire coordinate subspace on those positions. Thus \(b_i=0\) there. On the complement, the restriction of each physical row of \(A\) to those three columns must annihilate \(V_4\), since \(AV_4\subseteq V_5\). These restrictions are collinear, by \(\dim V_4\ge2\).

Let \(h\ne0\) be the first nonzero pure clock, which exists since \(\sum_i b_i c_i=1/2\). At its stage the row restriction to the defective columns is nonzero: its evaluation against the clocks is \(h^2/2\) and all previous pure clocks vanish. Consider
\[
 P_h(X)=X(X-h)(2X-h), \qquad 2\int_0^X P_h(u)\,du=X^2(X-h)^2 .
\]
Each pure stage pays \(A\boldsymbol{c}^{k}=\boldsymbol{c}^{k+1}/(k+1)\) in its own coordinate for \(k=1,2,3\). The first nonzero pure row thus evaluates \(P_h\) to zero; the same holds for all their restrictions to the defective columns, by collinearity. Induction on physical stage indices now gives that every pure clock \(x\) satisfies \(x^2(x-h)^2=0\): earlier pure clocks are 0 or \(h\), where \(P_h\) vanishes. Hence the only pure clocks are 0 and \(h\). The first three nonconstant output moments then give \(2m=1,\ 3hm=1,\ 4h^2m=1\) where \(m=\sum_i b_i c_i\). The first two imply \(3h=2\); substituting in nine times the third gives \(16m=9\), contrary to eight times the first.

This proof uses no ordering or division in the primitive identity. Over an arbitrary nontrivial commutative ring, the support assertion specializes through a maximal ideal, as do the rooted-tree order conditions. Thus no order-five-or-higher explicit tableau over such a ring can have its five-node defects confined to three physical coordinates.

The [Lean module](../../lean/RKCert/ReviewedNative/ExplicitThreeDefectiveRows.lean) proves **RKResearch.Certified.Graded.no_three_physical_defective_rows** (the arbitrary-ring theorem), **no_three_physical_defective_rows_field**, and **width11_order8_defect_rank_options** (the exact field-level midpoint split). In ai-generated/lean run:

    lake build RKCert.ReviewedNative.ExplicitThreeDefectiveRows

The 4.36 kernel checked both printed theorems with only standard axioms. The rational support/chronology arguments below are mathematical proofs, **not** claimed to be Lean formalizations.

## 2. Rank four: exclusions independent of head placement

Write
\[
 \boldsymbol{B}=\boldsymbol{b}^{\mathsf T}A,\quad
 \boldsymbol{D}=\boldsymbol{b}^{\mathsf T}CA,\quad
 \boldsymbol{\lambda}_D=\boldsymbol{D}-\tfrac12\boldsymbol{b}^{\mathsf T}(I-C^2).
\]
The exact rooted conditions imply \(\boldsymbol{\lambda}_B\) kills all stage profiles through size 7, and \(\boldsymbol{\lambda}_D\) kills all through size 6. For instance, at a tree \(t\) of size \(n\), \(\boldsymbol{D}\boldsymbol{\Phi}_t=1/((n+2)t!)\) by grafting a root with children \(t\) and one leaf; the residual's other term gives the same number by adding 0 and 2 leaves to the root of \(t\). Consequently the discrepancies kill \(V_5\) and ordinary clock powers through degrees 6 and 5 respectively. Likewise \(\boldsymbol{b}^{\mathsf T}\) and \(\boldsymbol{b}^{\mathsf T}C\) kill \(V_5\).

The terminal weight is nonzero; otherwise stage 11 may simply be deleted, contradicting the [published 11-stage floor at order eight](../erk-eight-stage-floor/README.md) over ordered fields. In the rank-four branch \(\boldsymbol{\lambda}_B=\boldsymbol{0}\), so the zero last column of \(A\) forces \(c_{11}=1\), and \(\lambda_{D,11}=0\).

We use the [rational endpoint support theorem](../erk-eight-factorial-escape/PURE-HEAD-OBSTRUCTION.md): a rational degree-seven output quadrature must have at least six distinct sites if its list of available sites includes zero. A listed site can have weight zero.

* **Four defective positions anywhere.** If rank and support both equal four, \(V_5\) is exactly the coordinate subspace on \(S\), so both \(\boldsymbol{b}^{\mathsf T}\) and \(\boldsymbol{\lambda}_D\) vanish there. In the seven pure positions there must be at least six distinct clocks, by rational endpoint support. Since stage 11 does not contribute to \(\boldsymbol{\lambda}_D\), the latter lives on at most six positions. Using its vanishing clock moments through degree 5, Vandermonde interpolation implies it has zero total on each clock fibre. Thus, if nonzero, it is supported on a single repeated pair \(i<j\le10\) with opposite coefficients. Its vanishing through tree size 6 then says those two stages agree on all those profiles. Unary grafting shows that their padded matrix rows differ by a row annihilating all profiles through size 5, including \(V_5\) and powers through degree 4. This row vanishes on \(S\) and on indices at least \(j\). There are at most five remaining pure predecessor slots, all distinct in clock value because the only repeated pair loses \(j\). The slot \(i\) is included: its coefficient in row \(j\) is killed by the same interpolation, not assumed zero. Thus the physical rows are identical.

* **Five defective positions with a defective terminal stage.** Suppose \(|S|=5\) and \(11\in S\). The annihilator of \(V_5\) restricted to these coordinates is a line \(L\). The restrictions of \(\boldsymbol{b}^{\mathsf T}\) and \(\boldsymbol{b}^{\mathsf T}C\) to \(S\) lie there; the first is nonzero in the last coordinate. They must be proportional with factor \(c_{11}=1\). Thus all nonzero coordinates of \(L\) have clock 1. The restriction of \(\boldsymbol{\lambda}_D\) to \(S\) also lies there, but is zero at stage 11, so is zero on all of \(S\). There are six pure positions; endpoint support gives at least five distinct pure clocks since the output can use only one more clock, namely 1. Again the discrepancy has at most six positions, so every fibre sum vanishes. Unless it is zero, there is one opposite-coefficient pair \(i<j\) in the pure positions. Their row difference annihilates \(V_5\), so its restriction to \(S\) lies in \(L\). That restriction is zero at stage 11 by explicitness, hence zero on all of \(S\). There remain at most five pure positions before \(j\), with distinct clocks; interpolation through degree 4 proves equality of the physical rows as above.

In either case the two identical rows can be merged at the earlier position: remove the later row, redirect every still later consumer of that row to the earlier position, and sum their two output weights. Strictness is preserved. Induction on trees preserves all retained stage values and the output read, giving an impossible ten-stage tableau. Thus the discrepancy must actually vanish in either case.

Finally both pointwise balances cannot be exact: choose the last \(i\) with \(b_i\ne0\) and \(c_i\ne1\), which exists by the zeroth and first output moments. Every later weighted recipient has clock 1, so \(D_i=B_i\) by strictness. However exactness gives \(B_i-D_i=b_i(1-c_i)^2/2\ne0\). This finishes both exclusions without assuming where other stages lie, or how many nominal slots are weighted.

## 3. Rank three on four coordinates: two independent defect taps

Now suppose \(\dim V_5=3\) and \(|S|=4\). Since \(V_4\) grows strictly to \(V_5\) (the explicit order-eight midpoint separates clocks from defects, and a plateau would make \(V_4\) invariant under both \(A\) and \(C\)), \(\dim V_4=2\). On \(S\) the annihilator of \(V_5\) is a line \(L\). The same \(\boldsymbol{b}^{\mathsf T}\), \(\boldsymbol{b}^{\mathsf T}C\) argument shows that nonzero defective output weights are confined to one clock. Endpoint support forces at least five distinct pure clocks, or at least six if no additional site is used at the defective clock.

The restrictions of pure rows to \(S\) lie in the two-dimensional annihilator of \(V_4\) there. Let \(h\) be the first nonzero pure clock and \(g\) the first pure clock other than \(0,h\). The restrictions of these two rows are independent. Indeed, at the first row evaluation of \(P_h\) from §1 is zero, while at the second it is \(g^2(g-h)^2/2\ne0\); the earlier pure columns make no contribution to either evaluation. The first row's restriction cannot be zero, since it integrates \(X\) to \(h^2/2\ne0\).

There must be at least two distinct nonzero defective clocks before \(h\): if there is only one, \(a\), the \(X,X^2,X^3\) moments from that row give \(a=2h/3\) and \(a^2=h^2/2\), a contradiction in characteristic zero. (No such clock is impossible already for the \(X\) moment.)

On any initial set of physical stages with at least two distinct nonzero clocks, the restriction of \(V_4\) has rank at least 2. To see this, let \(\boldsymbol{r}=A\boldsymbol{c}-\boldsymbol{c}^2/2\), so \(\boldsymbol{r},C\boldsymbol{r},A\boldsymbol{r}\in V_4\). At the first nonzero clock \(a\), \(r_i=-a^2/2\ne0\), and \(A\boldsymbol{r}\) vanishes there since \(\boldsymbol{r}\) is zero before the first nonzero clock. A rank-one restriction would force \(C\boldsymbol{r}=a\boldsymbol{r}\) and \(A\boldsymbol{r}=\boldsymbol{0}\) on the initial set. Inductively, if all earlier \(r_j=-a c_j/2\), the second equality gives \((A\boldsymbol{c})_i=0\), hence \(r_i=-c_i^2/2\). The first equality now implies \(c_i=0\) or \(c_i=a\), extending the induction. This contradicts the second distinct nonzero clock.

Apply this to the strict predecessor prefix of the row with clock \(h\). There the restriction of \(V_4\) has rank two, and is zero off \(S\). Its annihilator on the preceding defective columns therefore has dimension equal to their number minus two. Since the tap at \(h\) is nonzero, at least three defective positions precede it. At the strict predecessor prefix of the row with clock \(g\), both independent restricted taps are available, so all four defective positions must already occur. This reduces the four-coordinate rank-three search without choosing a special Shanks head or requiring that all defects occupy consecutive positions.
