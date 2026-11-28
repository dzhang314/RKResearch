# DIRK12/15: variable scalar sites with four distinct invisible ghosts

Consider the real ordinary fifteen-stage order-twelve \(C(2),f_5=3\) equality tableau with \(\mathbf b\odot\mathbf h=0\), where \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\). Suppose exactly four physical rows have zero weight, all four have nonzero \(h_i\), and they have four distinct numerical clocks. Ghost/live clock coincidences are allowed. Write \(m\) for the number of distinct scalar labels among the **ten nonterminal live physical rows**, excluding the literal final row even if its clock is shared. If the scalar grid is not the fixed seven-site grid, then \(m\ge7\) and:

- \(m=8\) is impossible.
- At \(m=7\) the grid has eight sites with literal terminal numerically unique, and the exact grade-five reverse flag has zero aggregate on each nonterminal site.
- At \(m=9\) there is exactly one repeated nonterminal pair. The true weighted reverse cubic \(\mathbf G\) is local at that pair, both entries nonzero and summing to zero. Its grade-four head has nonzero aggregate on all nine nonterminal labels.
- At \(m=10\) the true weighted reverse cubic is nonzero at all ten nonterminal live rows. Its residues are fixed up to a common scale by the scalar nodal hull.

In all these possibilities the first forward live nonzero clock has at least three preceding ghost rows, and **all four ghosts precede the second distinct forward live nonzero clock**. This last result also holds irrespective of the scalar grid size. These are equality restrictions; the real interval remains **15–16**.

## Exact barycentric quotient of the true grade-five flag

Use the [actual equality frame](../dirk12-fifteen-frame/README.md) and its [true weighted reverse band](../dirk12-fifteen-weighted-reverse-band/README.md). The ordinary \(\mathbf hP_3(\mathbf c)\) columns pay each of the four ghost axes in actual \(F_6\) by cubic interpolation. The literal terminal axis \(\mathbf e_t\) is also in actual \(T_6\). If \(m\ge7\), these five axes and the seven scalar columns in \(P_6(\mathbf c)\) are independent: a polynomial of degree at most six vanishing on all nonterminal live rows is identically zero, and a zero polynomial leaves only the five independent coordinate axes. They fill \(T_6\) of rank twelve. Consequently
\[
   \mathcal B_5=\operatorname{Ann}T_6
      =\{\boldsymbol\lambda:\ \lambda_t=0,\
             \lambda_i=0\text{ on ghosts},\
             \textstyle\sum_i\lambda_i R(y_i)=0\ \forall R\in P_6\}.
\]
Here \(N=A^{\mathsf T}\) in true reverse physical chronology, \(\mathbf y=\mathbf 1-\mathbf c\), and \(Y=\operatorname{diag}(\mathbf y)\). In particular the moments in this formula do not include the literal terminal coordinate. If a nonterminal live row has that same scalar clock, its entry is still included.

For the distinct nonterminal labels \(z_1,\dots,z_m\) in reflected coordinates, set \(D(X)=\prod_j(X-z_j)\), and let \(L_z(\boldsymbol\lambda)\) be the aggregate of its nonterminal live entries at \(z\). If \(m=7\), all aggregates vanish. For \(m\ge8\),
\[
                    L_z(\boldsymbol\lambda)=P(z)/D'(z),
                    \qquad \deg P\le m-8 .
\]
Indeed the sum of \(z^j/D'(z)\) over all \(m\) sites is zero for \(0\le j\le m-2\), by the leading coefficient in Lagrange interpolation. This proves membership of every displayed weighted evaluation in the kernel, and their dimension \(m-7\) equals its exact codimension-seven kernel dimension.

For an actual \(\boldsymbol\lambda\in\mathcal B_j\) with \(j=3,4,5\), all its \(Y\)-lifts through grade five are valid. For \(m\ge8\), the aggregate polynomial \(P\), if nonzero, must therefore satisfy
\[
                             \deg P+(5-j)\le m-8 .
\]
For each lift the weighted interpolation polynomial is \(X^k P\) itself: its degree is still less than \(m\), so no reduction by \(D\) is possible. This is an exact grade budget of the weighted transpose, not a claim that a normalized reverse tableau has rooted order twelve.

## The four nonterminal counts

At \(m=7\) a variable scalar grid must have eight sites, namely the seven nonterminal sites and the additional terminal site. No aggregate can survive. At \(m=8\) all genuine \(\mathcal B_4\) aggregates vanish by one clock lift. In particular its vectors are supported at repeated nonterminal labels, and there are at most two such labels in ten physical rows. The true reverse cubic \(\mathbf G=N(\mathbf b\odot\mathbf y^2)-\mathbf b\odot\mathbf y^3/3\) is nonzero at the first live nonzero reflected clock \(d\): the vanished two leading weighted defects force diagonal \(d/2\) there. It cannot use exactly two labels, by the known clock-invariant rank-two obstruction. If it is local at \(d\), the [true first head](../dirk12-fifteen-rank3-one-active-cubic-head/README.md) gives a grade-four \(\mathbf H=N\mathbf G-(d/2)\mathbf G\) nonzero at the first live distinct nonzero clock \(v\ne d\). Its proof uses only locality of \(\mathbf G\), the vanished two weighted primitive seeds, and absence of ghost entries; it imposes no fixed grid ratio at this second debut. Hence at \(m=8\) there are exactly two repeated labels, each a pair, and all of \(\mathcal B_4\) is in their two-dimensional sum of local pair differences. Equality of dimensions makes \(\mathcal B_4\) invariant, giving the same contradiction. No fifth or sixth unweighted reverse profile was used.

At \(m=9\) the grade-three bound forces \(\mathbf G\) aggregates zero. There is only one repeated pair, which is its local support, with both entries nonzero. The first head is nonzero at the singleton \(v\) by the same true weighted chronology. Its aggregate therefore has a nonzero constant numerator polynomial (one remaining clock lift), so is nonzero at every one of the nine nonterminal labels. Neither the location of the second \(d\)-row nor the terminal clock uniqueness is inferred.

At \(m=10\) the nonzero \(\mathbf G\) has no pair at which to cancel. Its aggregate numerator has degree at most zero, so is a nonzero constant. This gives all ten entries \(\rho/D'(z)\) with one \(\rho\ne0\). In this case \(\mathcal B_5=\mathbf G P_2(\mathbf y)\) by its exact rank three, since the three clock powers are independent at ten support labels.

The usual positive polynomial test ensures at least seven live scalar sites including \(1\). If the total is seven, the [fixed-grid analysis](../dirk12-fifteen-rank3-invisible-four-ghost-fixed-grid/README.md) applies instead; for a variable grid there are at least eight, so at most one loss at the literal terminal gives \(m\ge7\).

## The four actual ghosts must debut early in the ordinary tableau

The forward rank ledger gives \(F_j=\mathbf hP_{j-3}(\mathbf c)\) for \(j=3,4,5\) because the four distinct numerical dirty labels yield independent clock lifts. In particular every live row reads these pure spaces as zero. Let \(a,b\) be the first and second distinct *nonzero* live numerical clocks in ordinary physical chronology. They exist by the scalar site count, and every live row in the prefix through the first \(b\) has clock in \(\{0,a,b\}\).

At the first \(a\), \((A\mathbf h)_a=(A C\mathbf h)_a=0\) by actual grades four and five and \(h_a=0\). With at most two earlier ghosts, their distinct clocks and nonzero amplitudes force all row taps to those ghosts to vanish, by the two equations (with zero or one ghost the claim is immediate). Then the scalar polynomial \(X(X-a)\) is killed by the actual row: no surviving input has clock outside \(0,a\). Its primitive is \(-a^3/6\ne0\), contradicting the true grade-three scalar defect zero at this live row. Thus at least three ghosts precede the first live nonzero clock.

Suppose only three ghosts occurred through the first \(b\). Take a scalar \(S\) from the two-dimensional space \(X(X-a)(X-b)P_1\). An affine polynomial \(Q\) can match the three numbers \(S(c_i)/h_i\) at the earlier ghosts exactly when one homogeneous linear compatibility condition holds. Thus a nonzero \(S\) admits that match. The true grade-four vector \(S(\mathbf c)-\mathbf hQ(\mathbf c)\) is zero throughout this inclusive prefix. At the two live debuts the true grade-five discrepancy is zero, so its primitives are zero there. Hence its scalar primitive \(JS\) has double roots at all three of \(0,a,b\), with degree at most five and nonzero. This is impossible. Consequently all four ghosts precede the first live occurrence at \(b\). This argument allows prior live returns to \(0\) and \(a\), and ghost/live clock coincidences.

For further use, on the variable scalar grid the unique additional live grade-six pure profile is explicit. Any paired scalar profile \(P\in P_6\) for \(\mathbf e_t\) satisfies \(P(0)=0\) at the literal ordinary origin and \(I(PR)=b_t R(1)\) on all \(R\in P_5\) by true grade \(6+5\). By integration by parts and Legendre orthogonality,
\[
                           P(X)=b_t X L_6'(X).
\]
The two sides agree on the five-degree moments and at zero; uniqueness follows from the \(L_6\) line. The actual difference \(\mathbf e_t-P(\mathbf c)\) is zero-profile, and has nonzero live restriction since \(m\ge7\) nonterminal labels cannot all be roots of this nonzero degree-six polynomial. It spans the live projection of \(F_6\), which has rank at most one by the four paid ghost axes. In particular no grade-six extra direction should be silently assumed zero on a live row.

All deductions are mathematical from the previously audited actual typed flags. No new end-to-end native Lean theorem or fixed-grid residue computation is needed for this packet.
