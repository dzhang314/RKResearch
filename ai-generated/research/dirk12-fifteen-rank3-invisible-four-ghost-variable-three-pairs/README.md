# DIRK12/15: three live pairs are impossible on the variable eight-site grid

Consider ordinary real order-twelve DIRK in fifteen physical stages with \(C(2), f_5=3\), and invisible weighted forward cubic. Suppose exactly four zero-weight physical rows are cubic-dirty at four distinct clocks. Suppose the live grid has eight sites, seven of them appearing among the ten nonterminal live physical rows, and the live repetitions are exactly three pairs. This chart is impossible. The proof works with either sign of each clock and physical weight, permits zero aggregate weight at a pair, and uses **no fixed-grid arithmetic**.

Together with the [two-repeat exclusion](../dirk12-fifteen-rank3-invisible-four-ghost-variable-two-repeats/README.md), this closes the \(m=7\) variable grid from the [exact nonterminal-site quotient](../dirk12-fifteen-rank3-invisible-four-ghost-variable-grid/README.md). Thus exactly four distinct cubic-dirty ghosts on a variable grid require \(m=9\) or \(m=10\) distinct nonterminal live sites. The real order-twelve interval remains **15–16**.

## The actual three centered pairs

As in the quotient proof, the actual ghost axes belong to \(F_6\), and \(T_6\) is the span of those four axes, the actual terminal axis and the degree-at-most-six scalar evaluations. The scalar terminal is unique among live rows. In true reverse physical order put \(N=A^{\mathsf T}\), \(\mathbf y=\mathbf 1-\mathbf c\), \(Y=\operatorname{diag}(\mathbf y)\), \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\), and \(JP(X)=\int_0^X P\). The exact \(\mathcal B_5=\operatorname{Ann}T_6\) is the direct sum of the three centered physical pair lines. In particular every genuine defect through grade five is zero on ghosts, singletons and the origin. The rank-two actual \(\mathcal B_4\) is a subspace of that sum.

Let \(z_1,z_2,z_3\) be the three repeated reflected clocks, all nonzero. Let \(a,b\) be the first two nonzero singleton live clocks in reverse chronological order. Such \(a,b\) exist since there are four nonzero singleton live sites. A pair is **spent** when both its physical rows have occurred. Its mass is the sum of its two nonzero output weights. If its mass is zero, any centered physical covector has equal normalized values on the two rows: both the weights and the covector coordinates are opposite. This is why a completed zero-mass pair never causes a mismatch in the corrected inputs below.

For any repeated label \(s\), its block indicator belongs to actual \(T_6\): use the scalar cardinal on the seven nonterminal sites, then subtract its evaluations at the four ghost axes and the literal terminal axis. If the pair has already been spent, this indicator is supported through that early physical cut. Let \(R\in P_4\), \(\boldsymbol\eta\in\mathcal B_4\), and suppose the actual input \(\mathbf W(R)-\boldsymbol\eta\) is zero through that cut. True triangularity also kills its actual primitive there. Its discrepancy from \(\mathbf W(JR)\) is in \(\mathcal B_5\). Pairing with the block indicator, at genuine budget \(6+5=11\), gives
\[
                         m_s JR(s)=0.
\]
In particular a spent pair of nonzero mass forces \(JR(s)=0\). No scalar formal profile of the corrected indicator is needed; only its actual \(T_6\) membership and numerical support are used.

## All three repeated clocks have appeared before the first singleton

With zero or one earlier nonzero live clock \(z\) before \(a\), the true degree-four primitive at \(a\) cannot integrate \(X(X-a)(X-z)^2\): the actual input is zero through \(a\) but its integral to \(a\) is nonzero by its definite sign. Use \(z=0\) if there is no earlier nonzero clock.

Suppose exactly two earlier nonzero live clocks \(d,v\) have appeared before \(a\). Any nonzero-mass pair spent in this prefix would contradict the preceding cut with \(R=X(X-s)(X-t)^2\), where \(s\) is the completed label and \(t\) is the other. This integral at \(s\) is nonzero on the segment between \(0\) and \(s\). Therefore each observed pair is seen either just once or twice with zero mass. In both cases the true cubic \(\mathbf G=N\mathbf W(X^2)-\mathbf W(X^3)/3\), a member of \(\mathcal B_3\), has a common normalized amplitude on all earlier rows at each of these labels. The first nonzero live debut \(d\) has amplitude \(d^3/6\ne0\) by the two exact leading weighted identities.

For every scalar cubic \(S\) with \(S(0)=0\) and its values at \(d,v\) matching these two amplitudes, \(\mathbf V=\mathbf W(S)-\mathbf G\) is zero before \(a\). Its genuine grade-five commutator \(YN-NY-N^2\) is pure, because the scalar identity is \(XJ-JX=J^2\). The commutator is zero at \(a\) and its literal diagonal is \(-N_{ii}^2\). Thus the input or the diagonal there is zero, so both actual primitive reads on \(\mathbf V,Y\mathbf V\) are zero at \(a\). Their grade-four and grade-five discrepancies yield \(JS(a)=J(XS)(a)=0\).

The two moment tests have rank two on the scalar cubics with zero constant coefficient, by scaling \(X=a u\) and the nonsingular first two columns of the \(u\)-weighted moment matrix. Their kernel is therefore one-dimensional. The differences between these interpolants \(S\) span the nonzero cubic \(X(X-d)(X-v)\), so the kernel would be just its line. But this line is zero on \(d,v\), whereas \(S(d)=d^3/6\ne0\), contradiction. Thus all three repeated live labels appear before \(a\).

## No nonzero-mass pair is spent before the second singleton

Before \(a\), at most one nonzero-mass pair can be spent. Take the bare scalar input for \(R_0=X\prod_{j=1}^3(X-z_j)\), which is zero on the entire earlier weighted prefix. At each completed nonzero-mass label the paid cut demands \(JR_0(z_j)=0\). Each such root is double, as is \(0\). A nonzero degree-five primitive cannot have three distinct double roots, proving the assertion.

Fix one observed physical row at each repeat. Their three normalized readings identify the pure space \(\mathcal B_5\) with \(\mathbb R^3\), since it is exactly the sum of three centered pair lines and all three observed weights are nonzero. The readings of \(\mathcal B_4\) form a two-dimensional subspace \(U\). If a nonzero-mass pair is spent at \(s\) before \(a\), there is no other such pair by the preceding count. The subspace of \(U\) zero at \(s\) has dimension at least one, and gives at most one compatibility condition on the other two normalized coordinates. Choose a nonzero
\[
                              R\in X(X-s)(X-a)P_1
\]
whose values at those two other labels match such a vector, possible because the displayed scalar space has dimension two. Let \(\boldsymbol\eta\in\mathcal B_4\) give the matching readings and vanish at \(s\), hence on the whole physical \(s\)-pair. The actual \(\mathbf W(R)-\boldsymbol\eta\) vanishes on every earlier live and ghost row through both the spending cut at \(s\) and the first singleton \(a\). On the other pair labels, this is true even if a zero-mass pair has completed, because its normalized readings are equal. Its actual primitive vanishes at \(a\), and its grade-five error vanishes there; therefore \(JR(a)=0\). The cut also forces \(JR(s)=0\). Then \(JR\) has double roots \(0,s,a\), impossible at degree at most five for nonzero \(R\).

This rules out any nonzero-mass spending before \(a\). If such a spending occurs between \(a\) and \(b\), consider the first one. The very same correction works through both the earlier singleton \(a\) and the spending event: no other nonzero-mass pair has completed, and the only additional live singleton before the spending event is \(a\), where \(R\) is zero. It gives the same forbidden three double roots. Consequently all earlier pair readings are uniform within each observed block through the prefix before \(b\), including zero-mass pairs.

## Two clean receivers cannot share the paid mask

Take the scalar space \(S\in X(X-a)P_2\), of dimension three, with the one additional linear condition that its three values on the repeated labels belong to \(U\). At least two independent such profiles exist. For each, choose its actual \(\mathcal B_4\) correction. The corrected weighted input is zero on the entire physical prefix before \(b\), including at \(a\) and the origin, and its grade-five primitive reads exactly at both actual singletons. Thus \(JS(a)=0\). Since \(S(0)=S(a)=0\), their primitives are divisible by \(B=X^2(X-a)^2\) and have degree at most five. They have dimension at least two, so they are exactly \(B P_1\).

At the physical row of \(b\), the corrected input has numerical coordinate \(b_b S(b)\), using \(b_b\ne0\) for the output weight at this row. Its earlier coordinates are all zero. The exact grade-five primitive therefore demands
\[
                           JS(b)=N_{bb} S(b)
\]
for every one of these scalar profiles. The primitive \((X-b)B\) has value zero and derivative \(B(b)\ne0\) there, so \(N_{bb}=0\); the primitive \(B\) then forces \(B(b)=0\), contradiction.

All stage deductions are analytic with the genuine order-twelve weighted flag. The argument uses neither sixth-grade reverse debts nor any assertion about the rooted order of a normalized reverse method. No complete native Lean lower theorem is claimed.

The [support and grade ledger](support-grade-ledger.md) spells out the actual mask chronology. The [native scalar module](../../lean/RKCert/ReviewedNative/DIRKOrderTwelveFifteenVariableGhostScalar.lean) checks the polynomial, sign, and two-receiver gates in Lean/Mathlib 4.36.0; see the [axiom replay](mathlib-4.36-replay.txt).
