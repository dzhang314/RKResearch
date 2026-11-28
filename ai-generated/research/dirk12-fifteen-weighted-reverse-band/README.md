# A paid weighted reverse band on the fifteen-stage DIRK12 equality face

This is an exact equality restriction, not a new stage count. Work with the [actual fifteen-stage frame](../dirk12-fifteen-frame/README.md), including the established grade-six surplus and live physical terminal obtained by trimming against the known lower bound. Use \(T_j,F_j\) for genuine numerical and zero-profile rooted spans, grade \(j\) meaning tree order minus one. In particular \(f_5=\dim F_5\) is not \(\dim T_5\).

The two facts below are distinct:

1. **On either forward \(f_5\) face, the reflected cubic cannot have exactly two numerical support labels.** If it has three, the grade-six terminal-zero reverse flag is forced to have rank five; three labels are **not excluded** by this statement.
2. **If \(f_5=4\)**, the reflected cubic actually has at least five physical support labels. In combination with the [separate anchored support census](../dirk12-fifteen-anchored-grade-five-support/README.md), this makes every forward cubic-dirty stage unweighted when \(C(2)\) holds.

## The physical terminal-zero ledger and exact budgets

Write \(t\) for the last physical stage, \(N=A^{\mathsf T}\) in reverse chronological order, and \(Y=\operatorname{diag}(1-\mathbf c)\). The actual terminal has \(c_t=1\), \(b_t\ne0\), and a literal zero column in \(A\). Both actual leading reverse defects vanish. For a polynomial \(P\), write \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\) and \(JP(X)=\int_0^X P(x)\,dx\), where \(y_i=1-c_i\). The genuine reflected cubic is
\[
                   \mathbf G=N\mathbf W(X^2)-\mathbf W(X^3)/3 .
\]
It is nonzero by the actual second/cubic two-seed triangular forcing theorem (the second reverse seed is zero and \(\sum b_i y_i=1/2\)).

Write \(\mathcal B_j\) for the all-monomial genuine reverse defect flag through grade \(j\), including its \(N,Y\) descendants in the paid grading. In the native notation this is primitiveBack at **level \(j-1\)**, not level \(j\). Its scalar primitive errors of input degree at most \(j-1\) are included, and both \(N\) and \(Y\) send \(\mathcal B_j\) into \(\mathcal B_{j+1}\). Every member of the flag is zero at the physical terminal. Actual weighted root adjoint pairing certifies \(\mathcal B_j\subseteq\operatorname{Ann}T_{11-j}\) on the grades used. Strict growth and saturation of the already known middle spaces give
\[
\begin{array}{c|ccc}
  j&3&4&5\\ \hline
  \mathcal B_j & \operatorname{Ann}T_8&\operatorname{Ann}T_7&\operatorname{Ann}T_6\\
  \dim\mathcal B_j &1&2&3 .
\end{array}
\]
In particular \(\mathcal B_3=\langle\mathbf G\rangle\). At grade six set
\[
       Z_5=\{\boldsymbol\lambda\in\operatorname{Ann}T_5:
                           \lambda_t=0\}.
\]
As \(\mathbf e_t\notin T_5\) by the genuine unanchored endpoint lemma at \(2\cdot5+2=12\), this is a codimension-one cut in \(\operatorname{Ann}T_5\). Also \(\dim T_5=6+f_5\) by paid degree-five coefficient separation. Thus
\[
       \mathcal B_6\subseteq Z_5,\qquad
       4\le\dim \mathcal B_6\le\dim Z_5=8-f_5.
\]
Only the degree-five endpoint test is used; the unanchored degree-six test would require order fourteen and is not available. The reflected polynomial primitive \(N\mathbf W(P)-\mathbf W(JP)\) of input degree at most five has grade at most six and fits \(5+6=11\) when paired with \(T_5\). Its terminal coordinate is zero from the literal column and \(y_t=0\).

## The actual weighted inclusive two-detector gain

The following argument applies in reflected **physical** chronology to any clock-invariant subspace \(U\subseteq\mathcal B_j\), at \(j=4,5\). Both the input and its lift vanish or match **including** the last detecting row; no diagonal refund is assumed.

There are at least six distinct net-active nonzero reflected clocks: otherwise \(X V(X)^2\), where \(V\) vanishes at the at most five such labels, is an exactly paid scalar polynomial of degree at most eleven and positive integral with zero quadrature. The same assertion over a characteristic-zero field uses all \(X V P\) of \(\deg P\le \deg V\) and the fixed nonsingular \(X\,dX\) Gram. At each such label the actual weight vector cannot be matched by \(U\) across the whole clock block. Indeed invariance allows the same-clock projection by interpolation in \(Y\), and every vector in \(U\) sums to zero. Matching the weight vector in the block would give a vector with nonzero sum.

Pick the first two distinct nonzero weight-block detection failures in the growing physical prefix, with labels \(u,v\). Put \(S=X(X-u)(X-v)\). For \(M\in P_1\), the vector \(\mathbf W(SM)\) matches some vector \(\mathbf L_M\in U\) through the two detecting rows, inclusively. At a failed clock \(S=0\); at nondetecting clocks use the available prefix matches and the invariant block projections. One can choose the lift linear in \(M\) by choosing the lifts for \(S\) first, and then blending by multiplication by \(M(Y)\). The vector
\[
          \mathbf D_M=N\mathbf W(SM)-\mathbf W(J(SM))-N\mathbf L_M
                       \ \in\ \mathcal B_{j+1}
\]
has numerical profile \(-\mathbf W(J(SM))\) through both detecting rows, since true lower triangularity including the diagonal reads equal inputs there. If \(\mathbf D_M\in U\), as long as the primitive value is nonzero at a failure, scaling its prefix provides the prohibited match; thus both primitive values vanish. The primitive has double roots at \(0,u,v\) and degree at most five, forcing \(M=0\). Hence \(\dim\mathcal B_{j+1}\ge\dim U+2\). The actual input polynomial has degree at most four and the primitive grade is at most five in both uses.

If the **higher** space \(U=\mathcal B_{j+1}\) is invariant, repeat this same detector construction inside it. No nonzero multiplier can have its lift \(\mathbf L_M\) in \(\mathcal B_j\), since then its image under \(N\) lies in \(U\), and the same contradiction would force \(M=0\). Thus the lifts are independent modulo \(\mathcal B_j\) and again give a gain of at least two. This is the incoming version; it does not incorrectly place \(N U\) inside \(U\).

If \(\mathbf G\) has exactly two numerical labels, the rank-two \(\mathcal B_4=\langle\mathbf G,Y\mathbf G\rangle\) is invariant by interpolation on those labels; the outgoing grade-four cut gives \(\dim\mathcal B_5\ge4\), contradicting rank three. If it has three labels, \(\mathcal B_5=\langle\mathbf G,Y\mathbf G,Y^2\mathbf G\rangle\) is invariant. The outgoing grade-five cut gives \(\dim\mathcal B_6\ge5\). As \(f_5\ge3\), this forces \(f_5=3\) and \(\mathcal B_6=Z_5\) of rank five, not exclusion.

For the anchored application \(\mathbf h=A\mathbf c^{\,2}-\mathbf c^{\,3}/3\) is a genuine cubic defect and \(\mathbf b\odot\mathbf h\in\operatorname{Ann}T_8\) by grade \(3+8=11\). When nonzero it is proportional to \(\mathbf G\), with exactly the active cubic-dirty labels as support. Thus the two-label exclusion and the three-label forced-rank claim apply to that definition of label, including arbitrary zero weights and repeated physical rows.

## Minimal grade-six flag when \(f_5=4\)

Now \(\dim\mathcal B_6=4\). The two-detector tests forbid invariance of \(\mathcal B_4,\mathcal B_5\) at the outgoing unit steps, and of \(\mathcal B_6\) at its incoming unit step. It remains to check that the reflected cubic cannot be local even at one numerical label. Here one may use the existing [weighted four-debut projection and obstruction](../../lower-bounds/proof-dependencies/dirk_multigrade_confluent_cut_rank_and_weighted_reflection_20261123.md). Its application at order twelve only needs the following grades, not the longer order-thirteen horizon:

- If \(\mathbf G\) is localized on one label, it is an invariant line. A generator \(\mathbf w\) complementary to it in rank-two \(\mathcal B_4\) then gives \(\mathcal B_j=\langle\mathbf G\rangle+\mathbf w P_{j-4}(Y)\) for \(j=4,5,6\), by the two noninvariant unit steps. This is the precise local cubic one-head chart in the cited weighted lemma.
- Project away the earliest nonzero reflected coordinate of the local \(\mathbf G\) line. The projection subtracts a multiple of \(\mathbf G\), so preserves sums and commutes with the physical clock; a scalar weighted polynomial word becomes a weighted polynomial word with the projected weight vector. Chronological elimination preserves lower triangularity even in the implicit diagonal.
- For input grade \(m=3,4,5\), the needed genuine primitive discrepancy on \(\mathbf W(P)-\mathbf w Q(Y)\) is in \(\mathcal B_{m+1}\), with \(\deg P\le m,\deg Q\le m-4\) (negative means zero). The projection error only adds a multiple of \(N\mathbf G\), already grade four. For the scalar-input commutator at \(m=3,4\), \(YN-NY-N^2\) on \(\mathbf W(P)\) has error in \(\mathcal B_{m+2}\): the genuine primitive and single-operator rules cancel its formal scalar profile by \(X J-JX=J^2\). Projecting adds only terms from \(N\mathbf G,YN\mathbf G,N^2\mathbf G\), through grade five. These are the stated primitive and commutator hypotheses of the weighted four-debut obstruction. Every one is in the actual terminal-zero flag through grade six. No product of two reflected features is used.
- The projected scalar functional sums the coordinates and is unchanged because \(\mathbf G\) sums to zero. Its moments through degree seven are still paid; the projected weighted system therefore has at least four distinct nonzero net-active sites. The weighted four-debut theorem forbids that under the stated local single-head chart.

Thus \(\mathbf G\) is nonlocal. The ordinary noninvariant unit-step expansions then give \(\mathcal B_j=\mathbf G P_{j-3}(Y)\) at \(j=3,4,5,6\). Since \(\mathcal B_6\) itself is noninvariant, \(\mathbf G\) has **at least five distinct numerical support labels**. The support statement concerns physical \(G_i\ne0\) and includes unweighted ghosts if present.

In the anchored \(f_5=4\) face the separate census gives at most two distinct active \(\mathbf h\) labels. A nonzero \(\mathbf b\odot\mathbf h\) would be proportional to \(\mathbf G\), which is impossible by the five-label conclusion. Hence the entire anchored rank-four face has \(\mathbf b\odot\mathbf h=0\). In the non-C(2) equality face the same argument also shows \(\mathbf b\odot F_3=0\) whenever \(F_3\) is clock-invariant: a clock-invariant two-dimensional \(F_3\) is supported on at most two clock labels, and every weighted \(F_3\) vector lies in the one-dimensional \(G\) line (grade \(3+8=11\)). These are branch restrictions; the equality case is not closed.

## Native scope

The reviewed module **DIRKOrderTwelveFifteenReverseRanks** checks the native rank prefix, terminal cap on actual grade-six reverse vectors, saturation when \(f_5=4\), and the weighted genuine forward cubic line. The weighted two-detector specialization and low-height four-debut application above are mathematical, not claimed as a full native proof of the final label conclusion.

The native module was checked directly on Lean/Mathlib 4.36.0 with standard axioms only; the direct build and axiom log are preserved. The separate typed consumer is provided as a replay source, not a compatibility claim for another Mathlib version.

    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenReverseRanks
    lake env lean AuditDIRKOrderTwelveFifteenReverseRanks.lean
