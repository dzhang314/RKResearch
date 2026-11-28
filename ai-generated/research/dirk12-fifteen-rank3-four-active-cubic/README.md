# DIRK12/15: four active cubic labels on the \(C(2), f_5=3\) equality face

Let \(A\) be an ordinary real lower triangular 15-stage tableau of rooted order twelve with \(C(2)\), and let \(f_5=\dim F_5=3\). Here \(T_j\) is the genuine numerical rooted span, \(F_j\) its pure zero-profile span, and grade means tree order minus one. Put \(\mathbf c=A\mathbf 1\), \(C=\operatorname{diag}(\mathbf c)\), \(\beta\mathbf v=\mathbf b\odot\mathbf v\), and \(\mathbf h=A\mathbf c^{\,2}-\mathbf c^{\,3}/3\). Then:

- \(\mathbf h\) cannot have five through nine distinct **active dirty labels** \(c_i\) (a physical row is active dirty if \(b_i h_i\ne0\)).
- If it has exactly four such labels, each of the four has **zero ordinary weight sum on its dirty rows**. The four nonzero-mass triples are impossible; the four cancelling pairs are not excluded here.
- In the separate minimal reverse grade-six rank-four face, if \(\beta\mathbf h\ne0\) then there are at least ten active dirty labels.

No unrestricted fifteen-stage exclusion is claimed. The real bound is still 15–16. All counts allow signed weights, repeated clocks and zero weights unless the count itself forces otherwise.

## Genuine grade budgets and mass counts

Use the actual [15-stage equality frame](../dirk12-fifteen-frame/README.md). It gives \(f_6=5\), \(\dim T_5=9\), actual initial reverse defects \(D(1)=D(2)=0\) and a live explicit physical terminal \(t\), \(c_t=1\), with literal zero column. Under \(C(2)\) the first physical row is literal zero and has clock zero. All \(F_5\) vanish at terminal, since the paid \(q=5\) debit (\(2q+2=12\)) gives \(\mathbf e_t\in T_6\setminus T_5\) and the paired pure budget is \(5+6=11\). In particular both physical endpoints are clean. We do not assume the same for all \(F_6\) at this point.

Write \(r\) for the number of active dirty labels, and \(m_\ell(z)=\sum_{i:b_i h_i\ne0,\ c_i=z}b_i h_i^\ell\). The vanishing of the true pairings of \(\mathbf h\) against scalar powers through eight and of \(\mathbf h^2\) through five implies \(m_1(z)=0\) if \(r\le9\), and both \(m_1(z)=m_2(z)=0\) if \(r\le6\), by Vandermonde. There must be at least two active dirty rows at each such label. With exactly two rows and both moments zero, their \(h_i\) are equal and their weights opposite: subtract \(h_i\) times the first from the second identity, then divide the other nonzero \(b_j h_j\). Thus a label with nonzero ordinary dirty mass \(m_0(z)\) requires at least three dirty rows.

Let \(q\) be the number of nonzero dirty masses when \(r\le6\). Scalar quadrature is supported in the union of the active clean clock labels and those \(q\) labels. This **candidate** union contains \(1\) because the terminal is physically live and clean; it need not have nonzero aggregate at \(1\). If there are at most six candidate labels, use the product of \(1-X\) and the squared nodal hull of all the other labels. Its degree is at most eleven and its integral over \([0,1]\) is positive, but it is zero on the quadrature support. Thus there are at least \(7-q\) active clean physical rows. Counting at least \(2r+q\) active dirty rows gives \(s\ge 2r+7\), which excludes \(r=5,6\). For \(7\le r\le9\), just the first moment gives at least \(2r\) dirty rows, plus the two actual clean endpoints, impossible.

For \(r=4\), every count above is tight. All fifteen weights are nonzero. The cancelling fibers have two rows with identical \(h\) and opposite weights; each noncancelling fiber has exactly three rows. Active clean rows are at distinct labels, disjoint from noncancelling dirty labels. The union of the two kinds of candidate scalar labels is exactly seven distinct points including \(0,1\). If \(1\le q\le3\), the true \(\mathbf h^3\) probes through scalar degree two (\(9+2=11\)) force \(m_3(z)=0\) on the \(q\) noncancelling fibers, since the cancelling pairs have zero \(m_3\) and interpolation separates the remaining at most three sites. On a three-row fiber with \(m_1=m_2=m_3=0\), localize at the at most three distinct nonzero numerical amplitudes \(h_i\). Their first three weighted powers have Vandermonde rank equal to the number of amplitudes, so all their weight aggregates are zero. This contradicts noncancellation. Thus \(q=0\) or \(q=4\).

For the last general statement in the opening, use the [weighted reverse band](../dirk12-fifteen-weighted-reverse-band/README.md) and let \(\mathcal B_j\) be its true reverse pure space through grade \(j\). Its grade-three, four and five prefix ranks are \(1,2,3\), and its grade-six rank is four or five. Its terminal-zero cap is \(8-f_5=5\). If grade six has rank four, the noninvariance and weighted four-debut argument of that note applies without change: it uses the ranks and budgets, not the numerical value of \(f_5\) beyond certifying rank four. Consequently the genuine reflected cubic \(\mathbf G\), spanning \(\mathcal B_3\), has at least five physical labels. If \(\beta\mathbf h\ne0\), it spans that line by the paid \(3+8=11\) product. The excluded interval 5–9 then forces \(r\ge10\).

## Four noncancelling fibers force clean \(C(6)\) in both directions

Assume \(r=q=4\). Each dirty triple has three distinct nonzero \(h\)-values: otherwise the first two weighted powers suffice to force cancellation at each of its one or two amplitudes. There are exactly three clean rows at \(0,u,1\). All seven numerical clocks are the fixed 7-node Lobatto grid. Indeed if \(V\) is the monic hull of the five nonendpoints, the true scalar moments give \(\int x(1-x)V(x)R(x)\,dx=0\) for \(\deg R\le4\) at degree at most eleven. The positive Gram for \(x(1-x)\) fixes \(V\) as proportional to \(L'_6\), the derivative of the usual shifted Legendre polynomial, using integration by parts. The whole argument with these fixed rational moments does not require treating any unknown tableau coefficient modulo a prime.

The four clock labels give independent head powers. The dimensions \(f_3=1,f_4=2,f_5=3\) imply \(F_j=\mathbf h P_{j-3}(\mathbf c)\) for \(j=3,4,5\). Since \(\mathbf h^2\in F_6\) and its values within a triple are not a common scalar times \(\mathbf h\),
\[
        F_6=\mathbf h P_3(\mathbf c)+\langle\mathbf h^2\rangle.
\]
In particular **all** \(F_6\) are zero on the three clean rows, for this subface only.

The genuine weighted reverse \(\mathcal B_6\) contains \((\beta\mathbf h)P_3(\mathbf c)\), of rank four, because \(\beta\mathbf h\) spans \(\mathcal B_3\). If the grade-six rank were four then the displayed space would be all of it and invariant under the clock: the four head powers exhaust the four physical labels. The paid incoming weighted two-detector gain at grade five into six contradicts the actual unit \(3\to4\) gain. Therefore \(\mathcal B_6=Z\), the terminal-zero cut in \(\operatorname{Ann}T_5\), of rank five. Ordinary products place \(\beta F_6\) inside \(Z\) at \(6+5=11\), and \(\beta\) is invertible in this subface. Thus \(\mathcal B_6=\beta F_6\) and in particular all its vectors vanish on clean rows. Likewise \(\mathcal B_j=\beta F_j\) for \(j=3,4,5\), by the head powers and ranks. The actual reverse chronology is the reordered weighted transpose \(N=A^{\mathsf T}\) on covectors, with reflected clocks \(\mathbf y=\mathbf1-\mathbf c\). These conclusions use only true scalar reverse contexts. They do not assert that a full transposed method has rooted order twelve.

At the lone interior clean row, the actual forward aggregate primitive on all scalar inputs through degree five is therefore exact to upper endpoint \(u\). Its six candidate node labels are \(0,u\), and the four dirty clocks. In reverse chronology, after dividing that row by its nonzero weight, it is exact to \(1-u\) on the reflected six-node set (the image of \(1,u\), and the four dirty labels). The diagonal is the same \(A_{ii}\) in both readings. Lagrange interpolation uniquely determines every aggregate tap on these full six-node sets, with a missing tap treated as zero. The arithmetic below shows that all these taps are nonzero, including the diagonal. Every dirty triple consequently has at least one physical row on each side of the interior clean row and is split as \(2+1\) or \(1+2\).

## Exactly two doubled labels are needed on either side

Work in one direction, with primitive \(J[P](x)=\int_0^xP(t)\,dt\) in its own clock variable (so the clean pivot is \(u\) in this notation). Suppose at most one dirty label is doubled strictly before that pivot. Let \(d\) be that label if there is one, otherwise any dirty label, and \(Q=X-d\). Interpolate \(P\) of degree at most four on \(0\) and the four dirty labels by \(P(0)=0\) and \(P(z)=h_i Q(z)\) for a prior dirty row at \(z\). This matches all earlier rows, including both rows at the possible double, because \(Q(d)=0\). At the other three labels the values are nonzero, hence \(P\ne0\). In reverse use the same construction with reflected labels and multiply the contrast by \(\beta\); both operations are valid in the actual weighted flag.

The genuine grade-four contrast \(P(\mathbf c)-\mathbf h Q(\mathbf c)\) (or the weighted reflected contrast) vanishes strictly before the pivot. If \(P(u)\ne0\), the chronological commutator \(CA-AC-A^2\), or \(YN-NY-N^2\) in the reversed chronological order, gives \(-A_{ii}^2\) times that nonzero pivot value. The output is genuine pure of grade at most six because the scalar commutator \(XJ-JX-J^2\) is zero, and the pure grade-six space vanishes at the clean pivot. This contradicts its known nonzero diagonal. Thus \(P(u)=0\). The input is now zero *including* the pivot. Applying the actual primitive directly and after one extra scalar power forces \(JP(u)=J[XP](u)=0\), using only pure errors in grades five and six. We have
\[
                  P=X(X-d)(X-u)S,\qquad \deg S\le1 .
\]
For all twenty distinct fixed interior ordered pairs \((u,d)\), the \(2\times2\) moment matrix for \(X(X-d)(X-u)\,dX\) integrated from \(0\) to \(u\) is nonsingular by the arithmetic below, so \(S=0\), contradiction. Neither direction has at most one doubled label. Every dirty triple is doubled in precisely one direction, so there are exactly two doubled labels in each direction.

## The opposing paid grade-five cut excludes all thirty splits

Return to the original clock \(x\). Let \(D_f,D_b\) be the two disjoint sets of two dirty labels doubled before and after the clean pivot, respectively. There are exactly eight physical rows through the pivot inclusive in each direction: its origin, six dirty rows, and the pivot. The grade-five forward numerical space \(P_5(\mathbf c)+\mathbf hP_2(\mathbf c)\) has rank nine, so choose a nonzero state \(\mathbf v=P(\mathbf c)-\mathbf hR(\mathbf c)\) of grade at most five that vanishes on the entire forward eight-row prefix. Its scalar profile \(P\) is nonzero: if \(P=0\), the correction polynomial \(R\) of degree at most two would vanish at all four dirty labels via their earlier rows. On each doubled label the two distinct \(h\)-values force \(R(z)=P(z)=0\); and \(P(0)=P(u)=0\) on the two earlier clean rows. In addition \(JP(u)=0\) by chronological evaluation of \(A\mathbf v\) and grade-six cleanliness at the pivot. The reverse grade-five space of scalar words and pure rows is \(\beta(P_5(\mathbf c)+F_5)\), also of rank nine. Its nonzero counterpart \(\mathbf w\) vanishing on the reverse eight-row prefix has a nonzero scalar profile \(Q\) with \(Q(1)=Q(u)=0\), \(Q(z)=0\) for \(z\in D_b\), and \(\int_u^1Q(x)\,dx=0\).

In each direction the four specified roots leave a free affine factor. The one nontrivial primitive functional fixes a line. Explicit representatives are
\[
\begin{aligned}
 U_f(X)&=X(X-u)\!\!\prod_{z\in D_f}(X-z),&
 P_0(X)&=U_f(X)\left(\int_0^u xU_f(x)\,dx-X\int_0^u U_f(x)\,dx\right),\\
 U_b(X)&=(X-1)(X-u)\!\!\prod_{z\in D_b}(X-z),&
 Q_0(X)&=U_b(X)\left(\int_u^1 xU_b(x)\,dx-X\int_u^1 U_b(x)\,dx\right).
\end{aligned}
\]
The nonzero mixed integrals below check that neither of the two primitive functionals has both coefficients zero. Thus \(P,Q\) are nonzero multiples of \(P_0,Q_0\).

The actual \(A\mathbf v\) is supported strictly *after* the pivot by triangularity; \(\mathbf w\) is supported strictly *before* it by definition. Thus their scalar pairing is zero. By rooted order it equals \(\int_0^1 (JP)(x)Q(x)\,dx\), with the paid grades \(6+5=11\). This may also be regarded as an ordinary rooted product because \(\mathbf w=\beta(\mathbf w')\) with \(\mathbf w'\) a genuine grade-five forward feature of the same \(x\)-profile. The integral is nonzero for **all thirty** choices of pivot and forward double pair by the arithmetic below, contradiction. This closes \(q=4\) and leaves only \(q=0\) when \(r=4\).

## Exact finite-grid arithmetic and scope

The fixed polynomial is \(L'_6=-42+840X-5040X^2+12600X^3-13860X^4+5544X^5\). It splits into five simple roots \(2,9,22,35,42\) modulo \(43\). The independent arithmetic uses monomial primitives and checks:

1. all 30 forward six-node Lagrange tap numerators are nonzero (reflection covers the reverse list);
2. all 20 weighted \(2\times2\) primitive determinants are nonzero;
3. all 30 mixed grade-five cut integrals are nonzero.

These are checks on the actual fixed-grid **polynomials**, not modular reductions of arbitrary tableau coefficients. Take the product over all relevant choices of labeled roots for each numerator or determinant. It is a symmetric expression in the five roots, with small primitive denominators and a leading coefficient unit modulo 43; tap denominators are differences of distinct roots. The product therefore lies in the rational localization at 43 and its mod-43 residue is nonzero. Any real root-factor case with value zero would force that product zero before reduction. This is the entire exact arithmetic transfer.

Python independently reconstructs all the polynomial expressions and checks the finite values. The portable **DIRKOrderTwelveFifteenFourDirtyArithmetic** checks the same fixed arithmetic on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The reviewed **DIRKOrderTwelveFifteenRankThreeCore**, checked on Lean/Mathlib 4.36.0, proves the first three genuine rooted cubic-power probes at their exact grades (for the denominator-cleared cubic defect), the literal opposing chronology pairing, and the actual grade-six reverse rank-four or saturated rank-five alternative. The logs list standard axioms only. The combined reduction excluding the noncancelling four-label case is mathematical, not an end-to-end Lean fifteen-stage theorem.

    python3 -B check.py
    lean ../../lean/RKCert/ReviewedNative/DIRKOrderTwelveFifteenFourDirtyArithmetic.lean
    # From ai-generated/lean, in its pinned Lean/Mathlib environment:
    lake build + RKCert.ReviewedNative.DIRKOrderTwelveFifteenRankThreeCore

From the repository root:

    sha256sum -c ai-generated/research/dirk12-fifteen-rank3-four-active-cubic/sources.sha256
