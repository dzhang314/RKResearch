# Independent source audit: Native's successive marks and simultaneous support rank

**Mathematical verdict: PASS as stated over fields, with an explicit non-circular reading of the gauge paragraph.** The general \(r\)-step theorem and its sharpened degree windows are paper results, not compiled Lean results. The displayed trajectory of commutator witnesses presupposes the actual last diagonal already paid; it does not by itself refund an unknown last diagonal through its own top gauge. No numerical stage bound is inferred.

Manifest SHA-256 642961176fc8f6c42f50bac4ff30d34e304c7ccc117c260a2d7efa51bc396b5f verified, and all five sealed files passed:
- SUCCESSIVE-MARKS-AND-SUPPORT.md 7187dbfce2e44b0324a0073d6d5e3c9d354dc0b5cb468ccb7b194902e73c8991
- PROVENANCE.txt 1818821dfd89b421b2862db54bc3cbef144cf69575a31a5ba9fa4f6db5bb022e
- MeasuredMarkGauge.lean 92782d50158eb731a12d695c7d4b4ed06742c89bf1e2b831fdc60ad4e69341c1
- PaidSuccessiveMarkRoots.lean 04e271bb6176eb0e63b94137229da5770fc537785ac9d9fc7e5d6ee56fdee13f
- PaidSupportMarkRank.lean 104f82165343acff7d8c6705a0b7cf215530fc76b732d9b49ec6ae4598640dd3

Read-only audit also checked the exact declared local provider text/hashes for PaidDIRKLocalMarks.lean, PaidDIRKLocalTwoTests.lean, and PaidPrimitiveJets.lean. No build, elaboration, solver, numerical replay, repository write, held path or current quantitative application.

## 1. All marks and rescues are paid on the original tableau

Use \(F_j,E_j\) for actual nested spaces with true scalar profiles. At step \(a\) put \(g_a=k+a-1\), \(B_{a-1}=\prod_{j<a}(X-u_j)\), and \(W=XP\). The numerical adjusted column \(z_a=(B_{a-1}W)(c)-B_{a-1}(c)\odot\mathbf a\) belongs to \(E_{g_a}\) with genuine profile \(B_{a-1}W\); the second term is in \(F_{g_a}\) by iterated paid clock multiplication. The scalar degree is at most \(d+a\le k+a-1=g_a\). If \(P\ne0\), the profile is nonzero. Separation through \(2g_a+1\le p\) makes \(z_a\ne0\) without assuming a physical zero row. The optional one-condition saving is also correct: if a polynomial profile \(f\in\mathbb P_{g_a}\) has \(f(0)=0\) and its numerical evaluation is pure at grade \(g_a\), testing it against degree \(\le g_a-1\) is paid already at \(p\ge2g_a\). Write \(f=Xf_0\) and use the fixed \(x\)-weighted Gram on degree at most \(g_a-1\), cutoff \(2g_a\). No positivity of unknown factors is needed. This saving is not claimed in the staged Lean consumer.

Numerically \(z_a=B_{a-1}(c)\odot z_1\), so it vanishes on \(S\). Its first actual nonzero row is outside \(S\); **every** \(F_H\) discrepancy vanishes there by the actual cover. By nesting, the filtered adjustment also vanishes there. Therefore that genuine coordinate reads \(B_{a-1}(u_a)W(u_a)\ne0\), forcing both a nonzero clock and distinction from all earlier clock labels. Multiplying by \(C-u_a I\) erases the current physical row, so the next first row is strictly later. This is why a repeated numerical clock cannot supply a second mark under the hypothesis. No head-by-head normalization, injective polynomial reconstruction on a projected tableau, or presumed order after deletion appears.

At this first row, the true Volterra commutator \(D=CA-AC-A^2\) costs two, so \(D z_a\in F_{g_a+2}\subset F_H\) using \(a\le r\le m-1\). Its actual leading row equals \(-a_{ii}^2(z_a)_i\) by lower triangularity; the field and nonzero pivot give \(a_{ii}=0\). For any \(R\) of degree \(\le m-a\), the actual input \(R(C)z_a\) is genuine at grade at most \(k+a-1+m-a=H-1\), with numerical zeros on the earlier rows. Its \(A\)-output has zero at the current row by this diagonal refund and true scalar discrepancy in \(F_H\). This reads exactly \(J_0(R B_{a-1}W)(u_a)=0\). The highest grade \(F_H\) is used only for actual support/vanishing, not for a weight moment beyond the order. In particular \(H=p\) causes no extra pairing: primitive and commutator identities use units through polynomial degree \(H\le p\).

This is a field proof, valid in fields with the paid units. In a ring with zero divisors, \(-a_{ii}^2(z_a)_i=0\) and a merely nonzero pivot do not give the diagonal; rank and distinct-clock root factors also require appropriate splitting/cancellation. A residue-field use must reverify actual support, ranks and nonzero hypotheses there. No assertion of a ringwise coefficient conclusion in the presence of nilpotents follows just by reduction.

## 2. Sharp \(r\)-step scalar count

Let \(n_a=m-a+1\), so \(T_a=J_0^{n_a}(B_{a-1}W)\). The \(n_a\) independent powered moment tests yield the centered moments by expanding powers of \(X-u_a\); hence the first \(n_a\) primitive evaluations vanish and \(T_a\) has a zero of order \(n_a\) at \(u_a\). Its origin order is at least \(n_a+1\) from the \(X\) factor of \(W\). It is nonzero and has degree at most \(d+m+1\le H\), with all derivative and primitive denominators paid. The exact identity
\[
 T_{a+1}=(X-u_a)T_a'-(m-a)T_a
\]
is the usual one-step integration-by-parts relation for an iterated primitive. It keeps the current \(u_a\) multiplicity on that transition, because the derivative's potential loss is restored by \(X-u_a\); each later step loses at most one. Thus at step \(r\), the previous \(r-1\) sites have multiplicity at least \(m-r+2\), the origin the same, and the last mark at least \(m-r+1\). All are distinct. The degree lower bound is \((r+1)(m-r+2)-1\), and comparing with \(d+m+1\) gives \(d\ge r(m+1-r)\), the exact contradiction threshold. The requirement \(r\le m-1\) is real: it is needed for the \(+2\) diagonal budget. The paper degree maxima for one, two, and three marks, and its four example conditional counts 4, 5, 6, 8, follow by additionally minimizing with \(d\le k-1\).

## 3. Physical ranks and the simultaneous-head limitation

The range of actual \(1_S c P(c)\) over unrestricted polynomials consists exactly of columns supported on \(S\), zero on its numerical zero clocks, and constant on the portions of each nonzero fibre inside \(S\). In a field its dimension is the number \(\nu\) of distinct represented nonzero clocks, by literal Lagrange interpolation. The theorem first shows injectivity on \(\deg P\le d\) by choosing \(\mathbf a=0\), then disjointness from \(F_k\) for a single actual adjustment in that space. Thus
\[
 \nu\ge d+1+\dim(F_k\cap\mathcal L),\qquad |S|\ge d+1+\dim F_k .
\]
For the second bound both spaces are supported on the actual chosen rows (nested \(F_k\subset F_H\)), so restriction is injective on their direct sum. It is not a new method on \(S\). For the first, the contrast map's kernel on \(F_k\) is exactly the stage-supported, zero-at-zero, whole-fibre-constant subspace. Rank-nullity gives the displayed contrast formulation. A sum of head labels or even of individual head dimensions does not replace this intersection. The three-row example at each clock over \(\mathbb Q\) really can have two independent sum-zero directions per clock, including their full polynomial spans, and no nonzero constant on any fibre. It is not asserted to be an actual RK flag.

## 4. Gauge: exact sufficient observation, not a self-paying diagonal

If \(Z=F_H\cap\ker L\) vanishes at all the known mark rows and honest witnesses \(W_0\subset F_H\) vanish there, equality \(L(W_0)=L(F_H)\) pays the entire endpoint cut by subtraction. Neither nonzero gauge values alone nor a truncated smaller range suffices. With a smaller range, an unspecified functional can annihilate the witness images without annihilating the quotient; this is an obstruction to the argument, not a counterexample to every more structured tableau.

For the displayed family \(D(C^j z_r)\), \(0\le j\le m-r-1\), the true grade is \(k+r+1+j\). The only top member can be \(j=m-r-1\); if \(F_{H-1}\subset Z\), all others have zero gauge. Hence this **particular family** contributes at most one gauge direction; no claim that every conceivable operation on the same carrier is rank one. Earlier numerical marked rows see zero by strict chronological prefix. The last row sees zero because its diagonal is **already** zero. If \(r=m-1\), even \(D z_r\) is at top grade \(H\). Without F_H vanishing or another actual refund, its last entry is \(-a_{ii}^2(z_r)_i\); declaring it an honest zero-first witness to pay that same diagonal would be circular. If \(r\le m-2\) and \(F_{H-1}\) already vanishes at the genuine marks, the unshifted \(D z_r\) is lower grade and can independently refund its last diagonal. In all cases the actual zero/witness and image test must be separately certified.

## 5. Lean source boundary

The local provider matches the paper's first physical failure, actual square-diagonal refund, and primitive cut. PaidDIRKLocalTwoTests carries the older \(m\ge4\), \(\deg P\le m+1\) two-mark conditions; the staged support consumer retains them exactly, so it does not implement the sharper paper \(m=3\) or general \(r\) claim. Its stronger global equality with the weighted evaluation is supplied by the paper mask match on \(S\) and true support of \(\mathbf a\) outside it.

The staged weighted-site bound and raw stage-rank bound implement separate actual linear dimension deductions; the injectivity of the restricted direct-sum map uses physical support, not a quotient order. The primitive transition and two factor-retention lemmas are the relevant scalar steps; the declared paid primitive provider aligns with their degree requirements. The measured gauge map theorem is the stated unconditional linear subtraction under actual image inclusion. No compiled status for these staged files is claimed, and the \(r\)-step theorem is not presented as a checked Lean theorem.
