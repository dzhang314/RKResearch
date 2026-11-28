# Ten active labels: the ten-active dormant center is impossible

**Scope.** Continue the [ten-active singleton setup](ERK11-NONZERO-TEN-TEN-ACTIVE-EDGE-EXIT.md) of the all-live, half-clock, two-carrier, two-new-boundary order-eleven equality problem. Here the dormant middle row is physical **9**. It is impossible over characteristic zero. Together with the edge result this excludes the entire \(q=n=10\) branch, without ordering or reverse ordinary order eleven. It does not dispose of other activity counts or change the unrestricted stage interval.

## 1. The central mark is a true shared-row factorization

Use the preceding support, actual clock \(C\), widths \(a,b=1-d\), common cubic model \(K\), and supported \(T'\). Let the actual earlier square-clock vectors be \(V_L,V_R\) with models \(V=X^2(X-a)^2,\ W=(1-X)^2(X-d)^2\). The actual grade-five vectors
\[
 p=AV_L,\quad r=A^\star V_R,\quad
 L_\zeta=C(C-a)T',\quad R_\zeta=(1-C)(C-d)T'
\]
have respective models \(P_a=JV,\ P_b^\star=\bar J W,\ X(X-a)K,\ (1-X)(X-d)K\). Strictness gives \(p=0\) through 8 and \(r=0\) from 10. The literal supports of \(L_\zeta,R_\zeta\) are contained in physical \(\{9,13,17\}\) and \(\{1,5,9\}\) respectively, even if the dormant clock aliases an unrelated active clock.

All four products \(pR_\zeta,\ L_\zeta r,\ pr,\ L_\zeta R_\zeta\) are paid as mixed grade-five products, and in this center placement their supports lie at the **same physical row 9**. Write their respective scalar integrals as
\[
 I_L=\int(1-X)(X-d)P_aK,\quad
 I_R=\int X(X-a)P_b^\star K,\quad
 J_0=\int P_aP_b^\star,\quad
 I_K=\int X(1-X)(X-a)(X-d)K^2.
\]
The products of their ordinary readouts give the necessary identity
\[
 I_L I_R=J_0 I_K .
\]
It is just equality of the two products with factors \(b_9^2 p_9 r_9 (L_\zeta)_9(R_\zeta)_9\), without any nonzero or sign requirement on these individual measurements. The adjacent shared Lean gate checks this scalar step. The common mixed model payment comes from the ordinary forward order and reverse grade-five pure annihilator, not the missing reverse grade-five square.

## 2. Four homogeneous quadratic profile marks

Use the edge note's measured two-coefficient profile, with the same polynomial basis \(A,B\); normalize a live scale so \(K=A+tB\). There are four quadratic-in-\(t\) necessary polynomials, with coefficients rational polynomial in \(a,d\):
\[
\begin{split}
 E_0&=m_0m_2-m_1^2,\qquad E_1=m_0m_3-m_1m_2,\\
 E_2&=\mathcal C(A+tB)/(a(d-1)),\\
 E_3&=I_L I_R-J_0 I_K .
\end{split}
\]
The two moments are paid by the literal \(0\le j\le3\) rank-one read of the dormant coordinate. The \(\mathcal C\) contact comes from the actual off-diagonal inverse Gram of both boundaries, and its indicated division is exact in the polynomial coefficient ring for the basis \(A,B\). All gauge factors are live. The center mark is homogeneous of degree two in the coefficients of \(K\), by the linearity of \(I_L,I_R\) and quadraticity of \(I_K\).

Take \(S\) to be the pair-resultant of \(E_0,E_1\), and take \(M_0,M_1,M_2,M_3\) to be the four maximal minors of the matrix of their coefficient rows \(E_0,E_1,E_2,E_3\) in \(1,t,t^2\), with row subsets in lexicographic order. These vanish at an actual common root without needing any leading profile coefficient nonzero. In particular the pair-resultant for rows \((A,B,C),(D,E,F)\) is \((AF-CD)^2-(AE-BD)(BF-CE)\), an identity valid also when rows drop degree. The maximal minors vanish because \((1,t,t^2)\) is an actual nonzero null vector. Both steps have denominator-free Lean gates.

Remove only exact factors from the literal guard list
\[
 a,\ d-1,\ a-d,\ 2a-d-1,\ a-2d,\ a-d-1.
\]
All are live by the calibrated-row census. Call the same normalized marks \(S,M_j\). Their bidegrees in \(a,d\) are \((20,20)\) for \(S\) and \((16,16),(16,16),(17,17),(17,17)\) for the maximal minors. The exact \(d\)-resultants of \(S\) with \(M_0,M_1,M_2\) have degrees \(602,602,640\) in \(a\) and their gcd is \(H_9(a)^2\) up to a nonzero rational, for the monic irreducible polynomial \(H_9\) of degree nine computed by the replay. In this projection no finite-field factor is discarded and no leading-degree assumption is used to infer the necessary resultant zeros.

## 3. Degree-preserving residue lift

The degree-nine factor retains degree and remains irreducible modulo 61. Thus the algebraic width \(a\) is integral at a place over 61, and its residue belongs to \(\mathbb F_{61^9}\), up to Frobenius. The specialized reduction of \(S\) retains full degree 20 in \(d\), so an actual common root \(d\) is algebraic and integral. The five reduced marks \(S,M_0,\ldots,M_3\) have exactly a linear gcd in \(d\). The replay checks all calibration guards at that single reduced root. With that width substituted, the four reduced profile polynomials \(E_0,\ldots,E_3\) retain a full quadratic and have unit gcd. The quadratic earns algebraicity and integrality of any \(t\), so its existence would give a common reduced root, impossible.

This field-arithmetic proof concerns the algebraic coefficients of the exact projected equations, not naive reduction of an unknown tableau. The exact replay is standalone with python-flint. The shared Lean bundle in the edge packet checks the rank-one, shared-row, pair resultant and maximal minor scalar identities over a commutative ring; the native checks do not purport to formalize the full tableau ingress or the polynomial projection.

The [exact replay outputs and Lean receipts](erk11-ten-ten-active-audit/)
document the checks. The [portable scalar identities](../lean/RKCert/ReviewedNative/ERK11TenActiveMomentGate.lean)
pass on all four requested core Lean versions; the tableau exclusion is mathematical.
