# Actual native order-eight four-off localization and the missing payment

**Read scope.** Published checkout rk-publish-canonical-rk-nov25 and pinned through-order-20 audit only. This is a source-level proof of localization and a precise missing-payment reduction, not a checked contradiction. The four-off branch is separate from the census and one-off branch. All occurrences below refer to literal Fin 10 rows, not a merged tableau.

Let \(A\) be strict lower, \(\mathrm{HasOrder}\ 8\ A\ b\), \(c=\mathrm{nodes}\,A\), \(g=\mathrm{OneOff.g}\,A=A c-c^2/2\), \(E_j=\mathrm{treeSpace}\,A\,j\), \(F_j=\mathrm{zeroSpace}\,A\,j\). Write \(y=1-c\). Let \(J_k=\mathrm{reflectedStageRow}\,A\,b\,k\), so
\[
  J_k=(k+1)A^\mathsf{T}(b\,y^k)-b\,y^{k+1}.
\]
The physical output and products are coordinatewise. There are four distinct off clocks and five distinct clean clocks (the census conclusion). Tags keep a clean and an off row at the same clock separate.

## Public interfaces and budgets

* ERKEvenHorizon.erk_even_horizon_of_stage_cap at \(q=4\) gives \(\dim F_4=3,\dim E_4=8,J_0=0\), exact flags of ranks 1 and 2, \(\mathrm{back}(2)=E_4^\perp\), and the last physical coordinate at clock one, live and in \(E_4\). These are in RKResearch.Certified.Graded.Reverse.
* Native erk_paid_rank_interval at \(1\to3\) and \(3\to4\), and explicit_midpoint_rank_eq, give \(\dim F_3=2,\dim E_3=6\). MultiOff.two_curve_head gives \(F_3=g\,\mathbb P_1(c), F_4=g\,\mathbb P_2(c)\) and \(g=P(c)\ne0\) on off tags, with \(\deg P\le2\).
* offMass_zero_of_head cancels the **aggregate** off weight at every off tag, using \(4+2\le8\). onOffSpace_le_E5 and onOffSpace_rank give the nine-dimensional tagged value space \(W\subset E_5\). Native Reverse.backward_count with \(j=5,n=1\) caps \(\dim E_5\le9\). Thus \(E_5=W\). This is constancy of actual grade-five columns on tags, not literal row equality.
* reflectedStageRow_annih at \(p=8\) places \(J_1\) in \(E_5^\perp\), \(J_2\) in \(E_4^\perp\), and \(J_3\) in \(E_3^\perp\), **not** \(J_3\) in \(E_4^\perp\).
* Terminal coordinate membership in \(W\), its nonzero weight and aggregate off cancellation imply terminal clean using MultiOff.on_of_state_single. The terminal clean tag \(1\) has no other physical copy, since its coordinate is in \(W\). Row \(0\) is clean at clock zero by the native zero_mem_cleanKnots proof. With these endpoints, the public mathematical order8_nodal_lobatto calculation uses only paid probes \(k=0,1,2\) of the degree-five clean hull and identifies it as \(H_C=X(X-1)L_3\), where \(L_3=X^3-\tfrac32 X^2+\tfrac9{14}X-\tfrac1{14}\). The published p8 Lobatto proof uses legacy vector names; its native port is the scalar/hull bridge. The **localization below does not need** the coefficient formula for \(L_3\), only the five distinct clean clocks and the endpoints.

Every clean aggregate \(W(a)\) is nonzero. Otherwise the contributing clean rule would have at most four clocks including 1. If \(D\) is the hull of its at most three other clocks, \((1-X)D^2\) vanishes on the contributing rule and has degree at most 7, but has strictly positive formal integral over \([0,1]\). This is the reflected case of the public RKCert.Endpoint.primitive_x_cubic_square_pos applied to \(D(1-X)\) at 1. It uses exactness and no positivity hypothesis on \(b\).

## Actual repeated tag and its location

The map from 10 physical indices onto the nine tags has exactly one two-element fiber \(\{i,j\}\), \(i<j\), and all other fibers are singletons, by summing fiber sizes. Consequently
\[
     E_5^\perp=K r,\qquad r=e_j-e_i.
\]
Because \(J_0=0\), \(\mathrm{back}(1)=KJ_1\) has rank one, giving \(J_1=\rho r\) with \(\rho\ne0\). The two rows have the same clock, so reflected-clock multiplication preserves \(Kr\). Exact rank two then gives
\[
     E_4^\perp=Kr+K\delta,\qquad \delta=A^\mathsf T r,
     \qquad \delta\notin Kr .
\]
For each tag, sum the corresponding physical entries of \(\delta\). This vector on tags is nonzero, since a zero aggregate would put \(\delta\) in \(E_5^\perp\). Its four off aggregates annihilate \(g,cg,c^2g\); by the \(3\times4\) Vandermonde and \(P(o)\ne0\), either they are all zero or all nonzero. The all-zero case would also kill every clean aggregate by interpolating on the five clean clocks with the degree-four pure columns of \(E_4\). Thus every off aggregate is nonzero. Since \(\delta_k=A_{jk}-A_{ik}=0\) at \(k\ge j\), every off tag has a physical representative strictly before \(j\).

The literal formula \(J_1(k)=2\sum_{l>k}A_{lk}b_l y_l-b_k y_k^2\) shows its latest nonzero index is the last index with \(b_k y_k\ne0\). Such an index exists by the paid reflected first moment. As \(J_1=\rho r\), that index is \(j\). After \(j\) no off tag can occur (it already has a representative before \(j\), and the only repeated pair is \(\{i,j\}\)). A clean singleton after \(j\) has nonzero \(b\); it must have \(y=0\), hence is the unique terminal row. This proves \(j=8\) and \(b_8y_8\ne0\).

### The last two distinct nonterminal clean rows

Put \(\eta=y_8\ne0\), so \(J_1=-b_8\eta^2 r\). By the paid \(J_2\in E_4^\perp\) and its value at 8,
\[
             J_2-\eta J_1=\xi\delta
\]
for a scalar \(\xi\). If row 7 were off singleton, \(b_7=J_1(7)=0\) would force \(A_{8,7}=0\). If row 7 were the earlier duplicated off, \(b_7=-b_8\) and \(J_1(7)=b_8\eta^2\) again force \(A_{8,7}=0\). Both violate its nonzero projected off coefficient. Thus row 7 is clean.

If row 7 is a clean singleton at \(z=y_7\ne0\), the literal \(J_1,J_2\) at row 7 give \(A_{8,7}=b_7 z^2/(2b_8\eta)\ne0\) and \(\xi=b_8\eta(3\eta-2z)\). If row 6 were off, then it is either a singleton or the earlier repeated off with \(b_6=-b_8\); in both cases the output-weight terms cancel in the two equations
\[
 b_8\eta A_{8,6}+b_7z A_{7,6}=0,\qquad
 3b_8\eta^2 A_{8,6}+3b_7z^2 A_{7,6}=\xi A_{8,6}.
\]
Eliminating \(A_{7,6}\) yields \(-b_8\eta z A_{8,6}=0\), contradicting its projected off coefficient. If instead row 7 itself is the earlier repeated clean, \(W(c_7)=b_7+b_8\ne0\) and the two row-7 equations give \(\xi=b_8\eta^2\ne0\). An off row 6 would then be singleton, and \(J_1(6)=0\) forces the sum of its two later nonterminal taps at the common reflected clock \(\eta\) to vanish (with their weights). Thus \(J_2(6)=0\) and \(\xi\delta_6=0\), again impossible. Hence rows 6, 7 and 9 are clean.

Rows 0 through 5 now consist of zero, four distinct off tags, and the first nonzero clean clock \(h\). The index of \(h\) is 4 or 5: at a clean row \(A g=A(cg)=0\) and \(A c=c^2/2\); with at most two preceding distinct off clocks the two defect tests force all those aggregated taps zero, while every earlier clean clock is zero. The conclusion would be \(c=0\). If \(h\) occurs at 4, the extra equality \(A(c^2g)=0\) there would likewise force its three preceding off taps zero via the \(3\times3\) Vandermonde, which is impossible. If \(h\) occurs at 5, all four off sources are already available and that argument no longer applies.

## The static grade-five reduction does not pay the missing row

The \(E_5=W\) representation by \(Q(c)+gR(c)\) with \(\deg Q\le5,\deg R\le3\) has exactly one relation: \(Q=H_C\) and \(R\) the interpolation of \(-H_C(o)/P(o)\) at the off clocks. One can always lower \(Q\) to degree four. This does not remove a quartic clean defect.

Indeed the terminal coordinate in \(E_4\) gives the particular column
\[
     Q(c)+gR(c)=Q(1)e_9,\qquad Q=X L_3,\qquad \deg R\le2 .
\]
Here \(Q\) is forced by its four nonterminal clean zeros and leading normalization. Strictness kills \(A e_9\), so at every clean row the preceding identity gives
\[
   (\mathrm{primitive}\ Q)(c)+\mathrm{mDef}\,A\,4+R_2\,A(c^2g)=0 .
\]
All \(F_5\) columns are constant on tags and vanish at the initial row. Cancelling off masses and using the paid bush probes \(k=0,1,2\), their clean restrictions form at most a single line: the four nonzero clean values, weighted by the nonzero \(W(a)\), annihilate \(1,a,a^2\). The displayed relation shows that this line is nonzero, and spanned by the clean profile of \(\mathrm{primitive}\ Q\) (its value at 1 is \(1/280\ne0\)). Its interpolation through the five clean clocks is
\[
        \mathrm{primitive}\ Q-H_C/5,
\]
whose quartic coefficient is \(1/8\). Thus the ordinary one-relation reduction lowers the polynomial part only to degree four. It equates one combination of \(\mathrm{mDef}\,A\,4\) and \(A(c^2g)\) to a nonzero profile, and does not kill the latter component.

As a sanity check, the late scalar tap does not provide a contradiction. Put \(x=c_6,z=c_7\). Solving the same reverse row equations at 6 and 7 gives \(A_{7,6}=(z-x) W(x)(1-x)^2/[W(z)(1-z)^2]\), using the aggregate masses when \(i=6\) or \(7\). A nonzero \(E_4\) column zero before row 6 and at 9 exists by dimension, and its clean integrated profile has double roots at \(0,h\) and a root at \(x\). Thus that profile is proportional to \(X^2(X-h)^2(X-x)\), giving \(A_{7,6}=(z-x)z^2(z-h)^2/[x^2(x-h)^2]\). These are compatible on the Lobatto three interior knots. Their weights are \(49/180,16/45,49/180\) on the two outer and middle nodes; multiplying a weight by the square of \(a(1-a)\) gives relative values \(1,4,1\), and the squared distances to the third node give exactly the balancing ratio. Neither equality pays the missing clean grade-five component.

## Exact missing physical lemma and its native consumer

The missing test is the actual terminal row identity
\[
                    \bigl(\mathrm{mat}\,A(c^2g)\bigr)_{\mathrm{Fin.last}\,9}=0.
\]
It would have to follow from actual order, strictness and the four-off branch, not be an assumption in the endpoint theorem. No such proof was located or derived here. Equivalently the missing scalar in the reverse argument is \(\mathrm{row}\ J_3\ (c^2g)=0\). For the equivalence, \(v=A(c^2g)\in F_5\) and is constant on tags; its weighted clean profile on the four nonzero clean nodes is in the one-dimensional kernel of \(1,c,c^2\). Thus either it is zero or every entry is nonzero. The fourth projected clean probe \(y^3\) kills it exactly when it is zero (Vandermonde). By the literal row pairing, \(\mathrm{row}\,J_3(c^2g)=4\sum_i b_i y_i^3 v_i\); the term without \(A\) cancels by off aggregates. This proves equivalence to the terminal test. For the first-clean index 4, a real proof of this test therefore needs an additional contradiction with that physical prefix, not a claimed extra stage-order condition.

The consumer is genuinely native. \(E_4=E_3+\mathrm{span}\{e_9,c^2g\}\): if a combination of the two were in \(E_3\), its degree-\(\le3\) pure profile would vanish at the four nonterminal clean clocks, so would be zero; the terminal evaluation kills the \(e_9\) coefficient, and four distinct off clocks force a quadratic to be affine only for the zero leading coefficient. The dimensions are 6 and 8. \(J_3\) already kills \(E_3\) by the order-eight budget, and its value at 9 is zero by strictness and \(y_9=0\). Precisely the proposed terminal test would put \(J_3\) in \(E_4^\perp\).

Then all reflected polynomial primitive defects of degree at most three would lie in \(Z=E_4^\perp\): use the public monomial expansion in OneOffTailClockRank.reverse_primitive_paid, with the cubic term supplied by this identity rather than an order-nine hypothesis. Take \(U=E_5^\perp\). The \(E_5=W\) clock invariance gives the reflected mask invariance of \(U\), and the native annihilating transpose transport gives \(A^\mathsf T U\subset Z\). The public two_failed_of_three_moments applies to actual reflected moments \(1/2,1/3,1/4\) and mass-zero \(U\). ordered_hermite_outgoing in reverse physical order with \(r=2\) would force \(\dim U+2\le\dim Z\), i.e. \(3\le2\).

The cubic slot cannot be borrowed from the published order-nine four-off consumer: its theorem pays \(4+3+2=9\). This note isolates one physical grade-five component remaining after valid order-eight payments. No checked Fin 10 contradiction, global floor of 11, or separate one-off result is claimed. No Lean, network, held data or checkout edit was used.
