# One strict matrix pays the exceptional prefix and the first three or four mixed lengths

This construction extends the [exceptional prefix](ODD-REALIZATION.md). It proves all rooted conditions through a smaller order while retaining the separately specified higher word contacts. The remaining target-order conditions are not proved.

## 1. Literal setup and notation

Let \(r=2n+1,\ m=r+1,\ p=m+r\), and \(d=L(r)=(n+1)^2\). Keep the repaired zero-weight early bank with its genuine negative anchors \(\alpha,a\), common diagonal \(\gamma=-g<0\), and decoder \(D'\). Write
\[
 D(X)\coloneqq(X-\alpha)(X-a),\quad
 J\coloneqq I_0-\gamma I,\quad J^*\coloneqq I_1-\gamma I,\quad
 \ell\coloneqq\int_0^1,\quad z\coloneqq1-\gamma,\quad t(X)\coloneqq X-z.
\]
The fixed real-algebraic exceptional negative prefix has length \(j=n+2\). Its actual rows \(v,w\) are supported on the first \(j,j-1\) physical sites, respectively, \(v_j\ne0\), and its true formal model \(P\) is nonzero of degree at most \(r-2\). Their verified contacts are
\[
 vE(DR)=\ell(PDR)\quad(\deg R\le m-1),\qquad
 wE(DR)=\ell((J^*P)DR)\quad(\deg R\le m-2),
 \tag{1}
\]
where \(E\) is evaluation at all late clocks. These are inherited exact finite tests on actual rooted inputs. Keep the same scalar quadrature: pin the negative prefix and the last clock \(z\), and use the \(q=n^2+n-2\) interior sites from the orthogonal nodal-hull rule. Its precision is \(d+q-1\ge p-1\), all weights \(b_i\ne0\), and all sites avoid both anchors. Their order among the interior stages is free. Denote their true diagonal by \(C\); in row expressions write \(bt^k\) for the actual row \(b\,t(C)^k\). These notations are only for describing the linear solves.

We shall choose one strict lower \(T\) with
\[
 bT=-bt,\qquad bA_0(C)+bQ(C)T=v,\qquad vT=w,\qquad
 A_0\coloneqq P-J^*Q .                                        \tag{2}
\]
When \(\deg Q\le r-3\), the middle row exhibits \(v\) as an actual combination of words through length \(r-2\), with true model \(P\). The upper budget (1), including the mark \(v\,t(C)\), is then preserved.

## 2. Choose one higher pre-primitive polynomial and the first suffix sites

Take \(\deg Q=s\), with \(s=3\) for the length-three result (\(n\ge3\)), or \(s=4\) for the length-four result (\(n\ge4\)). The two last clocks \(z,y\) and a quadratic \(Q_0\) can satisfy
\[
 Q_0(z)=1,\quad (J^*Q_0)(z)=P(z),\quad
 (J^*Q_0)(y)-(z-y)Q_0(z)=P(y),\quad Q_0(y)\ne1.              \tag{3}
\]
Here \(y\) is an actual interior site chosen as in ODD-REALIZATION.md, by excluding at most \(2n-1\) choices. At these fixed \(z,y\), the two evaluation equations on the coefficients of \(t,t^2\) are invertible, with determinant \(g^2(z-y)((z-y)^2+2g(z-y)-2g^2)/6>0\). Thus choose a polynomial \(R_s=t^s+c_1t+c_2t^2\) with \(J^*R_s\) zero at both sites; also \(R_s(z)=0\). Set \(Q=Q_0+\eta R_s\) with a nonzero algebraic \(\eta\). Avoid the at most one extra value making \(Q(y)=1\) and the at most one making
\[
 \Delta(X)\coloneqq P(X)-J^*(Q-1)(X)
\]
identically zero; the latter is impossible at two distinct \(\eta\) because \(J^*R_s\ne0\). Then (3) holds for \(Q\), its degree is exactly \(s\), and \(\Delta\) is nonzero of degree at most \(2n-1\), with roots \(z,y\).

Describe the actual physical suffix in reverse order, \(c_0=z,c_1=y,c_2,c_3,\ldots\), so a column at \(c_k\) can only use taps from \(c_i\) with \(i<k\) among these sites. Choose an interior \(c_2\) distinct from \(y\) with \(\Delta(c_2)\ne0\) and the second divided difference \(Q[z,y,c_2]\ne0\). At most \(2n-3\) further interior roots come from \(\Delta\); the second divided difference in the last node has degree \(s-2\) with nonzero leading coefficient, so excludes at most \(s-2\) additional sites. There are enough of the \(q-1\) sites in both stated ranges. For \(s=4\) also choose a distinct interior \(c_3\) with \(Q[z,y,c_2,c_3]\ne0\): the third divided difference is a nonconstant affine function of its last node. For \(s=3\) any distinct interior \(c_3\) suffices. Complete the first five suffix sites with an arbitrary distinct interior \(c_4\), and, for \(s=4\), choose four more distinct interior suffix sites. These choices are available, and all lie beyond the support of \(v\).

## 3. Shared first five suffix columns and actual pivots

Name three actual responses to be prescribed:
\[
 q_1\coloneqq (bt)T,\qquad q_2\coloneqq (bt^2)T,\qquad
 u\coloneqq q_1T .
 \tag{4}
\]
Their true formal models are respectively \(J^*t,J^*(t^2),J^{*2}t\), of word lengths \(2,3,3\). Work initially on the suffix columns only. The equations \(bT=-bt\) and \(bQ(C)T=v-bA_0(C)\) have zero \(v\) there.

At \(c_0\) there are no taps, and \(A_0(z)=0\) by (3). At \(c_1=y\), the single tap from \(z\) is forced by \(bT=-bt\) and (3) makes it satisfy the \(bQ(C)\) equation too. Here \(q_1,q_2,u\) are zero in both columns. At \(c_2\), the \(b\) and \(bQ(C)\) equations have two independent inputs from \(z,y\). The resulting response is nonzero:
\[
 (q_1)_{c_2}=-\,t(y)b_{c_2}\Delta(c_2)/(Q(y)-1)\ne0 .
\]
Indeed subtract the \(b\) equation from the \(bQ(C)\) equation, using \(Q(z)=1\) and \(J^*1=-t\), and then multiply the resulting \(y\)-input by \(t(y)\). The \(q_2,u\) entries there are the induced literal responses.

At \(c_3\), the restrictions of \(b,bt,bQ(C)\) to \(z,y,c_2\) have rank three by the nonzero second divided difference. In addition to the two fixed equations choose the \(q_1\) entry freely, use these three actual taps, and take \(q_2,u\) entries to be the induced responses. At \(c_4\), the four input rows \(b,bt,bt^2,bQ(C)\) have rank four on \(z,y,c_2,c_3\). For \(s=3\) this is cubic interpolation, and for \(s=4\) it follows from the chosen third divided difference. Choose the \(q_1,q_2\) entries freely, solve the four actual equations, and take the induced \(u\) entry. Choose this \(q_1\) entry so that \(q_1\) is outside the span of those four input rows on the five suffix sites. Such a choice excludes exactly one value: the restriction to the preceding four sites has full rank and determines the new value of any linear combination. When \(s=4\), also make the degree-four interpolant of the normalized values \((q_1)_i/b_i\) on the first five suffix sites have nonzero leading coefficient. This excludes at most one more value, since the coefficient of the fifth cardinal polynomial is nonzero. All these choices can be made algebraically.

Consequently the five actual input rows
\[
                 b,\ bt,\ bt^2,\ bQ(C),\ q_1                 \tag{5}
\]
have full rank on the first five suffix sites. At every subsequent column with those five sites strictly later in physical chronology, the two fixed equations in (2) can be solved together with arbitrary desired \(q_1,q_2,u\) entries, by using those five literal taps. This holds irrespective of other already-chosen earlier row taps; their contributions are simply included on the right side. It is the measured linear solve, not a formal word-space construction.

## 4. Five pivots pay all length-three contacts when \(n\ge3\)

Use \(s=3\) and freeze the suffix just constructed. On the other \(d-5\) sites choose the remaining entries of \(q_1,q_2,u\) to pay their respective contact
\[
       aE(DR)=\ell(P_a DR),\qquad \deg R\le p-k-3,
 \tag{6}
\]
where \(k=2,3,3\) and \(P_a\) is the stated true model for each row in (4). These are independent ordinary evaluation-dual solves on distinct non-anchor sites, after subtracting the fixed suffix entries. Indeed the largest number of constraints is \(p-4=4n-1\), and \(d-5\ge4n-1\) for \(n\ge3\).

Before solving those columns, use the freedom in rows within the first \(d-5\) physical sites to set \(vT=w\). Choose the earlier rows arbitrarily, then use row \(j\) for the missing earlier taps in this equation; \(v_j\ne0\) and \(w\) has the shorter support. The five physical suffix rows contribute nothing to \(vT\). Each earlier column can now use the invertible system (5) for the two fixed and three prescribed responses, without changing any value in the frozen suffix. Thus (2), (4) and (6) hold on a single matrix.

The literal equality \(bT=-bt\) exhausts the extra words at length one. With pure marks and this equality, the only new primitive responses through length three are those in (4): for instance \(bTT=-q_1\), \(bTt(C)T=-q_2\) and \(bTTT=-u\). Marks merely multiply both the numerical test and the corresponding polynomial by \(t\), with one unit of budget. The scalar rule pays pure marks through the needed degrees. So every word through length three satisfies (6).

## 5. Nine pivots pay all length-four contacts when \(n\ge4\)

Use \(s=4\). This time continue the suffix first, naming \(a_i=(q_1)_i/b_i\), \(c_i'=(q_2)_i/b_i\), and \(e_i=u_i/b_i\) for its normalized row values. With the invertible five-tap system (5), their values on the four next distinct suffix sites are freely assignable jointly. In addition to the earlier four rows, both \(bt^3\) and \(q_1t(C)\) are then required for the next dictionary.

The five polynomial rows \(b,bt,bt^2,bt^3,bQ(C)\) span polynomial evaluation through degree four and have full rank on the first five suffix sites. Let \(\Pi_a,\Pi_{ta}\) interpolate \(a\) and \(ta\) through degree four on these five sites, in the \(t\)-coordinate. The coefficient \(\mu\) of \(t^4\) in \(\Pi_a\) is nonzero by the choice at \(c_4\). Thus
\[
 t\Pi_a(t)-\Pi_{ta}(t)=
          \mu\prod_{i=0}^{4}(t-t(c_i)).
 \tag{7}
\]
The two sides have the same leading coefficient and both vanish at the five interpolation sites. On the next four sites choose the residual \(a-\Pi_a\) nonzero at a single site and zero at the other three. Equation (7) implies that the residual \(ta-\Pi_{ta}\) is then independent of \(a-\Pi_a\): at the other three sites it is the nonzero five-node hull multiple. Choose the freely assignable \(c',e\) residuals after their degree-four interpolation on the first five to complete a basis of the four-dimensional space of residuals. All four choices are realized by the actual five physical taps in each of those four newly processed columns. In particular the following nine actual rows are independent on the full nine suffix sites:
\[
 b,\ bt,\ bt^2,\ bt^3,\ bQ(C),\ q_1,\ q_1t(C),\ q_2,\ u .     \tag{8}
\]
This proof of rank depends on the chronological measured values; it is not an assumed rank of formal model polynomials.

The four additional desired grade-four outputs are
\[
 (bt^3)T,\qquad (q_1t(C))T,\qquad q_2T,\qquad uT .
\]
Their grade-four models are \(J^*(t^3),J^*(tJ^*t),J^{*2}(t^2),J^{*3}t\). Freeze their actual values on the nine suffix columns just processed, as well as the earlier three outputs there. Then solve (6) for all seven response rows on the first \(d-9\) sites. This is possible since \(d-9\ge4n-1\) for \(n\ge4\); the strongest moment band is still the one for \(q_1\). Once the full desired rows are known, set the earlier physical taps as in Section 4 to retain \(vT=w\), and for each earlier column use the nine independent suffix inputs (8) to obtain all seven responses and both fixed equations of (2). The computed \(q_1,q_2,u\) rows agree literally with their defining actual products, so the last four equations are not circular. This pays every grade-four word: every grade-three input is a combination of \(b,bt,bt^2,bt^3,q_1,q_1t(C),q_2,u\); an appended primitive is on the list, and an appended mark reduces its test budget by one as before.

## 6. Genuine smaller order; why a low-degree representation can obstruct it

Attach the strict earlier feed \(EJD'-TED'\), exactly as in the sealed exceptional construction. The physical late clocks are then the stated sites and true local order through \(m\) holds. A tree of size at most \(m+l\), where \(l=3\) or \(4\), has at most one child of size at least \(m\). For that child the numerical correction from the actual earlier decoder has a polynomial source divisible by \(D\), and the source degree is at most one less than the child's size. Each step up that unique spine is a true strict primitive followed by the exact polynomial of the smaller children. Expanding these polynomial factors as marks gives contractions along words of length at most \(l\), with source grade at most \(m+l-k\le p-k\) at word length \(k\). Therefore (6) pays every such contraction. The pure polynomial part has degree at most one less than the tree's size and is integrated by the actual scalar rule. The shifted equations are equivalent to the ordinary rooted order conditions. Consequently these are real-algebraic strict SDIRK tableaux of order **at least \(m+3\) when \(n\ge3\)** and **at least \(m+4\) when \(n\ge4\)**, while keeping the separately paid high \(v,vT,vC\) channel at the full exceptional budget (1). Through order 20, this supplies order at least 11 in the \(p=15\) geometry and at least 14 in the \(p=19\) geometry. It does not pay the remaining high mixed words, and has no new unrestricted stage count.

The change from a quadratic to a higher \(Q\) is substantial, rather than cosmetic freedom in the same two taps. With the old \(\deg Q\le2\) representation in (2), if every word through length three were paid then \(bQ(C)T\) would have its true model against \(D\mathbb P_{\le p-6}\). The pinned scalar rule is precise enough for \(bA_0(C)\) on the same band (\(\deg A_0+\deg F\le p+r-6\)). It would follow that \(v\) itself paid the model \(P\) on this extended band. But for \(n\ge4\), the degree of the negative-prefix nodal hull \(H_j(X)=\prod_{i\le j}(X-x_i)\) times \(P\) is at most \(3n+1\le p-6\). Its \(D\)-multiple vanishes on the entire actual support of \(v\), whereas its formal moment is \(\ell(D H_j P^2)>0\), since every prefix clock is negative. This is an exact incompatibility between the old physical compressed representation and a full length-three lower dictionary. The cubic and quartic constructions move \(Q\) to a later true word grade and do not force this false stronger contact.
