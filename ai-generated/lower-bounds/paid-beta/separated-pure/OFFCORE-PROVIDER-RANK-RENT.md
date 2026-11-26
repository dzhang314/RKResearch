# Off-core providers shorten flat runs in the separated pure ranks

Let \(A\) be a strictly lower triangular tableau over a field. Degree means tree size minus one. For degree \(j\), let \(E_j\) be the actual numerical rooted span and \(F_j\) its zero-model pure subspace, and write \(f_j\coloneqq\dim F_j\). Assume model separation through every degree used. Thus
\[
            E_j=P_{\le j}(\mathbf c)\oplus F_j,\qquad
            \mathbf c\coloneqq A\mathbf1,\quad
            C\coloneqq\operatorname{diag}(\mathbf c).
\]
Here \(P_{\le j}(\mathbf c)\) is the literal polynomial clock span of dimension \(j+1\). Unary extension applies \(A\) numerically and the primitive \(J\) from zero on the exact polynomial. Clock multiplication is \(C\) and corresponds to multiplication by \(X\). Root sum gives coordinatewise multiplication. A sufficient common coefficient hypothesis for a final degree horizon \(D\) is that \((2D+1)!\ne0\); the proof uses no signs. No global ordinary or weighted output is assumed.

**Flat-run theorem.** Suppose \(a\ge b+2,\ b\ge2,\ f_a\ge a+h\), and \(h<\lceil(a+b)/2\rceil-3\). Let \(L_{b-1}\) be any valid lower bound on \(f_{b-1}\) under separation. If
\[
              L_{b-1}+\lfloor b/2\rfloor
                            >\lceil(a+1)/2\rceil+h,                \tag{1}
\]
then
\[
                               f_{a+b}\ge a+b+h+1 .               \tag{2}
\]
The new ingredient is a rank count on the incoming feeds of actual clean stages outside a measured core. The size of an ordinary preceding provider gives a related, independent check.

## The clean rows and their physical feed rank

Suppose a numerical subspace \(U\) contains \(F_b\) and is invariant under \(C\) and multiplication by each member of \(F_b\). Define \(S\) to be the union of the physical supports of \(F_b\), and let \(U_S\) be the image of \(U\) under the coordinate projection onto \(S\), padded by zero elsewhere. Put \(u_S\coloneqq\dim U_S\).

The indicator vector of \(S\) belongs to \(U_S\). Indeed choose a basis \(\mathbf f\) of \(F_b\), and for each basis member choose a scalar polynomial whose value is zero at zero and one at every nonzero actual value of that member. If the polynomial is \(XQ(X)\), its evaluation on the member is \(Q(\operatorname{diag}(\mathbf f))\mathbf f\in U\), and multiplication by that vector also preserves \(U\). Thus the indicator of each basis support is in \(U\) and preserves \(U\) by multiplication. Iterating the identity
\(\mathbf1_{S_1\cup S_2}=\mathbf1_{S_1}+\mathbf1_{S_2}-\mathbf1_{S_1}\odot\mathbf1_{S_2}\)
gives the assertion for \(S\). In particular the projection onto \(S\) preserves \(U\), and applying any polynomial in \(C\) to \(\mathbf1_S\) shows
\[
          P(\mathbf c)\big|_S\in U_S
          \quad\hbox{with zero elsewhere}
\]
for every scalar polynomial \(P\). Also \(F_{b-1}\subseteq F_b\subseteq U_S\).

For a physical stage \(i\notin S\), every coordinate in \(F_b\) is zero there. It follows from the genuine primitive errors through degree \(b\) that
\[
          (AP(\mathbf c))_i=(JP)(c_i)
                        \qquad(\deg P\le b-1).
\]
The incoming row at \(i\), restricted to \(U_S\), annihilates \(F_{b-1}\), since \(AF_{b-1}\subseteq F_b\). Thus its possible scalar feeds on polynomial data supported in \(S\) all belong to one fixed row subspace \(\mathcal M\) of dimension at most
\[
                              q\coloneqq u_S-f_{b-1}.              \tag{3}
\]
Here \(\mathcal M\) is the image of that annihilator under substitution of the actual vectors \(P(C)\mathbf1_S\), in the dual of the scalar polynomials \(P_{\le b-1}\). The contribution from earlier rows outside \(S\) is a linear combination of evaluations at their earlier clock labels.

If \(b\ge2q+2\), there can be at most \(q\) distinct nonzero clock labels outside \(S\). Otherwise, let \(x_1,\ldots,x_{q+1}\) be the first such distinct labels in their physical order. For each \(x_i\), the exact primitive functional \(J_{x_i}:P\mapsto\int_0^{x_i}P\) is in \(\mathcal M\) plus the evaluations at \(0,x_1,\ldots,x_{i-1}\). Restrict them all to the scalar polynomials with zero values at \(0,x_1,\ldots,x_q\). These \(q+1\) primitives would have rank at most \(q\). They in fact are independent: for any values prescribed at \(x_1,\ldots,x_{q+1}\), choose a polynomial \(G\) of degree at most \(2q+2\) with those values, \(G(0)=0\), and \(G'\) zero at \(0,x_1,\ldots,x_q\). The linear conditions are invertible because their homogeneous kernel would have \(2q+3\) roots counted with multiplicity in degree at most \(2q+2\). Then \(P=G'\) is in the indicated restricted domain, since \(\deg P\le 2q+1\le b-1\), and its primitives have the prescribed values. This proves the required independence.

At degree \(b\), the rows on \(S\) have rank at most \(u_S\), since both clock polynomials and all \(F_b\) data there belong to \(U_S\). Outside \(S\), every rooted profile is simply its model evaluated at the clock; if \(b\ge2q+2\) the rank there is at most \(q+1\), including clock zero. It follows that
\[
               b+1+f_b=\dim E_b\le u_S+q+1=f_{b-1}+2q+1 .
\]
If \(q<\lfloor b/2\rfloor\), then \(b\ge2q+2\), and the displayed inequality contradicts strict growth of the separated pure space. Therefore the required incoming rank is
\[
                         \boxed{u_S\ge f_{b-1}+\lfloor b/2\rfloor.} \tag{4}
\]
This uses only physical support, genuine primitive errors, and model separation. It does not assume invariance of the full \(F_b\) under \(A\).

There is also a direct chronological width bound. If a nonzero actual clock occurs outside \(S\), let \(x\) be the first such clock and \(i\) its row. The preceding row \(A_i\) integrates profiles from \(E_{b-1}\) up to \(x\). On previous \(S\)-rows these profiles span at most \(u_S\) coordinate dimensions; outside \(S\) all previous profiles are exact evaluations at the single clock zero. Hence the actual rank of preceding \(E_{b-1}\) evaluations is at most \(u_S+1\). Chronological compression retains independent evaluations on that prefix and redirects each omitted coordinate only to earlier retained ones, preserving all rooted profiles through degree \(b-1\) and this last incoming row. Rescale the preceding matrix and that output row by \(1/x\). For a tree of size \(n\le b\), the unscaled factor \(x^n/t!\) and the homogeneity \(x^{-(n-1)}\) give exact ordinary order \(b\) after rescaling. Thus any valid ordinary order-\(b\) stage lower bound is at most \(u_S+1\). This is an actual width comparison, not a model rank treated as a physical method without the compression step.

## Applying the earlier Gram exit to the measured flat flag

Suppose the conclusion (2) fails. Strict separated growth implies \(f_a=a+h\) and every one of the next \(b\) gains is one. The previous Hermite rents from 02-PAID-DOUBLING-SURPLUS.md give, for any invariant \(U\subseteq F_j\),
\[
 f_{j+1}\ge \dim U+\lfloor(j+1)/2\rfloor,\qquad
  F_j\text{ invariant at }j\ge5\ \Longrightarrow\
    f_j\ge\lceil3j/2\rceil-3 .
\]
Thus every intermediate \(F_{a+i}\) is noninvariant, as is the endpoint by the hypothesis on \(h\). The numerical codimension-one clock-escape argument gives a common invariant core \(U\) and one head, with the actual \(C\) powers supplying each next grade. In particular the first rent gives
\[
                         u\coloneqq\dim U
                          \le\lceil(a+1)/2\rceil+h .               \tag{5}
\]
For each \(\mathbf f\in F_b\), the earlier chronological Gram exit applies at base grade \(a\) with length \(b\), source cost \(b\), and endpoint \(a+b\ge2b+2\). It proves both \(\mathbf f\in U\) and invariance of \(U\) under the actual multiplication by \(\mathbf f\). Its first genuine discrepancy row kills the entire head and the core, and its \(A\)-successor on the matched contrast gives the full weight-\(X\) Gram. No global output is used in that source proof. The necessary earlier certificates are CHRONOLOGICAL-GRAM-EXIT.md (manifest 8d77855e…) and 02-PAID-DOUBLING-SURPLUS.md (manifest 1e1de2dc…). Thus the preceding feed argument applies; (4) contradicts (5) and (1), proving (2).

An optional variant uses the ordinary width bound instead of (1). If \(a+b>u\) then some nonzero clock occurs off \(S\), since on \(S\) there are at most \(u_S\le u\) distinct clocks and separation through \(a+b\) needs at least \(a+b+1\) literal clocks. The direct provider comparison then gives any available order-\(b\) stage floor \(\le u_S+1\le\lceil(a+1)/2\rceil+h+1\). An independently stronger floor than that likewise eliminates the flat run.

## An iterated consequence better than doubling

For \(b\ge6\), the established dense base \(f_5\ge5\) and strict growth give \(L_{b-1}=b-1\). For integers \(a,h\) with \(a\ge\max(8,h+6)\), take
\[
 b(a,h)\coloneqq
      \max\!\left(6,\ \left\lceil
           \frac{2(\lceil(a+1)/2\rceil+h+2)}3
                           \right\rceil\right).
\]
Then \(b(a,h)\le a-2\) and \(\lfloor3b(a,h)/2\rfloor\ge\lceil(a+1)/2\rceil+h+2\), so (1) holds. The endpoint noninvariance condition also holds: \(b(a,h)\ge h+4\) under \(a\ge h+6\), hence \(a+b(a,h)\ge2h+7\). It follows that any separated floor \(f_a\ge a+h\) forces
\[
         f_{a+b(a,h)}\ge a+b(a,h)+h+1 .
\]
In particular, starting from the independently checked separated paid base \(f_9\ge10\), set \(a_1=9\) and \(a_{h+1}=a_h+b(a_h,h)\). Then \(f_{a_h}\ge a_h+h\); the first two new examples are \(f_{15}\ge17\) and \(f_{23}\ge26\). The characteristic-zero base \(f_8\ge9\) gives \(f_{14}\ge16\) by the same argument. These are pure-dimension statements on separated data, not assertions about any protected stage calculation or additional verified numerical table entry.

For the paid recurrence, \(b(a_h,h)\le a_h/3+2h/3+3\). Thus
\[
                 a_{h+1}+2(h+1)+15
                    \le\frac43(a_h+2h+15).
\]
Consequently \(a_h\le26(4/3)^{h-1}-2h-15\). This gives a logarithmic surplus with base \(4/3\), in place of the previous doubling schedule. One can use a stronger earlier bound on \(L_{b-1}\) in (1) to shorten a given step further; the displayed recurrence deliberately uses only the uniform base \(b-1\).

The Hermite threshold \(b\ge2q+2\) cannot itself be lowered using only the abstract incoming row-space model. At \(b=2q+1\), take \(\mathcal M\) to be the span of integrals up to any first \(q\) distinct nonzero clocks. These first \(q\) reads are available in order without any previous evaluations. Then \(\mathcal M\) together with evaluations at \(0\) and those clocks is the whole dual of \(P_{\le2q}\): independence follows from the confluent interpolation problem prescribing primitive values at those \(q\) nodes and derivatives there and at zero. Hence no later distinct clock is barred by that abstract feed rule. This does not construct a Runge–Kutta tableau or say that the rank bound is geometrically sharp for actual tableaux. It specifies why any further improvement must also use the genuine rooted feed structure, not merely the dimension of its scalar row space.
