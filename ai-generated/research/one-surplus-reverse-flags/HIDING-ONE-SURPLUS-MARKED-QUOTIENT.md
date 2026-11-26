# Passing ordinary defects through one reverse surplus

Keep the hypotheses of ONE-SURPLUS-CHARACTERS.md. In this note the actual reverse vector spaces have the genuine one-mark pairing through ordinary order \(p\). In particular the sum of a marked vector with model \(f\) equals \(I(f)\) whenever its witness is paid, and the sum kills true zero-density vectors. Multiplication of one marked vector by one genuine ordinary feature adds their costs and is allowed. No product of two marked vectors is used. Assume \(H\le p-1\). If the terminal-zero subflag is used, the masked output product and the scalar primitive discrepancies below must belong to that subflag; the products with the old marked head and core inherit their terminal zero.

Let the early unit band start at grade \(a\), with \(r\) initial old head powers, and let its single double step land at \(t\), with a subsequent late unit band through \(H\). Assume the actual old head and core meet the late head and core as above:
\[
 \mathbf g=\mathbf wL(Y)+\mathbf e,qquad
 U_-\subset U,qquad
 \delta\coloneqq\dim U-\dim U_-\in\{0,1\},qquad
 0\ne L\in\mathcal P_{1-\delta}.
]
When \(\delta=0\), \(\mathbf e\) can be taken zero. When \(\delta=1\), it may be supported at the single added core clock \(\alpha\), and \(L\) is constant. The heads and cores must be genuine at their respective starting grades.

Fix a genuine ordinary defect space \(F_q\) of grade at most \(q\), reversed into the same physical coordinates, and suppose \(a+q\le H\). There is one common clock polynomial \(B\) of degree at most one, a choice of late head representative, and a linear map \(f\mapsto P_f\) such that
\[
  f_*\coloneqq B(Y)f,qquad
  \deg P_f\le q+1,qquad
  (f_*)_i=P_f(y_i)\quad\text{on }\operatorname{supp}\mathbf w,
\tag{7}
\]
for every \(f\in F_q\). Also each \(\operatorname{diag}(f_*)\) preserves \(U\). The mask may be taken as \(B=L\) if \(\delta=0\), and \(B=L(X-\alpha)\) if \(\delta=1\). In particular it is a nonzero scalar in the leading-coefficient surplus case.

## Why the fit has only one extra degree

For a clock-local member of \(U_-\), its product by \(f\) lies in \(M_{a+q}\). A vector supported on one clock in the ending noninvariant band has no head part, by the distinct-label count; before the double step the same assertion holds in the old band. Hence the product belongs to \(U\). Off the possible added core clock, \(U_-\) and \(U\) agree by clock fibres. This proves that the masked multipliers preserve \(U\) on all fibres. Choose a single complement to \(U\) in the joint physical blocks of \(Y\) and these masked multipliers for a basis of \(F_q\). In the \(\delta=0\) case one may use all original multipliers too, since they already preserve \(U\). Subtract the old invariant component of \(\mathbf g\), leaving \(\mathbf e\) only at \(\alpha\) when required. These choices are made for the whole space, not separately for each \(f\).

If \(a+q\ge t\), compare the late head coefficients of the \(r\) true products \(f\odot Y^i\mathbf g\), \(0\le i<r\), all paid through \(a+q\). Their initial degree allowance is \(r+q-\delta\). Two consecutive coefficients agree after multiplication by \(X\) on all effective late head labels, more than the maximum degree of their difference. Hence the first coefficient has degree at most \(q+1-\delta\). At an unaffected physical head coordinate this coefficient equals \(L(y_i)f_i\), by the joint complement and \(\mathbf g=\mathbf wL(Y)\) there. For \(\delta=0\) take it directly as \(P_f\); at a zero of \(L\) the original product also vanishes on that fibre. For \(\delta=1\), multiply the coefficient by \(X-\alpha\), which removes the exceptional fibre and uses just the one extra degree. This gives (7).

If \(a+q<t\), the same consecutive comparison in the old band fits \(f\) on the old head by an ordinary polynomial of degree at most \(q\). This fits the late head away from a zero of \(L\) and the added core clock because the heads are proportional there. The two possible exceptions cannot both occur: if a core clock is added, \(L\) is constant. Multiplication by \(B\) therefore gives (7) also in this case.

## A paid uniform hiding criterion

For each such \(f\), let \(e\) be a bound on \(\deg P_f\) and let \(d\) be a bound on the genuine grade of both \(P_f\) and \(f_*\) (for example \(d=q+1\)). If
\[
             H\ge \max(a+q,t+2,d+\max(3,e)+1),
             \qquad p\ge d+e+4 ,
\tag{8}
\]
then
\[
                 \mathbf w\odot f_*=0,qquad
                 \mathbf v\odot f_*\in U .
\tag{9}
\]
In particular the masked ordinary vector annihilates \(M_H\) under the actual row-column pairing, and its output masses pool to zero separately at each clock.

Here is the proof including the needed projection. Eliminate the earliest pivots of \(U\) within the fixed joint blocks, obtaining the projection \(\pi\) and a zero-inserting section \(E\). The compressed \(N'=\pi NE\) is lower triangular, \(\pi\) commutes with clock and mask multiplications, and summation survives because \(U\) has zero density. Since \(U\subset M_t\), primitive comparison adds only vectors in \(\pi NU\subseteq\pi M_{t+1}\). The commutator comparison adds only vectors in the projection of \(NU+YNU+N^2U\subset M_{t+2}\), by expanding \(E\pi\) as the identity minus a projection into \(U\). These corrections and all projected pure spaces through \(H\) are supported on the projected head \(\pi\mathbf w\).

Consider the genuine contrast
\[
             \Theta\coloneqq
               \pi(\mathbf v\odot P_f(\mathbf y)-\mathbf v\odot f_*).
]
Its model is \(P_f\), through grade \(d\). It is zero on the support of the projected head: a joint block where the projected head is nonzero contains an original head coordinate, where \(f_*=P_f\) holds on the entire block. Off the projected head, \(\pi(\mathbf v\odot f_*)\) is zero by true membership in \(M_d\), so \(\Theta=(\pi\mathbf v)\odot P_f\) there.

If \(P_f\ne0\), the vectors \(Y'\Theta\) and \(Y'(Y'-uI)\Theta\) have first nonzero pivots at distinct nonzero clocks \(u,v\). Otherwise paid moments against all powers of degree at most \(e+1\) would make \((X-u)P_f\) zero by the \(X\)-weighted Gram. Their maximum total grade is \(d+e+3\), so the Gram is valid under (8). This argument also covers the possibility that the first vector is already zero.

At the two actual pivots all pure errors and projection corrections vanish, as their support is on the projected old head. The true commutator at a first pivot is minus the square of the physical projected diagonal times the pivot value. Its cost is at most \(d+4\), so both pivots are explicit by (8). With \(m\coloneqq\max(3,e)\), the strict primitive tests give
\[
 \int_0^u R(X)X P_f(X)\,dX=0\quad(\deg R\le m-1),\qquad
 \int_0^v R(X)X(X-u)P_f(X)\,dX=0\quad(\deg R\le m-2).
]
The largest grade in these tests is \(d+m+1\). Rescale \(u\) to one. The \(m\)-fold primitive of \(X P_f\) is divisible by \(X^{m+1}(X-1)^m\); since \(\deg P_f\le m\), its degree is at most \(2m+1\). After division by \((X-1)^{m-1}\), the second set of tests forces constant jets through order \(m-1\) at \(v/u\), by integration by parts. Its derivative is \(X^m\) times an affine polynomial; it cannot vanish to order at least two at a nonzero point unless it vanishes identically. This contradicts \(P_f\ne0\). Thus \(P_f=0\); (7) gives the head part of (9), and then \(\Theta=0\) gives its other part. Multiplication by \(f_*\) preserves \(U\) and annihilates the head, proving the final orthogonality.

The worst-case grade window is \(H\ge 2q+3\) (together with the fitting and projection windows). Because the model fit is linear on \(F_q\), the coefficient of degree \(q+1\) is a single scalar linear condition. On a subspace of codimension at most one, \(e\le q\). For \(q\ge3\) the primitive window then shortens to \(H\ge2q+2\) for a finite clock mask, or \(H\ge2q+1\) for a scalar mask, with \(d=q+1\) or \(q\) respectively. The finite mask can remove actual directions supported inside its one clock fibre; it cannot be assumed injective there. These are conditional budgeted conclusions, not exclusions of any particular stage count.
