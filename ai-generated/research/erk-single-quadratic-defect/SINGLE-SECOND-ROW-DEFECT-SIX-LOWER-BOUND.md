# Eleven rows are necessary for a dense size-six ERK chart with a single stage-order-two defect

Let \(A\) be strictly lower triangular with an exact dense derivative decoder through tree size six. Assume the defect \(\mathbf q\coloneqq A\mathbf c-\mathbf c^{\odot2}/2\) has just one nonzero component. Then there are at least **eleven stages**. This includes the standard practice of imposing the second simplifying condition at every stage except the second. The two eleven-row charts in this research use this practice, so the bound is sharp in this class. There is no non-existence claim here for width ten with multiple offending components.

We prove the result over a field with \(5!\) invertible. The same stage bound holds over any nonzero commutative paid base with one potentially offending physical row, by reducing to a residue field. The reduced field must still have a nonzero \(\mathbf q\), since its true clock vector has nonzero model and the first nonzero explicit clock has zero \(A\mathbf c\) entry.

## Hypothetical minimum width and its first four rows

Our earlier chronological argument gives at least ten rows and strict growth of pure rank from size three. If ten rows suffice, the dimensions of the pure spaces through sizes \(3,4,5,6\) must be exactly \(1,2,3,4\). Otherwise six independent model directions plus the pure space would not fit. Duplicate physical rows are inadmissible: physically identical predecessor rows have identical derivative coordinates at every rooted size, so merging one into the earlier row and adjusting later feeds and the decoder would give fewer than ten stages. Before the first nonzero clock all rows give the same origin profile, by strict induction on rows and the rooted recurrence. Thus only the origin can precede the one offending component at the second row. Scale clocks and coefficients by the same nonzero factor to make \(c_2=1\). This preserves all pure identities and the dense property, by the homogeneity of each rooted column.

Define
\[
 \mathbf f\coloneqq A\mathbf e_2,qquad
 \mathbf u\coloneqq A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3,qquad
 \mathbf v\coloneqq A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4 .
\]
Then \(\mathbf q=-\mathbf e_2/2\). The third clock \(N\) must be nonzero or its row would be zero. Since all later coordinates of \(\mathbf q\) are zero, \(f_3=N^2/2\). The rank-two pure space at size four is spanned by \(\mathbf q,\mathbf f\), so comparing rows 2 and 3 gives
\[
             \mathbf u=\tfrac23\mathbf q+k\mathbf f,qquad k\coloneqq1-\tfrac{2N}{3}.
\]
On the first three donor rows, \(\mathbf c^{\odot2}-N\mathbf c=(1-N)\mathbf e_2\). Therefore the fourth clock \(T\) has
\[
    f_4=\frac{T^2(3N-2T)}{2N},\qquad
    A_{43}=\frac{T^2(T-N)}{N^2}.
\tag{1}
\]
The cases \(T=0,N\) respectively duplicate the origin or the third row, so \(T\) is nonzero and differs from \(N\). Neither \(N=1\) nor \(T=1\) is excluded.

## Case 1: the fourth row reads the second coordinate

Suppose \(D\coloneqq3N-2T\ne0\). The pure size-five space is spanned by \(\mathbf q,\mathbf f,C\mathbf f\) (their restrictions to the first four rows are independent). Comparing there gives
\[
 \begin{aligned}
 A\mathbf f&=\alpha(C-NI)\mathbf f, &\alpha&\coloneqq N/D,\\
 \mathbf v&=\tfrac12\mathbf q+
       [1-N^2/2+\theta(C-NI)]\mathbf f,
 &\theta&\coloneqq -\alpha(T-N)/2.
 \end{aligned}
\tag{2}
\]
For the second line, on the first three donor coordinates the identity \(\mathbf c^{\odot3}=(1+N)\mathbf c^{\odot2}-N\mathbf c\) holds. At a row with this donor set and clock \(Y\), use (1) with \(Y\) instead of \(T\). The resulting ratio of the cubic defect to \(f_i\) differs from its value \(1-N^2/2\) at \(N\) by \(-N(Y-N)^2/(2(3N-2Y))\). Evaluating at \(T\) gives the stated slope. The first line follows because \((A\mathbf f)_3=0\) and \((A\mathbf f)_4=f_3A_{43}\).

Let \(X\) be the fifth clock and let \(f\) be its coefficient on column 2. On the first four donor coordinates there are two direct identities,
\[
 \begin{aligned}
 \mathbf c^{\odot3}&=(N+T)\mathbf c^{\odot2}-NT\mathbf c
                              +(1-N)(1-T)\mathbf e_2,\\
 \mathbf f&=T\mathbf c+U\mathbf c^{\odot2}-(T+U)\mathbf e_2,qquad
 U\coloneqq\frac{N-2T}{2N}.
 \end{aligned}
\]
Both remain valid with repeated clocks among the donor labels. Using (2), \(A\mathbf c=X^2/2\) at this new row, and its quadratic relation, these become
\[
 \begin{aligned}
 [B-\theta(X-N)]f&=X^2G(X),&
 B&\coloneqq N(2T-N)/6,\
 [\alpha(X-N)+(N+T)/3]f&=X^2J(X),\
 G(X)&\coloneqq X^2/4-(N+T)X/3+NT/2,&
 J(X)&\coloneqq T/2+(N-2T)X/(6N).
 \end{aligned}
\tag{3}
\]
For nonzero \(X\) eliminate \(f\). The resulting polynomial
\[
   [B-\theta(X-N)]J(X)-[\alpha(X-N)+(N+T)/3]G(X)
          =-\tfrac\alpha4(X-N)(X-T)^2 .
\]
Indeed it has leading coefficient \(-\alpha/4\), known roots \(N,T\) from the already existing rows, and its next coefficient divided by \(\alpha/4\) is \(N+2T\), by substitution of \(\theta,\alpha\). This proves the factorization even in the repeated-label branches.

At \(X=0\) at least one coefficient of \(f\) in (3) is nonzero: the two are \(NT(5N-4T)/(6D)\) and \(T(N-2T)/(3D)\). Thus \(f=0\), and its first two primitive moments give zero reads from the rows at \(N,T\); the fifth row is the origin. At \(X=N\), the two coefficients \(B,(N+T)/3\) cannot both vanish. Therefore \(f=f_3\). Once \(f\) is fixed, the two moment equations in \(N,T\) uniquely determine the third and fourth predecessor coefficients, followed by the row sum; the fifth row duplicates the third. At \(X=T\) the respective coefficients are \(NT(2N-T)/(6D)\) and \(2T(2N-T)/(3D)\), giving a duplicate of row four unless \(T=2N\).

It remains to allow \(T=2N\) and \(X=T\) with \(f\ne f_4=-2N^2\). Now the fifth predecessor coefficient on row 4 is \((f+2N^2)/(6N)\), by the first two moments. The pure size-six vector \(A(C-NI)\mathbf f\) is zero at rows 1–4 and nonzero at row 5. Thus it joins the existing three directions to give a basis of the entire pure space through size six. The pure vector \((C-NI)(C-TI)\mathbf f\) is zero at all five rows and hence zero everywhere, since these five coordinates distinguish the four basis vectors. It follows that \(\mathbf f\) is supported solely at clocks \(N,T\).

Consider the first later clock outside \(\{0,N,T\}\), if any, disregarding row 2. Its \(f\) equals zero, so it does not read row 2. Its remaining predecessors have labels in \(\{0,N,T\}\). Its first three primitive moments are all exact, by \(\mathbf q,\mathbf u,\mathbf v\) and (2). Their donor hull gives
\[
 A\mathbf c^{\odot3}-X^4/4
       =(N+T)X^3/3-NTX^2/2-X^4/4
       =-X^2(X-T)^2/4,
]
because \(T=2N\). Zero is impossible at a nonzero new clock different from \(T\). Thus every physical clock is in \(\{0,1,N,T\}\). A dense size-six decoder requires six distinct clock labels, since the first six clock powers must map to six independent monomials. This is a contradiction.

## Case 2: the fourth row does not read the second coordinate

Now \(T=3N/2\), and \(\mathbf g\coloneqq A\mathbf f\) is zero through row 3 but has \(g_4=T^2N/4\ne0\). The size-five pure space is spanned by \(\mathbf q,\mathbf f,\mathbf g\). Since \((C-NI)\mathbf f\) vanishes through row 4 it vanishes everywhere. The cubic defect in this case is
\[
   \mathbf v=\tfrac12\mathbf q+(1-N^2/2)\mathbf f-(N/4)\mathbf g .
\]
The coefficients follow on rows 2–4; at row 4 its cubic moment minus \(T^4/4\) is \(-T^2N^2/16\).

At a fifth clock \(X\ne N\), the second-coordinate coefficient is zero. Using the remaining labels \(0,N,T\) and its exact first two moments gives \(g=X^2(T/2-X/3)\). Its cubic defect must be \(-Ng/4\), which reduces to \(-X^2(X-T)^2/4=0\) because \(T=3N/2\). Both possible clocks give a duplicate row, from the first two moments and row sum. At \(X=N\), write \(f,g\) for the row's two scalar values. Its first two moments and its cubic condition, using the cubic donor identity of Case 1, give respectively
\[
          \tfrac{5N}{6}f+g=\tfrac{5N^3}{12},\qquad
          \tfrac{N^2}{3}f+\tfrac N4 g=\tfrac{N^4}{6}.
\]
Eliminating \(f\) gives \(-3Ng/20=0\), hence \(g=0,f=N^2/2\). Its third predecessor coefficient is then zero (\(f_3\ne0\)), and its other moments make it a literal duplicate of row 3. This exhausts the second case and proves the claimed sharp lower bound.
