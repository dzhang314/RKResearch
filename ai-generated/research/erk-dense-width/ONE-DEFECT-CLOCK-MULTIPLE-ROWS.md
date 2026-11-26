# One carrier clock, with any number of offending stages

We continue the assumption of ordinary accuracy or a dense decoder through size six and test whether \(\dim F_6=4\) is possible. Thus \(\dim F_j=j-2\) for \(3\le j\le6\), by the strict chronological pure-growth lemma. Suppose all nonzero entries of \(\mathbf q\) are at a single clock, but do not assume a single physical offending row.

Repeated histories through size six may be merged. Indeed, redirect every read of the later duplicate to its earlier row; through the cap, the rooted recurrence only uses already equal derivative data. Restriction of the stage columns then loses a numerically duplicated coordinate and preserves their ranks and pure subspaces. An ordinary output or the dense decoder can be adjusted along that same coordinate. In particular stages before the first nonzero clock all have the origin profile and may be merged. Normalize the first nonzero clock to 1 by scalar dilation, so \(q_2=-1/2\) and all carriers have clock 1. Dilation preserves all numerical zero relations and pure ranks. Scalar-moment contradictions below can always be taken in the original undilated coordinate.

Define
\[
 \mathbf f\coloneqq-2A\mathbf q,\qquad
 \mathbf u\coloneqq A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3,\qquad
 \mathbf v\coloneqq A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4,qquad
 \mathbf w\coloneqq \mathbf q\odot(\mathbf q+\mathbf1/2).
\]
The respective costs are four, four, five and five. The third clock \(N\) is nonzero, because a zero-clock non-carrier there would have zero coefficient on stage 2 and be the origin. Also \(f_3\ne0\) or the third row duplicates the origin or row 2. Thus \(F_4\) is spanned by \(\mathbf q,\mathbf f\), and
\[
                 \mathbf u=\tfrac23\mathbf q+k\mathbf f .
\]
If \(q_3=0\), comparison at row 3 gives \(f_3=N^2/2\) and \(k=1-2N/3\). If \(q_3\ne0\), then \(N=1\), \(f_3=q_3+1/2\), and \(k=1/3\).

For clarity, the scalar contradictions used repeatedly are the following. At most four distinct physical clocks are insufficient for dense size six, regardless of the defect modes. At most three effective ordinary clocks including zero cannot meet degree-five quadrature: their monic cubic hull, padded if necessary, has zero constant but orthogonality to \(1,X,X^2\) forces the paid shifted-Legendre cubic with constant \(-1/20\). The Gram calculation also excludes ordinary stages supported at only 0 and 1 (before normalization) or at only 0 and one scaled clock. Therefore there must be some nonzero phase beyond a list of at most three physical labels containing the origin.

## The third row is a second carrier with a different residual value

Here \(N=1,q_3\ne0\), and \(q_3\ne-1/2\) since \(f_3\ne0\). Let \(\theta\ne0,1\) be the first other nonzero clock. Before it, all positive clock powers on predecessors agree, so at any clock-one row \(f=q+1/2\), and at a zero-clock row \(f=q=0\). Thus \(\mathbf f=\mathbf q+\mathbf c/2\) on that prefix, and \(A\mathbf f=0\) there. At \(\theta\) the first two moment equations give
\[
       F\coloneqq f_\theta=\theta^2(3-2\theta)/2,qquad
       (A\mathbf f)_\theta=\theta^2(\theta-1)/2\ne0 .
\]
Both \(A\mathbf f\) and \(\mathbf w-q_3\mathbf f\) are pure through size five and zero through row 3. They must be dependent, since those first rows already distinguish two of the three pure directions. Consequently \(\mathbf w-q_3\mathbf f\) is zero before \(\theta\), forcing every earlier clock-one residual to be either \(-1/2\) or \(q_3\).

### The first other clock has \(F\ne0\)

Now \(F_5=\operatorname{span}(\mathbf q,\mathbf f,C\mathbf f)\). Reading at the first occurrence of \(\theta\) gives the identities
\[
\begin{aligned}
 \mathbf w&=q_3\frac{\theta-C}{\theta-1}\mathbf f,\
 A\mathbf f&=\alpha(C-I)\mathbf f,\
 \mathbf v&=\tfrac12\mathbf q+
           [\tfrac12+\nu(C-I)]\mathbf f,\\
 \alpha&\coloneqq(3-2\theta)^{-1},&\nu&\coloneqq-\tfrac12\alpha(\theta-1).
\end{aligned}
\]
For the cubic line, the coefficient of \(\mathbf f\) at 1 is \(1/2\), and at \(\theta\) it is \((2-\theta^2)/(2(3-2\theta))\); this gives the stated slope. In particular \(f=0\) away from \(1,\theta\). If \(\theta=2\), the first new off-label clock would have \(q=f=0\) with predecessors only at \(0,1,2\). Its exact moments through degree three require \(I_x[X(X-1)(X-2)]=x^2(x-2)^2/4=0\), impossible at a new label. So assume \(\theta\ne2\).

Consider the first proposed change to one of the lower profiles: a new clock, a new q-value at 1, or an f-value at \(\theta\) different from \(F\). On its predecessors,
\[
 \mathbf f=\mathbf q+\theta\mathbf c+\tfrac{1-2\theta}{2}\mathbf c^{\odot2},
 \qquad
 \mathbf c^{\odot3}=(1+\theta)\mathbf c^{\odot2}-\theta\mathbf c .
\]
The stated identities follow by evaluating at the already present profiles. At the proposed row with clock \(x\) and two values \(q,f\), substitute its first two moments into these identities and compare with \(A\mathbf f,\mathbf v\) above. This gives
\[
\begin{aligned}
 [B-\nu(x-1)] f &= x^2G(x)+Bq,& B&\coloneqq(2\theta-1)/6,\
 [\alpha(x-1)+(1+\theta)/3] f &=x^2J(x)+(1+\theta)q/3,\
 G(x)&\coloneqq x^2/4-(1+\theta)x/3+\theta/2,&
 J(x)&\coloneqq \theta/2+(1-2\theta)x/6 .
\end{aligned}
\]
For \(x\ne1\) we have \(q=0\), and the determinant of the two equations factors as \(-\alpha(x-1)(x-\theta)^2/4\), as in the single-row calculation (3) with \(N=1,T=\theta\). At \(x=\theta\) at least one coefficient is nonzero because \(\theta\ne2\), forcing \(f=F\). At \(x=1\) the equations give \(f=q+1/2\): the coefficients \(B,(1+\theta)/3\) cannot both vanish. Then \(\mathbf w=q_3\mathbf f\) at that clock forces \(q=-1/2\) or \(q=q_3\). A zero-clock non-carrier has \(f=q=0\). This excludes the first change, so all physical labels are among \(0,1,\theta\), a contradiction.

### The first other clock has \(F=0\)

Now \(\theta=3/2\), and with \(\mathbf g\coloneqq A\mathbf f\) the pure size-five space is spanned by \(\mathbf q,\mathbf f,\mathbf g\). The first independent readings through \(\theta\) give
\[
           (C-I)\mathbf f=0,qquad
           \mathbf w=q_3\mathbf f,qquad
           \mathbf v=\mathbf q/2+\mathbf f/2-\mathbf g/4 .
\]
At the first proposed new scalar clock or new q-value at 1, let \(M_1,M_\theta\) be the pooled incoming coefficients from those two old clocks. On the predecessors \(\mathbf f=\mathbf q+\mathbf c/2\) at clock 1 and both vanish off that clock. Hence \(M_1=2g+f\), using \(A\mathbf q=-\mathbf f/2\). If \(x\ne1\), then \(q=f=0\). The exact first two moments give \(g=x^2(\theta/2-x/3)\). The cubic clock hull and \(v=-g/4\) reduce to
\[
       -x^2(x-\theta)^2/4=0 ,
\]
so no new nonzero clock is possible. At \(x=1\) the first two moments instead give \(g=(5/6)(q+1/2-f)\). Inserting those moments in the cubic hull gives an actual cubic defect differing from \(q/2+f/2-g/4\) by \((f-q-1/2)/8\); thus \(f=q+1/2\). The relation \(w=q_3 f\) again permits only the two old q-values. This case also allows at most three scalar clocks, a contradiction.

## The third row is a non-carrier and the fourth introduces a new q-value

Now \(q_3=0\), \(f_3=N^2/2\), \(k=1-2N/3\). A fourth carrier having \(q=-1/2\) would duplicate row 2: its first moment is zero, and the first two moments then give \((1-N-k)f=-Nf/3=0\), so it reads neither row 2 nor row 3. Suppose instead that the fourth row has \(q_4\notin\{0,-1/2\}\), at clock 1. The first two moments give, with \(K\coloneqq3-2/N\),
[
              f_4=K(q_4+1/2),\qquad
              (A\mathbf f)_4=(1-N)(q_4+1/2).
\]
Consequently \(F_5=\operatorname{span}(\mathbf q,\mathbf f,\mathbf w)\), and comparison through row 4 yields
\[
         (C-NI)\mathbf f=(1-N)K\mathbf w/q_4,qquad
         A\mathbf f=(1-N)\mathbf w/q_4 .
\]
When \(N=1\), \(\mathbf f\) is supported at clock 1. The first scalar clock outside \(0,1\) would have \(q=f=w=0\), hence exact first three primitive moments on predecessors only at 0 and 1, incompatible as before. When \(N=2\), at the first proposed clock outside \(0,1,N\), one has \(q=f=w=0\) and the same double-root hull \(I_x[X(X-1)(X-2)]\) forbids it. When \(N=1/2\), the corresponding hull is \(x^2(x-1)^2/4\), again giving no new clock. We can therefore assume \(N\notin\{1,1/2,2\}\).

Up to the first possible clock outside \(0,1,N\), the value of \(f\) at every row at clock \(N\) is \(N^2/2\). Indeed its cubic defect, as a linear combination of the three basis vectors, is \((1-N^2/2)f\) at that clock, by comparison with row 3. Its first two moments and the donor cubic identity \(\mathbf c^{\odot3}=(1+N)\mathbf c^{\odot2}-N\mathbf c\) then give
\[
                    N(N-2)(N^2/12-f/6)=0 .
\]
There also cannot be a non-carrier at clock 1 before that proposed new clock: it has \(f=w=q=0\), and its exact cubic hull test is \(I_1[X(X-1)(X-N)]=(2N-1)/12\ne0\).

At a proposed new off-label clock \(x\), we have \(q=f=w=0\), and hence \(A\mathbf q=A\mathbf f=0\) there and the first three primitive moments are exact. The aggregate feed on the old clock \(N\) is related to \(A\mathbf w\), since \(f=K w/q_4\) at clock 1 and \(f=N^2/2\) at \(N\). For \(K=0\), its feed at \(N\) vanishes by \(A\mathbf f=0\), leaving only one nonzero clock, impossible for all three moments.

For \(K\ne0\), the size-six pure vector
\[
                    \mathbf R\coloneqq\mathbf q\odot\mathbf f-K\mathbf w
\]
is zero through the first four rows. If any carrier at clock 1 has acquired a q-value other than \(-1/2,q_4\), then \(\mathbf R\ne0\): there \(R=K w(q/q_4-1)\). The space of pure vectors through size six vanishing on the first four rows has dimension one, because the three earlier basis vectors are independent there. The size-six vector \(A\mathbf w\) also vanishes through those rows, so would be proportional to \(\mathbf R\). In that event \(A\mathbf w=0\) at the new off-label non-carrier, forcing its aggregate feed at \(N\) zero and again a contradiction.

Otherwise the preceding clock-one carriers have just the two q-values \(-1/2,q_4\). Their aggregate mass at this new row is \(2(A\mathbf w)_i/q_4\), using \((A\mathbf q)_i=0\) and the interpolation identity for the constant on those two values. The aggregate mass at \(N\) is \(-2K(A\mathbf w)_i/(N^2 q_4)\). Both feeds cannot vanish because the first moment is nonzero. The ratios of the second and third raw clock moments to the first therefore equal
\[
       \frac{1-K}{1-K/N}=\frac{2N}{2-N},\qquad
       \frac{1-NK}{1-K/N}=\frac{3N^2}{2-N}.
\]
But exact primitives give these ratios as \(2x/3,x^2/2\). Thus \(x=3N/(2-N)\) and \(x^2/2=3N^2/(2-N)\), forcing \(N=1/2\), already excluded. No new clock can occur in this branch, contrary to paid size six.

## The third and fourth rows are both non-carriers

The remaining fourth row has \(q_4=0\) and clock \(T\ne0,N\); otherwise it duplicates the origin or third row by its first two moments. Exactly as in (1) of the single-defect source,
\[
                   f_4=T^2(3N-2T)/(2N).
\]
Through the first four rows the three pure size-five directions are independent: take \(\mathbf q,\mathbf f,C\mathbf f\) when \(f_4\ne0\), and \(\mathbf q,\mathbf f,A\mathbf f\) otherwise. Since \(\mathbf w\) is zero there, \(\mathbf w=0\) globally. Thus the common nonzero q-value is \(-1/2\), and \(f_i\) is the actual total feed from all carriers at clock 1. Through the fifth row it is still the coefficient on row 2 alone, irrespective of whether that fifth row is a new carrier.

If the fifth row is a non-carrier, all its moment and defect identities are exactly the fifth-row calculation of the frozen single-defect source: it reads only the first four rows, which have just the original q-carrier. That calculation used only the stated first-four values and the global size-five basis for the fifth-row equations. It proves the row is a duplicate except possibly when \(3N-2T\ne0\), \(T=2N\), it has clock \(T\), and \(f_5\ne f_4\). In that exceptional case \(A(C-NI)\mathbf f\) is a new fourth pure direction with nonzero fifth coordinate.

If the fifth row is a carrier, its clock is 1, its q-value is \(-1/2\), and its first clock moment is zero. We check it as follows.

* For \(3N-2T\ne0\), use the two donor polynomial identities and global pure formulas of (2) in that same source. The canceled constant terms in the first three clock moments change the fifth-row equations (3), at clock 1, to
\[
     [B-\nu(1-N)] f=0,\qquad
     [\alpha(1-N)+(N+T)/3] f=0,
\]
where \(B,\alpha,\nu\) are respectively \(N(2T-N)/6\), \(N/(3N-2T)\), \(-\alpha(T-N)/2\). If \(f\ne0\), the factorization for (3) puts 1 among \(N,T\). If \(N=1\), the two coefficients cannot both vanish. If \(T=1\), they both vanish only for \(T=2N\). In that exceptional case the coefficient on row 4 is \(f/(6N)\), from the first two clock moments (the first is zero here). This is nonzero, so \(A(C-NI)\mathbf f\) again gives the new fourth pure direction at row 5. If \(f=0\), both moment values vanish, forcing the other positive-clock feeds zero and a literal duplicate of row 2.
* For \(3N-2T=0\), the global relation \(C\mathbf f=N\mathbf f\) follows just as in the single-defect source. If \(N\ne1\), then \(f=0\) at this proposed row; its vanishing first two moments make it a duplicate. If \(N=1\), the first two moments and cubic condition yield \((5/6)f+g=0\), \(f/3+g/4=0\), where \(g=(A\mathbf f)_5\). Explicitly the first primitive moment is zero, the second is \(f/3\), and the third is \(f/2-g/4\); on the preceding labels \(0,1,3/2\) the cubic is \((5/2)\mathbf c^{\odot2}-(3/2)\mathbf c\), giving the second equation. The two equations force \(f=g=0\) and again a duplicate.

In either surviving fifth-row case \(T=2N\) and, as above, \(A(C-NI)\mathbf f\) makes the fourth pure direction. The size-six vector \((C-NI)(C-TI)\mathbf f\) is zero through row 5 and therefore zero everywhere. Thus \(\mathbf f\) is supported only at \(N,T\). Consider the first later non-carrier clock \(x\) outside \(\{0,N,T\}\). It has \(q=f=0\). Its total feed from all actual carriers is \(f=0\), so their clock-one contributions to every positive power vanish. The non-carrier predecessors lie at \(0,N,T\). The exact first three primitive moments would then imply \(-x^2(x-T)^2/4=0\) in the donor cubic hull, as in the earlier doubled-root calculation. Such a row cannot occur. All scalar clocks are therefore among \(0,1,N,T\), contrary to dense accuracy. For the ordinary output, its aggregate mass on actual carriers is zero because it annihilates their constant nonzero \(\mathbf q\); its effective clocks are at most \(0,N,T\), likewise impossible.

This exhausts one carrier label, including multiple physical carrier rows with either constant or varying q. Parts of the argument use [the one-coordinate calculation](../erk-single-quadratic-defect/SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md) for literal first-four and no-prefix fifth-row equations. No step assumes its final single-carrier-row hypothesis when later aggregate coefficients might differ.
