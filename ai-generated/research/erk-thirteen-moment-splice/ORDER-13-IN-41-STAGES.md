# Exact paid order thirteen in 41 explicit stages

There is an exact order-thirteen explicit Runge–Kutta tableau with 41 stages over \(\mathbb U_{13}\coloneqq\mathbb Z[1/13!]\), and over every nonzero commutative algebra over that ring. The improvement over the 42-stage tableau is in the forward prefix. The new prefix has the same four-clock bank size but its clocks admit an exact linear read of the next order. That read replaces one of the six separately constructed next-order stages. The 14-stage reverse suffix, its literal row mergers, and its unit next-order defect identity are unchanged.

## A general exact read from primitive stages

Write \(E_x f\coloneqq f(x)\), \(I_x f\coloneqq\int_0^x f(z)\,dz\), and \(g_t(x)\coloneqq |t|x^{|t|-1}/t!\) for the exact derivative polynomial of a rooted tree. Let \(\Pi_m\) send old stage data to polynomials of degree at most \(m-1\) and satisfy \(\Pi_m\boldsymbol{\Phi}_t(A)=g_t\) through tree order \(m\). For a child \(r\) of size \(m+1\), write
\[
 \rho_r\coloneqq g_r-\Pi_m\boldsymbol{\Phi}_r(A),\qquad P_r\coloneqq I_x\rho_r.
\]
Assume that \(\rho_r(0)=\rho_r(1)=0\) and that \(\int_0^1x^j\rho_r(x)\,dx=0\) for \(0\leq j\leq h\). Then \(P_r\) has double zeros at both endpoints: its derivative vanishes there, as does \(P_r\) by definition at zero and by the zeroth moment at one. Integration by parts gives \(\int_0^1x^j P_r(x)\,dx=0\) for \(0\leq j<h\), if the integers \(1,\ldots,h\) are units. In the centered coordinate \(u\coloneqq2x-1\), set
\[
 \omega(u)\coloneqq(1-u^2)^2,\qquad
 \langle f\rangle\coloneqq\frac12\int_{-1}^1f(u),du .
\]
It follows that \(P_r\), written in \(u\), has the form \(\omega R\), where \(R\) has degree at most \(m-3\) and \(\langle \omega u^j R\rangle=0\) for \(0\leq j<h\).

Consider old stages whose actual incoming rows are \(I_{(1+z_i)/2}\Pi_m\), with distinct centered clocks \(z_i\). Their derivative weights are individually exact through order \(m+1\). At order \(m+2\) a tree with more than one root child still gives the exact derivative weights, since every child then has order at most \(m\). The only errors are \(-P_r((1+z_i)/2)\) at trees \([r]\). Therefore a linear combination of evaluations that annihilates these primitive errors also gives an exact same linear combination of the exact derivative polynomials through order \(m+2\).

Here is a sufficient polynomial test for such a combination. Suppose \(\omega(z_i)\) and all clock differences are units, and put \(Q(u)\coloneqq\prod_i(u-z_i)\) for the \(N\) clocks. For a polynomial \(q\) of degree less than \(h\), take the weighted interpolatory read: divide each coordinate by \(\omega(z_i)\), interpolate on the \(N\) clocks, and integrate the interpolant against \(\omega q\). This read agrees with \(\langle qP_r\rangle\) whenever
\[
 \langle\omega q Q u^k\rangle=0\qquad(0\leq k\leq m-3-N).
\]
In fact polynomial division by the monic \(Q\) expresses the interpolation remainder as \(Q\) times a polynomial of degree at most \(m-3-N\). The displayed conditions account for all of that remainder. If the range for \(k\) is empty, there is no condition. The exact moment of \(P_r\) is zero, so this is an exact next-order read. The condition is sufficient on an envelope for the actual tree errors; it does not presume that every polynomial in that envelope occurs as a tree error.

## The four old clocks and their next-order read

Start with the [original 16-stage order-nine seed](../erk-eleven-twelve-moment-splice/paid9-seed.json) used in the [verified 32-stage order-twelve construction](../erk-eleven-twelve-moment-splice/ORDER-12-IN-32-STAGES.md). Append its actual output row at clock one and the single midpoint row from its grade-six chart. Use the same grade-seven chart \(\Pi_7\) as in that construction: it has both endpoint reads, the old output moments of degrees zero, one, and two, the original literal quarter-clock contrast, and the new midpoint read. These are seven paid linear conditions on polynomials of degree at most six. In particular the original quarter contrast and all previous stages are unchanged.

Instead of the four next preparatory clocks in the order-twelve tableau, use the four centered clocks
\[
 z_1=-5,\qquad z_2=-1/3,\qquad z_3=1/5,\qquad z_4=1/3 .
\]
Their stage rows are \(I_{(1+z_i)/2}\Pi_7\), and their actual clocks are \(-2,1/3,3/5,2/3\). All differences among these four clocks and the two endpoints are units in \(\mathbb U_{13}\); the gap between \(-5\) and \(1/5\) uses thirteen but no later prime. The polynomials in the preceding test are now
\[
 Q\coloneqq (u^2-1/9)(u-1/5)(u+5),\qquad
 F\coloneqq (u^2-1)Q .
\]
The even part of \(Q\) is \((u^2-1/9)(u^2-1)\). The moments of \(\omega\) in degrees zero, two, and four are \(8/15,8/105,8/315\). Hence \(\langle\omega Q\rangle=0\). At size-eight children, the actual endpoint and zeroth and first moment pins of \(\Pi_7\) are exact by old order nine. The general test applies with \(m=7\), \(h=1\), \(N=4\), and \(q=1\). Write \(\ell\) for its read. The linear combination \(\ell\) of the four stage derivatives is exact through tree order nine.

To form the grade-eight chart, use these four stage reads, both endpoint reads, and the old zeroth and first moment reads as before. On polynomials of degree at most seven the six point evaluations have kernel spanned by \(F,uF\). Define \(J_j\coloneqq\langle u^jF\rangle\). Direct even-moment integration gives
\[
 J_0=16/945,\qquad J_1=-192/945,\qquad J_2=J_0 .
\]
Indeed, the even part of \(F\) is \(\omega(u^2-1/9)\), and its odd part is \((24/5)u(u^2-1)(u^2-1/9)\). Thus \(J_0\) follows from the first two weighted moments above and \(J_1\) from \(\langle u^2(u^2-1)(u^2-1/9)\rangle=-8/189\). The identity \(J_2=J_0\) is \(\langle\omega Q\rangle=0\). The zeroth and first moments on the two-dimensional kernel have determinant \((J_0+J_1)(J_0-J_1)\). The factors are \(-176/945\) and \(208/945\), units in \(\mathbb U_{13}\). Replacing the first moment in \(u\) by that in \(x\) changes determinant by a unit. We thus obtain the paid chart \(\Pi_8\), exact on tree order at most eight.

## Five new rows suffice for the grade-nine chart

Append only five rows of the form \(I_{(1+u)/2}\Pi_8\), at the centered clocks
\[
 -1/3,\quad 1/5,\quad 1/3,\quad -1/2,\quad 1/2.
\]
These are correct derivative evaluations through order nine. The grade-nine chart uses those five rows, the two endpoint reads, the old scalar output as the zeroth moment, and the exact read \(\ell\) from the four earlier primitive stages. The seven point gaps are all paid. On polynomials of degree at most eight their kernel is spanned by \(D,uD\), where
\[
 D\coloneqq (u^2-1)(u^2-1/9)(u-1/5)(u^2-1/4).
\]
The read \(\ell(D)\) has only the term at \(u=-5\), because \(D\) vanishes at the other three old primitive clocks. The unnormalized weighted-cardinal numerator at that remaining clock is
\[
 \left\langle\frac{\omega Q}{u+5}\right\rangle
 =-\tfrac15\left\langle\omega(u^2-1/9)\right\rangle=-16/4725.
\]
Dividing by \(\omega(-5) Q'(-5)\) gives the coefficient of the \(-5\) read in \(\ell\), which is a unit. Also \(D(-5)\) is a product of unit differences to the seven new evaluation sites, including the endpoints. Thus \(\ell(D)\) is a unit. The other kernel vector may be taken to be \((u+5)D\); it is zero at all four old clocks and hence has \(\ell\) read zero. Its zeroth moment is
\[
 \langle (u+5)D\rangle=\langle F(u^2-1/4)\rangle=J_2-J_0/4=4/315.
\]
This is also a unit. The nine reads therefore determine a paid chart \(\Pi_9\), exact through order nine, pinned at the original origin and actual order-nine endpoint. Its integral on arbitrary data is the old output row, not merely an equal low-order functional. The exact derivative read at the order-nine endpoint itself holds through order ten, by the old order conditions. In all these solves, point values can first be subtracted using paid Lagrange interpolation; the displayed small pivots then solve the remaining polynomial coordinates. No other denominators occur.

The forward stage count is \(16+1+1+4+5=27\). The grade-nine chart is defined on these actual stage data; applying \(\ell\) adds no row.

## The unchanged order-thirteen suffix

Attach the 14 physical rows of [the archived 42-stage method](README.md), using this \(\Pi_9\) in its cross block. The other data in that construction are unchanged: the quadrature has centered scale \(12x-6\) at sites \(-6,-5,-4,-3,-2,-1,0,2,3,4,5,6,8\); the reverse chronological donors have clocks \(1,5/6,1/2,2/3\); two nonendpoint masses are split. The prescribed first-defect values on these donors are \(0,-1/72,1,1/3\), and the remaining moments are solved on the eight late unit labels. This specifies the same reconstructible suffix, not a new choice of quadrature or donor values.

For the ordinary order proof the suffix only requires that \(\Pi_9\) be exact through tree order nine, that its zero and one evaluations be the actual endpoint reads, and that \(I_1\Pi_9\) equal the old output row. These have been established. The error from a unary root is still \((A_S E-I)\rho_t+A_S\boldsymbol\epsilon_t\), where \(A_S\) is the strictly triangular suffix block, \(E,I\) collect the suffix evaluations and primitives, \(\rho_t\coloneqq g_t-\Pi_9\boldsymbol{\Phi}_t(A_F)\), and \(\boldsymbol\epsilon_t\) is the suffix derivative error. In the length-two reverse tests, \(|t|=10\) and \(\rho_t\) has degree at most nine and vanishes at both endpoints, exactly the required test space. The lower reverse tests and the ordinary quadrature are unchanged. The clock-zero and remainder clock-one labels still merge into actual old rows, and every pure repeated non-donor label keeps precisely the same incoming row as its companion. Hence the suffix retains its literal count of 14.

The proof of exactness is also unchanged. For \(r\coloneqq[\bullet]^{\#11}\) the residual \(\rho_r\) still has leading coefficient one in degree eleven and no constant term. If \(\Delta_t\) denotes the unscaled output defect at a tree \(t\), the suffix identity is
\[
 \Delta_{[r]\#[\bullet]}+\tfrac12\Delta_{[\bullet]^{\#13}}=-\eta,
\]
where \(\eta\) is the unit barycentric normalization from the fixed suffix. Both trees have order fourteen. Their factorials are units of \(\mathbb U_{13}\), since the only factors possibly needed are at most fourteen and fourteen itself has primes two and seven. Thus this identity is also a unit-ideal certificate for the factorial-cleared defects, including after every nonzero paid base change.

The total is \(27+14=41\) physical stages, after counting only the documented mergers.
