# A dense ERK width floor when the second-order defect uses at least three clocks

Let \(A\) be an explicit tableau, let \(\mathbf c=A\mathbf1\), and let \(C\) multiply by \(\mathbf c\) coordinatewise. Define
\[
             \mathbf q\coloneqq A\mathbf c-\mathbf c^{\odot2}/2 .
\]
For each size \(j\), let \(F_j\) be the actual span of formal rooted combinations of size at most \(j\) with zero model polynomial. A row carries \(\mathbf q\) if its coordinate of \(\mathbf q\) is nonzero. Labels of carriers are counted by their distinct physical clock values, so a carrier at clock zero counts, and repeated carrier clocks count once.

Suppose there are at least three carrier labels. Then an explicit dense derivative chart through size \(m\ge6\) requires **at least \(2m-1\) stages**. More precisely, \(\dim F_6\ge5\) both for a dense size-six chart and for any ordinary order at least six on such a tableau. These conclusions hold over a field with the required small integers invertible. They pass to a nonzero paid base if the requisite three distinct nonzero carrier coordinates and distinct labels survive in some prime quotient (unit residual coordinates and pairwise clock differences suffice). Different labels need not survive under every specialization, so no unconditional ring transport of this support hypothesis is intended.

The earlier pure no-plateau lemma gives \(\dim F_j\ge j-2\) and strict growth between successive paid sizes. Therefore, to prove the dimension claim, assume to the contrary that \(\dim F_6=4\). We then have \(\dim F_4=2,\dim F_5=3\). Once the contradiction proves at least five defects at size six, the no-plateau lemma gives \(\dim F_m\ge m-1\) through the dense cap, and the \(m\) independent model powers give the stated stage floor. No positivity of output weights or of clock values is needed.

## The one-dimensional feed obstruction

Suppose there are exactly \(d\) carrier labels in an actual predecessor region, and a receiver annihilates the incoming vectors \(\mathbf q,C\mathbf q,\ldots,C^{d-2}\mathbf q\). Suppose also that \(q_i\) is constant and nonzero among carriers at the same clock. Then the raw feeds into the carrier groups, pooled by label, lie on one fixed line: after multiplying each group mass by its nonzero \(q_i\), the \(d-1\) annihilation tests are a Vandermonde of rank \(d-1\). This concerns actual aggregate stage coefficients and does not require any sign.

For the applications here the receivers have exact primitive moments through polynomial degree three. The earlier non-carrier rows either have clock zero or clock \(\theta\), where \(\theta\ne0\) is the first nonzero non-carrier clock. At that first receiver, its carrier part on every paid polynomial must be \(I_\theta\) minus a multiple of evaluation at zero, where \(I_y\coloneqq\int_0^y\). It is nonzero, since it reads \(X\) as \(\theta^2/2\). It therefore spans the line on polynomials. If the carrier labels do not change, a subsequent receiver at any proposed nonzero new clock \(y\) must satisfy
\[
       I_y P=\lambda I_\theta P
       \quad\text{for }P=X(X-\theta),\ X^2(X-\theta).
\]
The previous non-carrier coordinates vanish on both tests. With \(z=y/\theta\), the first test gives \(\lambda=z^2(3-2z)\) and the second gives \(\lambda=z^3(4-3z)\). For nonzero \(z\) this implies \(3(z-1)^2=0\). Thus no new nonzero receiver clock can occur while the region has those same \(d\) carrier labels and the stated line of feeds.

## Exactly three carrier labels

The pure space through size five is then exactly \(\operatorname{span}(\mathbf q,C\mathbf q,C^2\mathbf q)\), by Vandermonde on the three carrier labels. Since \(\mathbf q^{\odot2}\) belongs to this space, on carriers \(q_i=P(c_i)\) for a polynomial \(P\) of degree at most two. In particular the value is constant on each carrier group. At every non-carrier row all pure size-through-five expressions vanish. Its exact lower primitive moments through degree three follow by taking unary roots of the normalized bush powers, and its incoming row annihilates \(\mathbf q,C\mathbf q\) (their unary lifts are paid). Thus the carrier feed has the rank-one property just proved, taking the full set of three carrier labels, with zero coefficients for those not yet physically present. If there is a first nonzero non-carrier clock \(\theta\), the line it generates applies throughout.

These three pure directions span all carrier-group values (and zero off the carriers). For every tree through size five the data on each carrier group agree, because they are the exact model evaluation plus a polynomial multiple of \(q_i\). A dense decoder annihilating the pure directions can therefore see only the non-carrier values, which are evaluations at clocks drawn from \(\{0,\theta\}\). The same argument works if there is no nonzero such clock, with just evaluation at zero. The model rank is at most two, impossible through size five. For an ordinary output the pooled weights on the three carrier groups likewise vanish. The remaining quadrature would have only clocks \(0,\theta\); exact first and second moments force \(\theta=2/3\) and then the third is \(2/9\ne1/4\). Thus this case already contradicts \(\dim F_5=3\) under ordinary or dense size five.

## At least four carrier labels: the initial four-row carrier hull

Now \(F_6=\operatorname{span}(\mathbf q,C\mathbf q,C^2\mathbf q,C^3\mathbf q)\) and \(F_5\) is the span of the first three. Again \(\mathbf q^{\odot2}\in F_5\), so there is a degree-at-most-two polynomial \(P\) with \(q_i=P(c_i)\) on the carrier rows. Put
\[
                     \mathbf r\coloneqq P(\mathbf c)-\mathbf q.
\]
This is an actual size-through-three rooted combination with model \(P\). It is zero on carriers; on non-carriers it equals \(P(c_i)\). Define three actual rooted combinations
\[
 \mathbf v_0\coloneqq AC\mathbf r,qquad
 \mathbf v_1\coloneqq AC(C-I)\mathbf r,qquad
 \mathbf v_2\coloneqq A^2 C\mathbf r .
\]
The corresponding size caps are five, six and six. We will normalize the first nonzero non-carrier clock to one before using the last two.

There must be a nonzero non-carrier clock. Otherwise \(C^j\mathbf q=(X^jP)(\mathbf c)\) for every positive \(j\), since the non-carrier clocks all vanish. In a dense chart, already \(j=1\) contradicts exactness: the left side is pure and the model of the right side is the nonzero polynomial \(XP\). For an ordinary output, \(j=1,2,3\) are paid and give \(\int_0^1 X^jP=0\). The three-by-three Gram with weight \(X\) has determinant \(1/43200\), a paid unit (equivalently solve the three moments), and forces \(P=0\). This too is impossible.

Let \(\theta\) be the first nonzero non-carrier clock. At that row the exact stage primitive moments hold through degree four, and \(A\mathbf q,AC\mathbf q,AC^2\mathbf q\) have zero entries. If at most three carrier labels had occurred beforehand, weighted Vandermonde would force all their aggregate feeds to be zero. The other prior rows have clock zero, which would make the exact moment \((A\mathbf c)_i=\theta^2/2\) impossible. Thus at least four distinct carrier labels precede \(\theta\).

On those predecessors, \(C^j\mathbf q=(X^j P)(\mathbf c)\) for \(j=1,2\), as any preceding non-carrier clock is zero. The same two annihilation tests and the row's exact scalar moments give \(I_\theta(XP)=I_\theta(X^2P)=0\). Scale \(A\) and the clocks by \(\theta^{-1}\) for the rest of the structural argument; replace \(P(X)\) by \(\theta^{-2}P(\theta X)\). We may thus assume \(\theta=1\). The two weighted moments force
\[
                  P(X)=p_2\bigl(X^2-\tfrac65X+\tfrac3{10}\bigr),\qquad p_2\ne0.
\]
Indeed on degree at most one the weight-\(X\) Gram determinant is \(1/72\), and the displayed degree-two monic polynomial solves the two equations.

Write \(I\) for the lower primitive as a polynomial, and let \(V_j\) be the model of \(\mathbf v_j\). Explicitly
\[
\begin{aligned}
 V_0&=I(XP)=\frac{p_2}{20}X^2(X-1)(5X-3),\
 V_1&=I(X(X-1)P)=\frac{p_2}{20}X^2(X-1)^2(4X-3),\
 V_2&=I^2(XP),\
 V_1+V_2&=(X-1)V_0 .
\end{aligned}
\]
The pure differences allow us to write
\[
            \mathbf v_j=V_j(\mathbf c)-L_j(\mathbf c)\odot\mathbf q,
       \qquad \deg L_0\le2,\quad \deg L_1,\deg L_2\le3.
\]
This uses only the actual spanning statements for \(F_5,F_6\). Set \(R_j\coloneqq V_j-P L_j\). Every carrier clock preceding the first nonzero non-carrier is a root of all three \(R_j\): before that row, \(C\mathbf r=0\), so the three actual combinations vanish. The polynomial \(R_0\) is nonzero of degree at most four. Indeed \(P\) is coprime to \(V_0\) (its values at \(0,1,3/5\) are nonzero paid multiples of \(p_2\)), and \(R_0\) differs from \(V_0\) by a multiple of \(P\). Thus exactly four distinct carrier labels precede this first non-carrier. If \(Q_4\) is their monic hull, then \(R_0=kQ_4\) for \(k\ne0\), and \(Q_4\) is coprime to \(P\).

## No first novel event after the initial non-carrier

Suppose a new event occurs, meaning that either a new carrier label appears or a non-carrier clock outside \(\{0,1\}\) occurs. Look at the first such row. With the unchanged four carrier labels, the incoming annihilation of \(\mathbf q,C\mathbf q,C^2\mathbf q\) gives the fixed line of feeds. The rank-one primitive test rules out a new non-carrier clock.

At a proposed new carrier clock \(y\), all earlier non-carrier clocks are 0 or 1. Therefore \(C(C-I)\mathbf r\) is zero on all predecessors, so \((\mathbf v_1)_i=0\). Also \(\mathbf v_0\) is zero on all predecessors: pre-existing carrier labels repeat their old size-five data, and at non-carriers it reads the model \(V_0\), which vanishes at 0 and 1. The repeated-label assertion follows directly from the common \(P(c_i)\) and the support form of all the pure differences through size five; no equality of their raw incoming coefficients is assumed. Hence \((\mathbf v_2)_i=0\) as well. Thus \(R_1(y)=R_2(y)=0\).

On the old four carrier labels, each \(R_j\) vanishes, as does \((X-1)R_0\). Using the model identity, the difference \(R_1+R_2-(X-1)R_0\) is a multiple of \(P\) times a polynomial of degree at most three. This polynomial has four distinct roots because \(P\) is nonzero on those four carrier labels. Therefore
\[
                   R_1+R_2=(X-1)R_0=k(X-1)Q_4 .
\]
Since \(Q_4(y)\ne0\), a new carrier would have to satisfy \(y=1\). But direct reduction modulo \(P\) gives
\[
                  V_1\equiv\frac{8X-7}{5}V_0\pmod P.
\]
For example the ratio of their un-reduced factors is \((X-1)(4X-3)/(5X-3)\); replacing \(X^2\) by \(6X/5-3/10\) gives the stated affine remainder, and \(5X-3\) is invertible modulo \(P\). Since \(Q_4\) is coprime to \(P\) and \(R_1/Q_4\) has degree at most one, comparison of these same remainders proves the polynomial identity
\[
                     R_1=k\frac{8X-7}{5}Q_4 .
\]
In particular it is nonzero at 1 whenever 1 is a new carrier label. This contradiction excludes the first novel event. Consequently all carrier labels belong to the old four and all non-carrier clocks belong to \(\{0,1\}\) in the normalized coordinates.

The four pure clock powers of \(\mathbf q\) fill the carrier group coordinates. As in the three-label case, a dense size-six decoder would have model rank at most two; an ordinary order-six output would have pooled scalar quadrature at only the original clocks corresponding to 0 and 1, which fails the third moment. This proves the theorem for any number of labels at least four.
