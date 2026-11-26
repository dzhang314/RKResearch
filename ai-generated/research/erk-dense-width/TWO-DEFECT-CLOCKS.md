# Two carrier clocks cannot attain the size-six defect minimum

Use the notation and field hypotheses from [the multiple-clock case](MULTIPLE-CLOCK-DEFECT-FLOOR.md). Suppose ordinary accuracy or a dense decoder holds through size six. If \(\dim F_6=4\), then the pure dimensions through sizes three, four and five are respectively 1, 2 and 3. We prove a contradiction when the nonzero coordinates of \(\mathbf q=A\mathbf c-\mathbf c^{\odot2}/2\) occur at exactly two distinct clock labels \(a,b\). A carrier is a row where \(q_i\ne0\), and a non-carrier is a row where \(q_i=0\). The pure symbols \(A\mathbf q,AC\mathbf q,A(\mathbf q^{\odot2})\) use costs four, five and six; \(\mathbf v=A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4\) uses cost five.

The first four-size pure space is \(\operatorname{span}(\mathbf q,C\mathbf q)\). In particular, at every non-carrier the exact lower primitive moments through degree two hold, and its incoming row annihilates \(\mathbf q\). A nonzero non-carrier clock must exist. Otherwise all actual labels belong to \(\{0,a,b\}\). For a dense chart the clock powers then do not span the model; for ordinary order six the monic cubic hull \(X(X-a)(X-b)\) would be orthogonal to \(1,X,X^2\), contrary to the paid shifted-Legendre monic cubic having nonzero constant \(-1/20\). Write \(\theta\) for the first nonzero non-carrier clock.

## One residual value per carrier label

If \(\mathbf q^{\odot2}\in F_4\), then \(q_i\) is constant and nonzero within each carrier group, by comparing \(q_i^2\) with a linear polynomial in the clock times \(q_i\). For a non-carrier, the two pooled raw feeds on the carrier labels lie on one fixed line by their annihilation of \(\mathbf q\). The first such nonzero-stage feed is nonzero at \(\theta\), since its first positive clock moment equals \(\theta^2/2\) and all its earlier non-carrier clocks are zero. On the two labels the first positive clock moment of the weighted defect feed, \((AC\mathbf q)_i\), is a nonzero linear test of this line: its two weighted masses sum to zero, but unequal labels distinguish them. Thus \(\mathbf f\coloneqq AC\mathbf q\) is nonzero at \(\theta\), and
\[
                   F_5=\operatorname{span}(\mathbf q,C\mathbf q,\mathbf f).
\]
At each non-carrier \(\mathbf v\) is a fixed scalar multiple of \(\mathbf f\). In particular if its carrier feed is \(\lambda\) times the feed at \(\theta\), its cubic primitive error is \(\lambda v_\theta\). Consequently, on each of the positive powers \(P=X,X^2,X^3\) the true primitive moment at clock \(y\) obeys
\[
             I_y P=\lambda I_\theta P+
                       \sum_{j<i:\,q_j=0} A_{ij}P(c_j).
\]
For the first two powers this follows from their actual exactness; for \(X^3\) subtract the observed cubic defect and use that every non-carrier before \(\theta\) has clock zero. Therefore the first proposed novel non-carrier \(y\notin\{0,\theta\}\) satisfies the same rank-one tests on \(X(X-\theta),X^2(X-\theta)\) as in the prior source. Their difference gives \(3(y/\theta-1)^2=0\), a contradiction.

All non-carrier labels are consequently in \(\{0,\theta\}\), and there are only four possible physical labels, not enough for a dense chart even through size five. For an ordinary output the two carrier-group masses vanish, by its annihilation of \(\mathbf q,C\mathbf q\); its remaining scalar quadrature on \(0,\theta\) cannot meet order four. This first case used only the accurate conditions through size five and the initial two defect ranks there.

## More than one residual value at a carrier clock

If \(\mathbf q^{\odot2}\notin F_4\), then
\[
                F_5=\operatorname{span}(\mathbf q,C\mathbf q,\mathbf q^{\odot2})
]
is supported entirely on carriers. Every non-carrier is now individually exact through size five. At the first nonzero non-carrier \(\theta\), the incoming row annihilates \(\mathbf q,C\mathbf q\), so the weighted q-mass within each label vanishes separately. Any label with only one prior nonzero q-value then contributes zero raw feed mass. If only one nonzero label contributed, exact positive clock moments through degree three would require \(\theta=3a'/2\) and \(\theta^2=2(a')^2\) for that label \(a'\ne0\); these are incompatible. With no such label the first moment fails. Thus both carrier labels are nonzero, with at least two distinct q-values at each before \(\theta\).

The four pure vectors obtained by restricting \(\mathbf q\) and \(\mathbf q^{\odot2}\) separately to each label form a basis of \(F_6\). They are available from \(\mathbf q,C\mathbf q,\mathbf q^{\odot2},C\mathbf q^{\odot2}\), and independent by the two q-values at each label. Thus at a carrier clock each tree profile through size six is its model value plus a quadratic in q without constant; at a non-carrier it is exactly the model value. In particular same-label rows with the same q-value have the same derivative data through the cap, whether or not their raw incoming rows are physically identical.

Let \(H(X)\coloneqq X(X-a)(X-b)\) and form the actual combinations and models
\[
\begin{array}{c|c|c}
&\text{actual}&\text{model}\\\hline
0&A H(\mathbf c)&V_0=I H\\
1&A(C-\theta I)H(\mathbf c)&V_1=I((X-\theta)H)\\
2&A^2 H(\mathbf c)&V_2=I^2H .
\end{array}
\]
Their size caps are five, six and six. Before \(\theta\), \(H(\mathbf c)=0\) on every row, so all three actual combinations are zero there. At \(\theta\) the actual first is still zero by chronology, hence \(V_0(\theta)=0\) by its individual stage exactness.

On each carrier group the first actual combination is a quadratic in q with constant \(V_0(a)\) or \(V_0(b)\) and the *same* quadratic coefficient, since its pure difference lies in \(F_5\). Those constants are respectively \(a^3(2b-a)/12\), \(b^3(2a-b)/12\); they cannot both vanish. Thus the common quadratic coefficient is nonzero (a linear polynomial vanishing at two distinct q-values on each label would give both constants zero). It follows that each group has exactly two different preceding q-values and that each constant is nonzero: the two roots are nonzero. In particular \(\theta\) differs from both carrier labels.

Consider the first event after \(\theta\) that is either a new non-carrier clock outside \(\{0,\theta\}\), or a third q-value at one carrier label. At a proposed new non-carrier the actual incoming row annihilates \(\mathbf q,C\mathbf q,\mathbf q^{\odot2}\). If the two old q-values at label \(a\) are \(u_a,v_a\) and its total raw feed is \(M_a\), the zero weighted first q-mass makes its weighted q-square mass \(-u_a v_a M_a\); the analogous assertion holds at \(b\). Thus the carrier-clock feeds satisfy
\[
                         u_a v_a M_a+u_b v_b M_b=0.
\]
Both products are nonzero. This is a fixed line, also containing the nonzero feed at \(\theta\). Exact polynomial moments through degree three then give the earlier rank-one contradiction to a new non-carrier.

At a proposed third q-value at a carrier label, the actual size-six combinations 1 and 2 above vanish. The first vanishes because \((C-\theta I)H(\mathbf c)\) is zero on all preceding data, including non-carriers at zero and \(\theta\). The second vanishes because the first actual size-five combination is zero on all predecessors: it repeats zero on the two old carrier profiles at each label and has the model values \(V_0(0)=V_0(\theta)=0\) on non-carriers. Thus the two quadratics in q for 1 and 2 vanish at the two older q-values and the proposed new one. Their constants \(V_1,V_2\) must both vanish at its carrier label. But
\[
                         V_1+V_2=(X-\theta)V_0
\]
by polynomial integration, which is nonzero at each carrier label. The first novel event is therefore impossible.

The remaining clock labels are at most \(0,a,b,\theta\). Again this contradicts dense size-six exactness. An ordinary output annihilates the split q,q-square modes of each carrier label, so its pooled mass on each of the two q-profiles is zero by their independent two-by-two Vandermonde. Its effective quadrature at only \(0,\theta\) fails the third moment. This proves the two-label exclusion without an assumed stage count or unverified sign.
