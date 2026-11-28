# DIRK12/15: the entire scalar live grid is finite in two high-site reverse charts

Continue the real ordinary fifteen-stage order-twelve DIRK \(C(2),f_5=3\) weighted-invisible cubic frame with four distinct cubic-dirty ghosts. Use either the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) (nonzero aggregate return mass as already proved) or the [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology.

The **entire ordered live scalar clock grid** takes only finitely many real algebraic values. More specifically, for each actual first-five ordinary nonzero live prefix, there are at most ten possibilities for the remaining three ordered distinct reverse nonzero clocks. The aggregate scalar weight at each distinct clock is then unique and algebraic. This is not a finiteness claim about physical weight splits at repeated labels, ghost weights/amplitudes, individual tableau entries, or the full equality face outside these two reverse chronologies. It does not assert that the finite set is empty, and the real DIRK12 interval stays **15–16**.

## Only three unknown scalar sites after the two actual prefixes

Use the reflected clock \(Y=\mathbf1-\mathbf c\). In the stated nine-site chart the first four nonterminal physical live rows in reverse order are \(d,v,d,u\) with three distinct nonzero labels; the repeated \(d\) has nonzero aggregate weight by the exact early return proof. In the stated ten-site chart those rows are \(d,v,0,u\), where the extra zero is at the already fixed label of the literal terminal, and \(d,v,u\) are three distinct nonzero singleton labels. In each case \(v,u\) have nonzero weights; intervening ghosts have zero weights.

There are ten nonterminal physical live rows. The *other* six nonterminal live rows are, in ordinary order, the literal origin and the first five distinct nonzero ordinary live rows. Those clocks are confined to the finite algebraic set of the [fifth ordinary live proof](../dirk12-fifteen-rank3-invisible-fifth-ordinary-live/README.md), which applies without restricting individual ghost geometry. Thus every distinct live scalar label except \(d,v,u\) is now fixed. Include the literal origin \(Y=1\) and literal terminal \(Y=0\) exactly once each in the fixed set \(S\), even if they repeat as actual physical labels. Write
\[
       P(Y)=\prod_{q\in S}(Y-q),\qquad
       K(Y)=(Y-d)(Y-v)(Y-u)=Y^3-A Y^2+B Y-C.
\]
The three unknown labels are disjoint from \(S\) and \(\deg P\le7\). Here \(A,B,C\) are scalar elementary symmetric coordinates, not the Runge–Kutta matrix. Each physical grid consistent with this ordinary prefix gives this pair of polynomials; the notation does not impose anything on individual signed weight splits.

## Two actual affine equations for the three symmetric coordinates

The scalar quadrature is exact through degree eleven. For \(j=0,1\), the polynomial \(Y^j P(Y)K(Y)\) has degree at most eleven and vanishes at every live label. Thus, putting \(m_i=\int_0^1 Y^iP(Y)\,dY\),
\[
             m_{j+3}-A m_{j+2}+B m_{j+1}-C m_j=0,\quad j=0,1 .
\]
Its coefficients depend only on the fixed prefix. These two actual affine equations are independent, with no generic moment-rank assumption. To see this, apply the same paid scalar exactness to \(Y^i P(Y)\) for \(i\le4\). Its evaluations vanish at every other label. Each \(m_i\) is the exact three-atom sum at \(d,v,u\), with respective coefficients \(\beta_d P(d),\beta_v P(v),\beta_u P(u)\); \(\beta\) denotes actual aggregate scalar weight. All three coefficients are nonzero by distinctness and the literal mass guards above. The two by three block \((m_{i+j})_{0\le i\le1,0\le j\le2}\) factors as the two by three Vandermonde, their invertible diagonal weights, and the three by three Vandermonde. It therefore has rank two, even for signed weights. Its reversal and scalar signs give the coefficient matrix of the two affine equations. Their common solution set is a real affine line (if a candidate exists) with an algebraic parametrization because the prefix is algebraic.

## The early reverse gate contains no affine line of admissible points

The true normalized early reverse ratio equation in both charts is \((r^2-4r+1)t+r(r+1)=0\), with \(r=v/d,t=u/d\). In physical reflected units this is
\[
             (v^2-4dv+d^2)u+dv(d+v)=0.
\]
Using \(A=d+v+u,\ B=dv+u(d+v),\ C=dvu\), this is exactly
\[
                       B(A-u)=6C .
\]
Since all three clocks are nonzero, \(C\ne0\), so \(B\ne0\). The distinguished third clock is therefore uniquely prescribed,
\[
                        u=A-6C/B.
\]
Its own equation \(K(u)=0\) becomes \(Bu-C-6C u^2/B=0\). Equivalently the affine line of candidates must intersect the degree-at-most-five surface
\[
           (AB-7C)B^3-6C(AB-6C)^2=0.
\]

Here is an exact noncontainment proof for every affine line which has an admissible point with \(BC\ne0\). If \(B\) is constant, it is nonzero and \(u=A-6C/B\) is affine. If \(C\) is also constant, it is nonzero and \(u\) varies along a nonconstant line; the quadratic coefficient of \(Bu-C-6C u^2/B\) is then nonzero. If \(C\) varies, its cubic coefficient first forces the slope of \(u\) to be zero. With \(u\) constant, the remaining expression is \(Bu+(-1-6u^2/B)C\); vanishing identically as \(C\) varies would first give \(u=0\), leaving the nonzero coefficient \(-1\).

If \(B\) varies, parameterize the line by \(B\), writing \(A=\alpha B+\beta,\ C=\gamma B+\delta\). In \(Bu-C-6C u^2/B\), the \(B^{-3}\) Laurent coefficient is \(-216\delta^3\); an identity would force \(\delta=0\). Then \(\gamma\ne0\) by the existence of an admissible point. Set \(u=\alpha B+\eta\) with \(\eta=\beta-6\gamma\). The expression reduces to
\[
               B(\alpha B+\eta)-\gamma B-6\gamma(\alpha B+\eta)^2 .
\]
Its constant term \(-6\gamma\eta^2\) would force \(\eta=0\), leaving the linear coefficient \(-\gamma\ne0\). Thus no such line is contained in the surface. This proof has no assumption about where the early reverse labels lie relative to \([0,1]\) or their signs.

The resulting line polynomial is nonzero and has degree at most five. There are at most five symmetric triples, each algebraic, and \(u\) is fixed by each. The remaining roots \(d,v\) of \(K\) have at most two orderings. This proves the claimed bound of ten triples per ordinary prefix. Finally the scalar quadrature gives the aggregate weights by its square Vandermonde moment equations at the distinct live labels; there are at most ten distinct nodes here and all corresponding moments through degree nine are paid. Nothing here fixes the physical split of an aggregate weight.

## Verification

    python3 -B verify.py

The exact symbolic script checks the early gate equivalence, line polynomial degree, and every coefficient used in noncontainment. The native portable companion checks the final denominator-cleared coefficient contradictions over the integers with a typed audit. The rank using true nonzero aggregate weights and the overall scalar-grid argument are mathematical. No degree-twelve moment, unknown coefficient reduction, or publication of an explicit scalar candidate set is claimed.
