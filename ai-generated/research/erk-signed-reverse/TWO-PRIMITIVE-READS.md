# Two consecutive exact reads from older primitive banks

Here a weighted mean constraint on a primitive error gives an exact read one order beyond the literal stage's usual accuracy. Pinning that read in a later chart gives a new derivative constraint on the next primitive error. A second bank realizes this derivative constraint without new rows. The example prepares a grade-ten forward chart in 34 physical stages over \(\mathbb U_{17}\coloneqq\mathbb Z[1/17!]\). An actual new order-ten endpoint gives 35 rows. This is a forward prefix, not a new absolute upper bound at order fourteen. The formula uses seventeen and can be used without future primes in later targets of order at least seventeen.

Throughout write \(u\coloneqq2x-1\), \(\omega(u)\coloneqq(1-u^2)^2\), and \(\langle f\rangle\coloneqq\tfrac12\int_{-1}^1 f(u)\,du\). The letter \(I_x\) denotes the primitive from zero in the original variable \(x\). Use the established order-nine 16-stage seed, its actual endpoint, and the single grade-six midpoint stage. These 18 rows and the grade-seven chart \(\Pi_7\) are exactly those used in the 32-stage paid order-twelve proof. That chart uses the old quarter contrast and pins the old zeroth and first moments. The first primitive errors from its pure stages at tree order nine are in \(\omega\mathcal P_{\le4}\) with zero mean; \(\mathcal P_{\le j}\) denotes polynomials of degree at most \(j\). This follows from the actual endpoint and moment pins at children of size eight.

## First bank and its exact read

Append four pure rows \(I_{(1+z)/2}\Pi_7\) at the centered clocks \(-1/3,1/3,3/5,-5/3\), with nodal polynomial
\[
 Q_4(u)\coloneqq (u^2-1/9)(u-3/5)(u+5/3).
\]
The six point gaps, including the endpoints, and all \(\omega(z)\) are units. In particular the gap \(34/15\) pays seventeen. Set
\[
 F\coloneqq(u^2-1)Q_4,\qquad J_j\coloneqq\langle u^j F\rangle,
 \qquad\kappa\coloneqq J_1/J_0,\qquad \sigma\coloneqq Q_4(1).
\]
The even part of \(Q_4\) is \((u^2-1/9)(u^2-1)\), so \(\langle\omega Q_4\rangle=0\), as in the first rank-drop construction. Its odd part is \((16/15)u(u^2-1/9)\). The same three normalized beta moments \(8/15,8/105,8/315\), and \(\langle u^2(u^2-1)(u^2-1/9)\rangle=-8/189\), give
\[
 J_0=J_2=16/945,\qquad \kappa=-8/3,\qquad \sigma=128/135,
 \qquad Q_4(-1)=-\sigma.
\]
At the four new sites define \(\ell_4\) by dividing the inputs by \(\omega(z)\), interpolating them by a polynomial of degree at most three, and integrating that polynomial with weight \(\omega\). It is the exact mean on \(\omega\mathcal P_{\le4}\), by \(\langle\omega Q_4\rangle=0\). Thus \(\ell_4\) on the four physical rows gives the same read of the exact derivative polynomial through order nine. The grade-eight chart \(\Pi_8\) uses the four reads, both endpoints and the old moments of degrees zero and one. These moments split the point kernel spanned by \(F,uF\), since the determinant \(J_0^2(1-\kappa^2)\) is a unit. This chart pins both endpoints and the old mean on arbitrary data.

One identity simplifies the next two pivots. For constants \(a,b\), if the four samples of \((a+bu)/(1-u^2)\) are interpolated by a cubic \(G\), then
\[
 (a+bu)-(1-u^2)G=(au+b)Q_4/\sigma.
\]
Both sides vanish at the four sites, and their values at \(\pm1\) agree. Their degrees are at most five, which proves the identity. Consequently the weighted integral minus its four-node interpolatory value on this rational test function is \(-(aJ_1+bJ_0)/\sigma\). The expression only calls for evaluation at the interior or exterior old nodes, none of which is an endpoint, and its weighted integral is a polynomial integral.

## Second bank and its inherited derivative constraint

Append five pure rows \(I_{(1+z)/2}\Pi_8\) at the centered clocks \(\kappa,\pm1/3,\pm2\). Write
\[
 Q_5(u)\coloneqq (u^2-1/9)(u^2-4)(u-\kappa),\qquad
 D(u)\coloneqq(u^2-1)Q_5(u),\qquad K\coloneqq(1-1/9)(1-4)=-8/3.
\]
The first useful property of these five clocks is a paid grade-nine chart. Use their reads, the two endpoint reads, the old mean and \(\ell_4\). The seven point reads have kernel \(D,uD\). Dividing \(D\) and \(uD\) by \(\omega\) gives polynomial parts of degrees at most four and residues at the endpoints. Use the preceding interpolation identity on the rational remainders, with \(Q_5(1)=K(1-\kappa)\), \(Q_5(-1)=K(-1-\kappa)\). This gives
\[
 \langle D\rangle-\ell_4(D)=KJ_0(1-\kappa^2)/\sigma,
 \qquad \langle uD\rangle-\ell_4(uD)=0.
\]
The first difference is a unit. The second pivot is
\[
 \langle uD\rangle
 =\langle u^2(u^2-1)(u^2-1/9)(u^2-4)\rangle
 =136/945,
\]
a unit because seventeen is paid. All seven point gaps are units, so these give the paid chart \(\Pi_9\). Its order-nine input rows include the exact promoted read \(\ell_4\).

The second useful property is a next-order exact read from these same five actual stages. At a child of size nine the residual of \(\Pi_8\) has zero endpoints and zero mean; the old actual endpoint and output reads are exact at those tests. Its primitive \(P\) therefore belongs to \(\omega\mathcal P_{\le5}\). Unlike the previous primitive, this one need not have mean zero. Instead it obeys the inherited constraint
\[
 M(P)=0,\qquad M(f)\coloneqq\ell_4(f'),
\]
where the prime is differentiation in \(u\). Indeed \(\Pi_8\) is fitted to all four old stage reads. Their exact linear combination \(\ell_4\) agrees with the corresponding exact polynomial through size nine, so the residual has zero \(\ell_4\) read. Passing to the centered derivative changes only a factor of two.

The five-node geometry makes \(M(\omega Q_5)=0\). To see this, for \(R\) of degree at most five the ratio \((\omega R)'/\omega\) is \(R'-4uR/(1-u^2)\). All its polynomial-part terms have degree at most four and thus are integrated exactly by the rule behind \(\ell_4\). The mean of \((\omega R)'\) itself is zero at the boundary. The same simple rational remainder identity gives
\[
 M(\omega R)=-4(aJ_1+bJ_0)/\sigma,
 \qquad a\coloneqq\tfrac12(R(1)-R(-1)),\quad
 b\coloneqq\tfrac12(R(1)+R(-1)).
\]
For \(R=Q_5\) these values are \(a=K,b=-\kappa K\), and hence the result is zero. In particular, the outlying fifth clock was determined by the ratio \(J_1/J_0\), not by requiring a new quadrature mean to vanish.

Define \(\ell_5\) on the five old reads by dividing by \(\omega\) at their sites, interpolating by a polynomial of degree at most four, multiplying back by \(\omega\), and applying \(M\). This gives the exact value \(M(P)\) on \(\omega\mathcal P_{\le5}\), since the interpolation remainder is a scalar multiple of \(\omega Q_5\). Thus it annihilates every allowable first error on these five rows, and gives an exact derivative read through order ten. Unlike the mean rule in the previous bank, this linear rule realizes a derivative-based constraint.

Every one of its five scalar coefficients is a unit. For site \(z\), take \(R=Q_5/(u-z)\). Substituting its endpoint values into the displayed formula gives
\[
 aJ_1+bJ_0=J_0K(1-\kappa^2)/(1-z^2).
\]
The additional cardinal divisor \(\omega(z)Q_5'(z)\) is a unit, as are all factors on the right. Thus any one old clock can be omitted in the next chart while keeping the corresponding exact \(\ell_5\) coordinate.

## The grade-ten count and where it applies

Append seven rows \(I_{(1+z)/2}\Pi_9\). Take four of the five previous sites and all three sites \(0,\pm2/3\). Every difference on the union of endpoints, five previous sites and three new ones is a unit. The seven actual evals and two endpoints leave a one-dimensional kernel on polynomials of degree at most nine, generated by their monic nodal polynomial. Its value at the omitted old site is a unit, and it vanishes at the four retained old sites. Hence the read \(\ell_5\) gives a unit pivot on this kernel. These ten observations form a paid \(\Pi_{10}\), exact through order ten. The row count is \(16+1+1+4+5+7=34\).

If a literal order-ten endpoint is needed, append the row \(I_1\Pi_{10}\). The usual correction by \((3x^2-2x)(E_*-E_1\Pi_{10})\), with \(E_*\) the new endpoint read, makes the chart pin that new derivative coordinate. This correction vanishes on all tree data through order ten and preserves the integral row. The total is then 35 forward rows. No order-fourteen suffix or new whole tableau is established by this count.

More generally the same iteration works whenever an inherited exact read \(L\) is pinned in the previous chart: it gives the homogeneous condition \(L(P')=0\) on the next primitive. A bank with nodal polynomial \(Q\) preserves this condition upon interpolation when \(L((\omega Q R)')=0\) for every admissible remainder quotient \(R\). The extra conditions are about the old literal reads and the new nodal polynomial, not merely the nominal order of the old output. This example pays two different classes of constraints in succession; it does not assume that either fixed read remains exact at indefinitely higher orders.
