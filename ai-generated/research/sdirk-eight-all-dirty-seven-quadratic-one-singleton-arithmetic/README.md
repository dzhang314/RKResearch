# A single physical singleton endpoint cannot open with three singleton clocks

Suppose a strict ten-stage SDIRK method has ordinary order at least eight over a characteristic-zero field, all ten quadratic defects nonzero, exactly seven different clocks, and exactly one physical endpoint with a singleton clock. In the actual orientation that starts at the singleton, the first-three clock types must be **S,D,D**, **S,S,D**, or **S,D,S**. Here S is a singleton and D a doubled clock. The [star companion](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-star/README.md) excludes S,S,S with a literal star third row; this packet eliminates S,S,S with a genuine arithmetic third row. Both-singleton endpoints, the two- and three-D-prefix possibilities, and the general 10–11 stage interval are not resolved by this result. No signs or ordering are required.

## The graph and two exact remainders

Use \(y=x-1,\ m=1/(2\gamma),\ h=m-1,\ t=y-h\) with normalized diagonal one and \(y\)-coordinates \(0,2h\) at the physical endpoints, \(h\ne0\). The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) and the [constant/affine exclusion](../sdirk-eight-all-dirty-seven-affine-final/README.md) give an affine nonconstant \(F_*\), a genuinely quadratic singleton graph \(R\), and \(Q/B=L_3-F_*L_4\) proportional to \(P R\), with \(P\) cubic and its three roots the D labels. The four S labels are exactly the roots of the quartic \(H=L_4-R C\), \(C=A_2+BR\). Let \(W\) be monic proportional to \(R\). \(W\) may overlap \(P\) or have a double root. Nothing below divides by \(W\) at a D clock.

An actual S,S,S arithmetic opener has singleton clock positions \(0,u,2u\), with values \(1/2,\kappa(u)/2,N(u)/(2D(u))\) where \(D(u)=-2+u+4u^2-u^3,\ \kappa(u)=1+2u-u^2,\ N(u)=(1+4u-4u^2)D(u)+4u^2(3u-2)\). All of \(u,\kappa,D,N,3u-2\) are nonzero by the true literal tap and residual guards. The uniquely fitted quadratic is
\[
       R(y)=\tfrac12(1+2y-y^2)+\frac{3u-2}{D(u)}y(y-u).
\]
The leading coefficient has numerator \(-D(u)+2(3u-2)=(u-1)^2(u-2)\) over \(2D(u)\). Thus \(u=1,2\) is impossible in this chart **because the graph is quadratic**, not by ignoring later exceptional clocks.

With \(L_3=t^3-3m^2t/5\) and \(L_4=t^4-6m^2t^2/7+3m^4/35\), set
\[
 F_*=(L_3/L_4)\bmod W,\quad \mathcal P=(L_3-F_*L_4)/W,\qquad
 J_3^\mathrm{s}(y)=y(y-u)(y-2u).
\]
Division in a remainder means multiplication by its inverse in the quadratic quotient. Consecutive Legendre coprimality ensures \(L_4\) is a unit modulo \(W\), because \(W\mid Q\). Also \(J_3^\mathrm{s}\) is a unit modulo \(W\), since its three roots are actual singleton clocks all with nonzero defects. Both assertions apply even if \(W\) has a repeated root. The actual terminal D gives \(\mathcal P(2h)=0\). The other two D clocks satisfy the monic quadratic \(\Delta\) obtained by its exact deflation. To form equations before specializing, synthetic division by \(y-2h\) with a possibly nonzero discarded remainder gives a polynomial quotient, and the terminal equation then makes it exact. The common cubic leading coefficient is nonzero because \(F_*\) is nonconstant.

Now form
\[
          M_0+M_1 y=(L_4/J_3^\mathrm{s})\bmod W .
\]
This must equal \(H_4(y-s)\), with \(H_4\ne0\) the leading coefficient of the singleton quartic and \(s\) the fourth and remaining singleton coordinate. Thus \(M_1\ne0\) and \(s=-M_0/M_1\). Both statements hold regardless of where the fourth singleton occurs chronologically. The exact reconstruction for low-degree fields never discards an unproved guard, and the good-place certificates below require this coefficient to stay a unit rather than silently dropping a residue component.

## The five possible true rear meshes

The true weighted mirror sees a first D, with clock reflection \(y'=2h-y\). It cannot have two further S rows: the disjoint forward triple has already used three of the four singleton rows. Its two other labels are distinct from each other and the terminal, by the genuine first-three phase gates. Let \(\sigma\) be the sum of the two roots of \(\Delta\).

1. Rear D,D,D star: \(\sigma=4h-2\).
2. Rear D,D,D arithmetic: its reverse second D label has original coordinate \(d=(\sigma+2h)/3\); use \(\Delta(d)=0\). The other D is \(2d-2h\). This relation does not assume any sign or chosen order of abstract roots.
3. Rear D,D,S arithmetic: \(d=(s+2h)/2\) and \(\Delta(d)=0\).
4. Rear D,S,D arithmetic: \(d=2(s-h)\) and \(\Delta(d)=0\).
5. One later D and one S in either actual star ordering: \(d=4h-2-s\) and \(\Delta(d)=0\).

These five equations and the terminal equation give decisive algebraic projections in \(u\). Polynomializations are audited against actual denominator/clock/evaluation guards: \(h,m,D,u,u-1,u-2,\kappa,N,3u-2\), the unit determinant of multiplication by \(L_4\) modulo \(W\), the cubic leading coefficient and \(L_4(2h)\). In the last three charts use also the unit determinant for \(J_3^\mathrm{s}\) and the true \(M_1\). Their nonzero status, except where explicitly supplied by the literal tap conditions, follows from the geometry just proved. At fixed \(W=y^2+b y+c\) multiplication by \(l_0+l_1y\) has determinant \(l_0^2-b l_0l_1+c l_1^2\); this makes the denominator checks independent of root choices.

The resultant in \(u\), after stripping only guards that must be nonzero, has rational irreducible factor degrees and multiplicities:
\[
\begin{array}{c|l}
\text{rear phase}&(\text{degree},\text{multiplicity})\\\hline
\mathrm{DDD\ star}&(6,1),(12,1),(36,1)\\
\mathrm{DDD\ arithmetic}&(2,1),(6,2),(7,1),(12,2),(63,1)\\
\text{one extra D (each of the three phases)}&(6,3),(12,3),(117,1).
\end{array}
\]
The use of a resultant does not assume either specialized leading coefficient is nonzero. In each exact field of degree at most twelve the actual pair of univariate polynomials has a linear gcd in \(u\). The literal guards remove all but the degree-seven branch. There a reconstructed reverse third D label is the actual first singleton clock; the independent number-field replay verifies an exact equality, not merely a collision modulo a prime. This treats all guard-loss factors before taking good places.

## The paid rear residual equations

At any candidate mesh, recover the singleton quartic \(H=M_1 J_3^\mathrm{s}(y)(y-s)\) and \(C=(L_4-H)/R\). At a rear D with actual normalized reverse residual \(\eta\), write \(g=\lambda\eta\) for its original residual, where \(\lambda\ne0\) is the true reverse-to-forward normalization. The actual equation is
\[
 L_4(x)=\lambda\eta C(x)+B\lambda\eta\bigl(\lambda\eta-R(x)\bigr)
\]
where \(x\) here denotes its \(y\)-coordinate. In a D,D,D phase, the three actual oriented values \(\eta_i\) are known (the first is \(1/2\)); for a star check both orders. Regard the three equations as linear in \(X=\lambda,\ Y=B\lambda^2,\ Z=B\lambda\), with rows
\[
             [\eta_i C(x_i),\ \eta_i^2,\ -\eta_i R(x_i)\mid L_4(x_i)] .
\]
The identity \(Y=X Z\) still has to hold. The good-place replay checks a unit full-rank fit and a nonzero \(Y-XZ\), so no real-root or positivity question arises. In particular integrality of these three unknowns at the good place follows from the unit coefficient matrix, not by assuming a priori that \(B\) or \(\lambda\) is integral.

For a one-extra-D phase the actual \(s\)-residual fixes \(\lambda=R(s)/\eta_s\). The true terminal D gives \(B=(L_4(2h)-g_T C(2h))/(g_T(g_T-R(2h)))\), \(g_T=\lambda/2\). A double's observed residual is nonzero and off the singleton graph, hence this divisor is nonzero, even if the clock is a zero of \(R\). The extra D equation rejects the fitted values. No division by an unknown \(B\) is used.

## Exact simple good places, not prime-field heuristics

For each large rational irreducible factor, the replay uses this fixed table:
\[
\begin{array}{c|rrrr|l}
\text{rear phase}&\deg& p& h\bmod p&u\bmod p&\text{nonzero discrepancy}\\\hline
\mathrm{DDD\ star}&36&47&43&17&31,\ 31\\
\mathrm{DDD\ arithmetic}&63&37&19&4&25\\
\text{extra D second, arithmetic}&117&19&2&17&16\\
\text{extra D third, arithmetic}&117&53&22&40&22\\
\text{extra D, star}&117&41&4&27&26 .
\end{array}
\]
For a putative characteristic-zero solution the irreducible \(h\) factor gives an isomorphism of its abstract field to the subfield generated by the lifted simple root over \(\mathbb Q_p\). All relevant base polynomials have unit leading coefficient at the place selected by the table. The specialized first projection polynomial retains degree nine in \(u\), so a putative gap is algebraic and integral after extending the embedding. The verifier enumerates **all** roots of the reduced gcd of the two gap polynomials, with total multiplicity equal to the gcd degree. Each is one of the listed values. It checks all needed distinct clocks and denominators on every such root; a bad denominator would fail the certificate, not silently discard a candidate. In the D,D,D star the other two D clocks can be algebraic before reduction, but the defining monic \(\Delta\) puts every lift in the valuation ring and both residue roots are enumerated. The other phases recover their clocks rationally from the retained pivots. The paid residual-equation discrepancies above rule out any field extension, including a possible nonsplit graph. This use of a fixed simple good place proves a characteristic-zero conclusion only; it asserts no finite-characteristic census.

The separate [single-endpoint parity lemma](PARITY.md) gives additional exact centered/antipodal guards for the remaining S,D,D case.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_small_fibres.py` and `SYMPY_GROUND_TYPES=flint python check_good_places.py` with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticOneSingletonArithmetic.lean) covers the arithmetic leading numerator, literal third value, and quadratic product remainder identities. The rooted-order ingress, projections, residual fits and transfer are a paper proof with exact replay, not an end-to-end native theorem.
