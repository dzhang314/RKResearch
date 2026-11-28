# Five physical quadratic zeros, pure support, and only four ordinary sites

Let $A,\mathbf b$ be a strict ten-stage SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven. Write $\gamma\ne0$ for the common diagonal, $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. Suppose exactly five literal residuals vanish, **all off-zero stages are silent**, and the unique supported grade-two column is a pure quadratic in the clocks, as in the [support-rank classification](../sdirk-eight-five-zero-support-rank/README.md).

**Result.** Four distinct nonzero ordinary clock aggregates are impossible in this chart, over every paid field. An actual tableau in the chart would therefore have five distinct live zero clocks. This result does not exclude that five-ordinary-site stratum, graph support, or activity at an off-zero clock.

## 1. Front and rear chronology

The exactly two physical off-zero clocks are $d,e$ and the supported trace is $r(X)=(X-d)(X-e)$. The first forward stage is off-zero with clock $\gamma$. The actual second gap cannot have $\kappa(u)=0$ since the [pure transition identity](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) would localize all off-zero clocks to $\gamma$. Thus both first two physical stages are off-zero and exhaust $d,e$, with
$$d=\gamma,\quad e=\gamma(1+u),\quad u\ne0,\quad \kappa(u)\ne0.$$
The first three literal clocks are distinct. Stage 3 is therefore zero, in the arithmetic third-zero phase, and
$$a=c_3=\gamma(1+2u),\qquad Q(u)=4u^3-12u^2+3u+2=0.$$

Assume now that ordinary quadrature has exactly four distinct active aggregates. By moment rank and orthogonality of the nodal polynomial these four sites are the four distinct roots of
$$L(X)=70X^4-140X^3+90X^2-20X+1.$$
With only five zero rows there is at most one duplicated site among live weights, and none of the four aggregate-supported Gauss sites can be lost. In particular any live zero row is Gaussian: a non-Gaussian live row would have to cancel with another live row at that very clock, leaving at most three others, not four needed ordinary Gaussian sites.

The final two physical weights are nonzero, their clocks are distinct, and $c_{10}=1-\gamma$. They are Gaussian zeros. Thus $\gamma$ is also Gaussian by reflection. If stage 8 is live its clock is Gaussian too; if it is silent the literal cubic reverse ghost gate holds regardless of its residual. These are exactly the rear scalar charts in the [native Gaussian rear characteristic projection](../sdirk-eight-four-zero-native-rear/README.md). No such chart survives characteristic zero, and in paid positive characteristic the characteristic must divide
$$P_{\rm rear}=37\cdot269\cdot379\cdot397\cdot487\cdot69877
=50962055131435661.$$
The rear conclusion uses only the two/three specified Gauss sites and the literal suffix, not the older exactly-four-zero hypothesis.

## 2. Two exhaustive front charts

If $a=c_3$ is Gaussian, it follows from $L(\gamma)=L((1+2u)\gamma)=Q(u)=0$ that the nested resultant
$$N_A=\operatorname{Res}_u\!\left(\operatorname{Res}_x(L(x),L((1+2u)x)),Q(u)\right)$$
vanishes in the coefficient field. Its exact integer value is
$$N_A=2^{57}5^{12}7^6(3517)(10759456151).$$
It is coprime to $P_{\rm rear}$.

If $a$ is not Gaussian, stage 3 must be the unique silent zero row, and the other four zero stages are distinct live Gaussian sites. The forward pure grade-four restriction to $U$ has dimension at most one: $GE_2$ has dimension three because $\dim(E_2\cap U)=1$, is contained in the four-dimensional $F_4$, and vanishes on $U$. The column $L(\mathbf c)$ belongs to $F_4$ by its ordinary orthogonality against all grade-three reverse scalar profiles, and is nonzero on $U$ since $L(a)\ne0$. The whole pure grade-four restriction is therefore the line it spans, and is clean at the four live Gaussian rows.

The supported cubic $(C-aI)r(\mathbf c)$ vanishes at the silent zero and at every off-zero stage. At the chronologically first live zero with clock $s$, its primitive read is exact by the preceding cleanliness, and its actual action is only the diagonal. Thus
$$
(J[(X-a)r])(s)=\gamma(s-a)r(s).
$$
Normalize time $T=X/\gamma$, put $R(T)=(T-1)(T-1-u)(T-1-2u)$, and define $G(T)=12(JR(T)-R(T))$, where $J$ is now the normalized primitive from zero. The necessary identity is $G(s/\gamma)=0$. It does not divide by a value of $r$ or by a tap.

If $s=\gamma$, the resultant of $G(1)=-12u^2-12u-3$ and $Q(u)$ equals $-2^6 3^5$. In particular those polynomials are incompatible at every paid characteristic. The integral Bézout combination giving 9 is also checked in Lean.

If $s\ne\gamma$, use the polynomial divided difference $D(x,y)=(L(y)-L(x))/(y-x)$, which vanishes at the two distinct Gaussian roots. Homogenize the primitive gate, $F(x,y,u)=x^4G(y/x)$, of degree four in the two time variables. Taking resultants against $D$ in $y$, $L$ in $x$, and $Q$ in $u$ gives
$$
N_B=2^{112}3^{45}5^{48}7^{25}
(853)(9453064485587)(77302364448451)(12847924825634167528081).
$$
This number is also coprime to $P_{\rm rear}$. The argument does not require any of the large displayed factors to be prime; the exact gcd with the independently known rear product suffices.

All projections are fixed integer polynomial resultants, so an actual algebraic root over *any extension* forces the same integer to vanish after reduction. There is no conclusion drawn from testing only prime field roots, and no unexamined geometric finite fiber: in every allowed rear characteristic the necessary front integer remains nonzero. The coprime front and rear conditions are impossible simultaneously.

## 3. Replay and domain

Run `python check_norms.py` with SymPy 1.14. It recomputes the displayed resultants, verifies their exact factorizations, then checks all three integer gcds against the rear product. `RKCert.Research.SDIRKEightFiveZeroPureFourOrdinary` checks the coincident Gaussian Bézout identity over a commutative ring and the exact integer coprimalities by kernel reduction. The full stage-flag ingress and the symbolic resultant computation remain the source mathematical proof and exact replay, not one native `HasOrder` theorem. Stock Lean/Mathlib 4.36.0 audit attached.
