# The last one-extra-D rear cannot overlap the front at the terminal clock

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, all literal quadratic defects nonzero, exactly seven distinct clocks, and precisely one singleton physical endpoint. The [scoped ledger](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a2-final/LEDGER.md) leaves two singleton labels at the front and one additional D and one S in the rear opening, orienting from the singleton. In that remaining topology, **the one known front D clock cannot equal the actual terminal D clock**. A known overlap with the other rear D, or no known overlap, is separate. The 10–11 stage interval is unchanged.

## Literal pair data and true affine factor

Normalize the diagonal to one, use \(y=x-1,\ H=2(m-1),\ m=1/(2\gamma),\ t=y-H/2\). The first singleton is \(0\), the terminal D clock is \(H\ne0\), and the other rear D clock is \(d\ne H\). Here the front D label equals \(H\); its two singleton labels are \(0,s\). The rear S is at \(t_s\), a distinct label not equal to \(0,s,H,d\). The genuine front and rear pairs use the [literal phase table](../sdirk-eight-all-dirty-seven-quadratic-sdd-one-extra-double-overlap/README.md): a given D offset \(z\) has its singleton partner at \(2z,z/2,2-z\) respectively for A2, A3, and star, with known corresponding defects \(\kappa(z)/2,N(z)/(2D(z))\) or the reversed arithmetic order at \(z/2\), and equal values in the star. Here \(\kappa(z)=1+2z-z^2\), \(D(z)=-2+z+4z^2-z^3\), \(N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2)\). This uses front D offset \(H\), rear offset \(H-d\), and the actual reflection \(y'=H-y\). Both true star row orders give these same consumed pair data by their respective literal formulas, not by an arbitrary reordering. Use the singleton front first-departure guard against literal gap two and all nonzero arithmetic/clock gates. The [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) forbids centered or antipodal D labels.

The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) gives \(\mathcal Q=L_3-F_*L_4\) proportional to \(P R\), with the genuine singleton graph \(R\) quadratic and \(P\) cubic on the D labels. Coprimality of consecutive centered Legendre modes \(L_j\), evaluated at \(t=y-H/2\), gives paid \(L_4(H),L_4(d)\ne0\). Fit the nonconstant affine \(F_*\) from their values \(L_3/L_4\), and divide exactly \(M_3=\mathcal Q/[(y-H)(y-d)]\). The [two paid S readings](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md#the-paid-affine-factor-recovers-the-quadratic-graph) give \(M_3=L R\) with
\[
 L=l_0+l_1 y,\qquad
 l_0=2M_3(0),\quad l_1=(M_3(s)/f_s-l_0)/s ,
\]
where \(f_s\) is the actual original defect at the later forward S. In an actual method \(l_1\ne0\) because \(L\) gives the remaining D root \(e=-l_0/l_1\). Thus
\[
 R=\tfrac12+a y+b y(y-s),\quad
 a=(f_s-\tfrac12)/s,\quad b=[y^3]M_3/l_1 ,
\]
with actual curvature \(b\ne0\). Comparing the quadratic coefficient gives
\[
 E=[y^2]M_3\,l_1-l_1^2 a-[y^3]M_3(l_0-l_1s)=0 .
\]
This is rank-safe even if \(a=0\), and assumes neither splitting nor that \(W,P\) have no common roots. Here \(W=R/b\). The original nonzero graph values at \(0,s,t_s\) also give \(M_3(0),M_3(s),M_3(t_s)\ne0\), since those are not doubled labels including \(e\).

## Actual overlap and two paid singleton equations

Let \(f_H\) be the actual front D defect, \(\rho_d,\rho_t\) the actual normalized reverse defects at \(d,t_s\), and \(\rho_H=1/2\). The rear singleton supplies the true normalization \(\lambda=R(t_s)/\rho_t\ne0\). At the literal overlapping D clock \(H\), the two paid residual roots are \(f_H,\lambda/2\), so the actual product fixes \(\beta=B\lambda=-2 L_4(H)/f_H\). There is **no second known overlap**. Write \(\lambda A_2=T_0+\lambda T_1\) with
\[
\begin{array}{c|cc}
 y&T_0&T_1\\\hline
 0&-\beta/2&2L_4(0)\\
 H&-\beta f_H&-\beta/2\\
 d&L_4(d)/\rho_d&-\beta\rho_d .
\end{array}
\]
These rows are paid by the first true S, the overlap's Vieta sum, and the other observed rear D. They determine the unique quadratic by distinct clocks. At the front S \(s\) and rear S \(t_s\) the actual equations therefore give
\[
 \begin{split}
 X={}& f_s T_0(s)+\beta f_s^2+\lambda\bigl(f_s T_1(s)-L_4(s)\bigr)=0,\\
 Y={}& \rho_t T_0(t_s)-L_4(t_s)+
               \lambda\bigl(\rho_t T_1(t_s)+\beta\rho_t^2\bigr)=0 .
 \end{split}
\]
No affine leading coefficient is inverted. There is no need to know the remaining singleton label or to divide by \(R\) at a D. The true distinct residual roots at the terminal overlap also give the guard \(\lambda/2-f_H\ne0\).

## Exact guard-safe contradictions

The verifier clears the integer numerators of \(E,X,Y\) with audited nonconstant denominator support only from true nonzero clock/phase guards, the two paid anchor Legendre values and the measured affine slope. It forms \(\operatorname{Res}_d(E,X),\operatorname{Res}_d(E,Y)\) separately, strips only proved nonzero \(H\)-guards and takes their gcd in \(H\). This permits zero specialized leading coefficients. The complete phase table is:

| Front / rear | Projected degrees | Irreducible \(H\) factor degrees |
| --- | --- | --- |
| A2 / A2 | 252,172 | 24 |
| A2 / A3 | 364,284 | 4,24 |
| A2 / star | 162,24 | none |
| A3 / A2 | 149,119 | 13 |
| A3 / A3 | 195,165 | 13 |
| A3 / star | 102,72 | 13 |
| star / A2 | 162,118 | 15 |
| star / A3 | 238,194 | 15 |
| star / star | 99,24 | none |

All eight nonconstant factors appear with multiplicity one. In every corresponding exact irreducible \(H\)-field the three specialized \(d\)-rows have linear gcd; true \(H,d\) guards remove it completely. This exact check over the abstract fields covers all their embeddings and arbitrary extensions. No sign, ordering, local field extrapolation, trace or actual fourth read is used.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_terminal_overlap.py` with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSOneExtraTerminalOverlap.lean) verifies the denominator-free singleton scale identities. The rooted-order and polynomial elimination proof is mathematical with exact replay, not fully native Lean. No statement in positive characteristic is made.
