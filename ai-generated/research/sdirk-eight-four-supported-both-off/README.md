# Four supported quadratic zeros need a zero on one actual third stage

Let a strict ten-stage SDIRK tableau with common nonzero diagonal $\gamma$ satisfy ordinary order at least eight over a field of characteristic zero or greater than seven. Write $c=A1$, $g=Ac-c^{\odot2}/2$, $C=\operatorname{diag}(c)$, $G=\operatorname{diag}(g)$ and $M=CA-AC-A^2$. Suppose exactly four physical $g_i$ vanish and that an actual supported degree-two column is
$$v=r(c)+\alpha g,\qquad \deg r\le2,\quad \alpha\ne0,\quad
v_i=0\ \text{when }g_i\ne0.$$
A *live* row has nonzero output weight, a *silent* row zero weight, and an *off-zero* row nonzero $g$; these are separate labels.

**Result.** At least one of physical stages 3 and 8 must be a quadratic zero. There are also at least two distinct live off-zero clocks and at least three distinct physical off-zero clocks. This closes the both-off-zero-third branch with or without silent rows, not the remaining zero-third chronologies nor the cases without the given graph.

## 1. Four Gaussian zero clocks and support census

On every off-zero row the residual is the nonzero graph $g=-r(c)/\alpha$. There are exactly six such rows. Group the live off-zero rows by clock. The six paid moments $b^{\mathsf T}C^jg=0$, $0\le j\le5$, and the Vandermonde at those groups imply every off-zero group has zero aggregate ordinary weight: its common nonzero graph value can be canceled from its mass. Thus the ordinary quadrature is carried entirely by the four literal zero rows. The invertible ordinary size-four Hilbert test requires four distinct live clocks there; ordinary nodal orthogonality identifies them as all four roots of $L_4$ (the fourth shifted Legendre polynomial), with their exact Gaussian weights. This argument also covers an off-zero clock equal to a separate zero clock.

Use the [saturated flag ranks](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) and the [two-sided restriction identity](../sdirk-eight-two-zero-line/README.md) in their paid-field form. For $U=\ker G$,
$$\dim(E_3\cap U)+\dim(W_2\cap U_{\rm row})=4.$$
The columns $v,Cv$ are independent in $E_3\cap U$: on the four distinct zero clocks they equal $r(c),c r(c)$ and a nonzero quadratic can vanish at at most two of them. Thus the supported reverse dimension is at most two. If there are no live off-zero clocks, the independent rows $b^{\mathsf T},b^{\mathsf T}C,b^{\mathsf T}C^2$ contradict this bound. If there is just one live off-zero clock, weighting $E_2$ into $W_2$ is injective (ordinary scalar probes detect the trace, and any live off-zero row detects the remaining pure line). The weighted map is onto by rank; its restriction to live off-zero rows has rank one, since the graph gives the same $(c,g)$ on that group. The supported reverse dimension would again be three. Hence there are $n=2$ or $3$ live off-zero clocks, each needing at least two live physical rows by zero aggregate weight.

Consequently $F_3=GE_1$ and $Z_3=W_1G$, clean at all physical zeros. The latter follows since the two distinct live off-zero clocks detect the two scalar rows of $W_1$. In either orientation the first two actual rows are off-zero. Forward $g_1=\gamma^2/2$, and a zero $g_2$ would make the actual first-edge identity localize all nonzero residuals to $\gamma$. At the rear all existing live quadratic weights give $Z_2=\langle b^{\mathsf T}G\rangle$, so the last weight (nonzero by trimming) and last residual are nonzero. The last two weights are nonzero and their clocks differ by the direct degree-one reverse-rank argument. If $g_9=0$, the clean grade-three row $(b^{\mathsf T}G)A$ would read $b_{10}g_{10}A_{10,9}\ne0$ at that zero, impossible.

A **silent physical stage 8** must be off-zero, since all four zero-residual rows have nonzero weights. The rows $b^{\mathsf T}A$ and $(b^{\mathsf T}G)A$ both vanish at its column: use the exact reverse degree-one identity and $Z_3=W_1G$. They read the two taps from rows 9,10. If $g_9\ne g_{10}$ both taps vanish, removing that column from every scalar reverse word and contradicting full rank. Thus $g_9=g_{10}$ and the actual reflected second-gap formula on the live two-row suffix forces $u_{\rm r}=2$. Also $A_{9,8}\ne0$ by the same column argument. The genuine $b^{\mathsf T}[A,M]=0$ read at column 8 then gives $c_8=2c_9-c_{10}$, by its literal second-subdiagonal coefficient. These deductions do not normalize the silent row or assume a globally defined reflected tableau.

## 2. Only two physical off-zero clocks are impossible

If exactly two physical off-zero clocks occur, they are both live somewhere. The first two and last two rows use both clocks. The actual first three forward clocks are pairwise distinct by the [first-three-stage identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md). Hence stage 3 is zero. A silent third at the rear would give the distinct arithmetic clock just proved, so the rear third is live, and its genuine reflected three-row equations likewise force it to be zero.

If $\gamma=1/2$, both ends start at the same literal off-zero clock and their second gaps are opposite. The common graph requires $\kappa(u)=\kappa(-u)$, where $\kappa(u)=1+2u-u^2$, contradicting $4u\ne0$. Otherwise the two clocks are $\gamma,1-\gamma$. Both ends have the same normalized second gap $u$, and their second graph ratios are reciprocal. Thus $\kappa(u)^2=1$. However both actual arithmetic zero thirds require $Q(u)=4u^3-12u^2+3u+2=0$. The exact identity
$$
(23u^3-70u^2+18u+48)Q(u)+
(-92u^2+188u-45)(\kappa(u)^2-1)=96
$$
excludes this in every paid field.

## 3. Three live paired clocks, both thirds off-zero

Assume now both physical thirds are off-zero. There must be six exterior off-zero rows, leaving the four Gaussian zeros in actual positions 4 through 7. If $n=3$ all six off-zero rows are live, in three pairs. The three graph clocks at each end are distinct and exhaust the same set. Both local normalized blocks exist, with each third either star (gap $w=2-u$, third residual ratio $\kappa(u)$) or arithmetic (gap $w=2u$, adjacent tap $tH(u)=2u(3u-2)$ with $H=-2+u+4u^2-u^3$).

If $\gamma=1/2$, the other two normalized forward gaps $x,y$ appear as $-x,-y$ after reflection. Two stars would require $x+y=2=-(x+y)$, impossible. A star opposed to an arithmetic phase requires the unordered star gaps $2/3,4/3$, whose common star residual ratio is $17/9$; the opposite arithmetic second gap $-2/3$ instead gives $-7/9$ at the same site. Two arithmetic phases require opposite second gaps at the same graph clock, contradicting $\kappa(u)=\kappa(-u)$. Thus $\gamma\ne1/2$.

Write $\lambda=(1-2\gamma)/\gamma$ and $z=(d-\gamma)/\gamma$ for the normalized gaps to the other fixed endpoint $1-\gamma$ and the third clock $d$. The two unordered forward gaps are $\{\lambda,z\}$, and the reflected ones $\{\lambda,\lambda-z\}$. The complete phase match is small:
* Forward star requires $z=2-\lambda$; forward arithmetic requires $z=2\lambda$ or $z=\lambda/2$.
* Reverse star requires $z=2\lambda-2$; reverse arithmetic requires $z=-\lambda$ or $z=\lambda/2$.

The only matches with $\lambda\ne0$ are two stars at $\lambda=4/3,z=2/3$, an arithmetic/star match there, or two arithmetic ends at $z=\lambda/2$. In the mixed case the arithmetic second gap is $2/3$, forbidden because its nonzero adjacent tap would have zero right side and $H(2/3)=4/27$. In the two-star case the forward equal-second-and-third residual and its reflected version together make all three graph residuals equal; then $\kappa(u)=1$ forces $u=2$ (since $u\ne0$), forbidden in a star. Thus there are two arithmetic ends, both with the middle graph clock $d=1/2$ and second gap $u=(1/2-\gamma)/\gamma$.

Their second ratios compare the same nonzero middle residual against the two endpoint residuals, so the endpoints have equal residuals. Thus the third ratio is 1. Its literal formula gives $t=2u-2$; substituting into the adjacent tap equation gives
$$(u-2)(u^3-3u^2+1)=0.$$
Normalize the centered graph trace to
$$ r_c(y)=R_0+R_2y^2,\quad y=2c-1,\quad
R_0=u(1+2u-u^2),\quad R_2=(u-2)(u+1)^2,\quad
\gamma=1/[2(1+u)].$$
This is the unique proportional graph on the three physical off-zero clocks. To obtain it, the endpoint value is normalized to $u$, and the midpoint value to $u\kappa(u)$; the centered endpoint is $s=2\gamma-1=-u/(1+u)$.

## 4. Gaussian anchors and a protected odd-subspace contradiction

Write $J$ for the centered primitive from $-1$ with derivative density $1/2$. Let $a,b_*$ be the actual first and last centered zero clocks. On the supported column, triangularity and $F_3=GE_1$ give $Jr_c(a)=\gamma r_c(a)$ (even when $r_c(a)=0$). Reflecting the supported weighted row gives $J^*r_c(b_*)=\gamma r_c(b_*)$, because $Z_3=W_1G$ is clean. These same statements hold in the silent case below; they never divide by the earliest or latest trace samples.

The four centered Gauss zero clocks are the roots of $L(y)=35y^4-30y^2+3$. For $u=2$ the first anchor forces $a=-2/3$, and $L(-2/3)=-277/81$. For the cubic gap $u^3-3u^2+1=0$, the denominator-cleared anchor is
$$
(1+u)[R_2(a^3+1)+3R_0(a+1)]-3[R_2 a^2+R_0]=0 .
$$
The nested resultants in $a$ and $u$ have stripped integer numerator $2014914997$, a prime certified by trial division. Thus the only possible characteristics are 277 and 2014914997. The complete splitting-field census of both the gap cubic and the Gauss quartic leaves, respectively,
* $u=2,\ a=184,\ b_*=93=-a$ in characteristic 277;
* $u=578011555,\ a=909066419,\ b_*=1105848578=-a$ in characteristic 2014914997.

All other ordered anchors fail even over nonsplit fields. The two intervening Gaussian nodes have centered clocks $y,-y$ with $y^2=6/7-a^2$; either order is allowed.

On the four-zero block, the actual supported columns with odd scalar traces $y r_c(y)$ and $y(y^2-s^2)$ belong to degree three. The latter vanishes at all three centered off-zero clocks $0,\pm s$. Their traces span the two-dimensional odd cubics because $r_c(\pm s)\ne0$, and their actual values on the zero rows are exactly their traces by $F_3=GE_1$ cleanness. Thus the two literal odd coordinate indicators on the mirrored Gauss pairs are real degree-three supported probes. For any two odd probes $H,K$ in that span, the original grade-seven pair is $I(H J K)=0$, because $J K$ is even. On the zero-block ordering $a,y,-y,-a$, the inner indicator's self-read gives $A_{6,5}=2\gamma$, and its read against the outer indicator gives $A_{6,4}=A_{5,4}$. The equal mirrored Gaussian weights are nonzero; no off-zero output weights enter these equations.

Subtract the reads of $A v$ at the two inner zero rows. The strict tap to the preceding outer zero cancels, giving
$$-(R_0 y+R_2 y^3/3)=2\gamma(R_0+R_2y^2).$$
This necessary equation implies the order-independent square pin
$$
y^2(R_0+R_2y^2/3)^2-(2\gamma)^2(R_0+R_2y^2)^2=0.
$$
Its exact residues in the two surviving prime-field scalar controls are **10** and **999087437**, respectively. This denies either ordering of the nonsplit inner roots and closes the three-paired-clock chart.

## 5. Independent silent-profile closure with both thirds off-zero

If $n=2$ and both thirds are off-zero, the last three cannot all be live: their distinct local clocks would require three live off-zero clocks. Hence stage 8 is silent, with $g_9=g_{10}$ and $u_{\rm r}=2$ as proved in Section 1. In original coordinates its clock is $1-5\gamma$, while the two live suffix clocks are $d=1-\gamma,e=1-3\gamma$. The first three off-zero rows must contain both live sites once, since each needs at least two live physical occurrences, and their clocks are distinct. The other front and rear off-zero sites are silent, each different from $d,e$. The two silent clocks may coincide or differ.

* **Coincident silent clocks.** Then the front first clock $\gamma$ is one of $d,e,1-5\gamma$, forcing $\gamma=1/2,1/4,1/6$. At $1/2$, the other two forward gaps are $-2,-4$, so only arithmetic with $u=-2$ is possible; the two live sites have equal residual by the rear read, but $\kappa(-2)=-7\ne1$. At $1/4$, gaps $2,-2$ pay neither phase. At $1/6$, gaps $2,4$ force uniform arithmetic and all three graph residuals equal. The graph is therefore constant, and all its literal clocks are the same three as in Section 4 at $u=2$. The anchored odd-block contradiction at 277 uses no off-zero weight and applies unchanged.
* **Different silent clocks.** If $\gamma$ is the front silent clock, the other two forward gaps are $\lambda,\lambda-2$ with $\lambda=1/\gamma-2$. A star would make one gap zero; either arithmetic orientation forces $1/\gamma=0$ or makes the two silent clocks equal. Thus $\gamma=d$ or $e$. At $\gamma=d=1/2$, $e$ cannot be physical second since its gap $-2$ gives $\kappa=-7\ne1$ against the equal live residual. If it is third, a star makes its residual ratio $-7$, and arithmetic requires $u=-1$ with third ratio $-17\ne1$. At $\gamma=e=1/4$, if the other live site $d$ is third, its gap 2 forces arithmetic $u=1$ (star would give $u=0$), with third ratio 3 rather than 1. If $d$ is second, its gap 2 forces uniform arithmetic, and the first three distinct graph values are equal; hence $r$ is constant. The front silent clock is then $5/4$, while the rear silent clock is $-1/4$.

In the last constant quarter-diagonal case normalize $v$ to the indicator of the four zero rows. Its outer zero clocks are precisely $\gamma,1-\gamma$ by the forward and reverse clean support reads. Let $P(X)=(X-\gamma)(X-(1-\gamma))$. The two genuine rows $b^{\mathsf T}P(C)$ and $b^{\mathsf T}CP(C)$ vanish at both live off-zero sites, at both silent rows, and at both outer zero rows. They span the coordinate rows of the two inner Gaussian zeros, because their weights and distinct clocks are nonzero. Hence $F_4=\operatorname{Ann}(W_3)$ is clean at these two actual zero rows. At the first inner zero with clock $x$ a strict tap $t$ reads only the preceding outer zero and its own diagonal in $Av$ and $A(Cv)$. Therefore
$$t+\gamma=x,\qquad 2(\gamma t+\gamma x)=x^2.$$
At $4\gamma=1$ these imply $(2x-1)^2=1/2$, whereas the two remaining Gauss roots, with outer squared clock $1/4$, have squared clock $6/7-1/4=17/28$. Their difference is the paid unit $3/28$. This excludes the independent two-ghost quarter-diagonal profile without enumerating any field coefficients.

## Domain and replay

The exclusion is for paid fields, with no positivity or real-number hypothesis. As a ring corollary the both-off-zero-third exclusion holds in a nonzero commutative ring if $8!$, $\gamma$, $\alpha$, and the six off-zero residuals are units: every maximal-ideal residue field retains that graph and the literal four-zero and third-row patterns. No condition on the output weights being units is needed because the field proof includes the silent cases. Nonunit residuals do not generally preserve that support on reduction.

Run `python check_norms.py` and `python check_fibers.py` with SymPy 1.14 and Python-flint 0.8. `RKCert.Research.SDIRKEightFourSupportedBothOff` checks the two-gap Bézout identity, the arithmetic and literal odd-block scalar implications, and the two finite nonzero residues. The full rank-to-chronology proof and exact geometric check are the source proof and replay, not a single native `HasOrder` impossibility theorem. Stock Lean/Mathlib 4.36.0 audit attached.
