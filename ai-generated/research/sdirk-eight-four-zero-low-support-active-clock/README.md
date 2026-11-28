# Four quadratic zeros: the low-support active-clock exclusions

Consider a strict ten-stage SDIRK tableau $A,\mathbf b$ of ordinary order at least eight over a field of characteristic zero or greater than seven. Write $\gamma\ne0$ for its common diagonal, $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. A *zero* below means a physical row with $g_i=0$, even if its weight vanishes. An *active off-zero clock* has at least one physical stage with both $b_i\ne0$ and $g_i\ne0$ at that clock. Its aggregate is the sum restricted to its off-zero stages, not the total weight of all stages at that clock.

**Result.** In the exactly-four-zero case, two different active off-zero clocks are impossible. So is one active off-zero clock with nonzero aggregate. There is no assertion here about one active clock with zero aggregate, or no active off-zero clocks.

## 1. Common flag reductions

The [genuine-graph](../sdirk-eight-four-supported-paired-zero/README.md) and [pure-polynomial](../sdirk-eight-four-pure-polynomial/README.md) exclusions give $E_2\cap U=0$. Alternatively take this as a hypothesis for the new calculations. In the [saturated flags](../clock-localized-tail/tied-stage-floor/README.md), $E_j,W_j$ denote forward and reverse columns and rows through grade $j$, with pure subspaces $F_j,Z_j$. Profiles are literal polynomials, with forward primitive $J f(X)=\int_0^X f(t)\,dt$ and reverse primitive $J^*f(X)=\int_X^1 f(t)\,dt$; integration here just means a polynomial operation using the paid denominators. The [two-sided support identity](../sdirk-eight-two-zero-line/README.md) is
$$\dim(W_j\cap U_{\rm row})=4-\dim(E_{5-j}\cap U),\qquad
U_{\rm row}=\{\mathbf r^{\mathsf T}:\mathbf r^{\mathsf T}G=0\}.$$
At $j=3$ this gives every literal zero-row coordinate functional in $W_3$, and the off-zero restriction of $W_3$ has rank two. Consequently there are at most two distinct active off-zero clocks by the Vandermonde test on $\mathbf b^{\mathsf T}C^j$, $j=0,1,2$.

Every physical zero clock $a$ is Gaussian. In fact the corresponding coordinate row has a profile $f$ of degree at most three; it is nonzero since the row pairs to 1 with $\mathbf 1$. Its pairings with $(C-aI)C^k\mathbf1$ for $0\le k\le3$ give the four vanishing moments of $(X-a)f(X)$. By the size-four Hilbert matrix, this nonzero polynomial is proportional to the monic shifted fourth Legendre polynomial $L_4$. Thus $L_4(a)=0$. The centered polynomial is $35Y^4-30Y^2+3$, $Y=2X-1$. Its roots are simple, and none equals $0,1$ in uncentered time or $1/2$ in uncentered time.

Also $F_4=GE_2$ is clean on $U$ by injectivity and dimension. This forces every zero to have physical index at least five, as in the [earlier literal prefix argument](../sdirk-eight-three-zero-silent/README.md): at clock $a$, the first three scalar columns read by $\mathbf e_i^{\mathsf T}A^j$, $0\le j\le2$, have determinant $-a^6/72$, while these reads all kill $\mathbf g$. The first four columns $\mathbf1,\mathbf c,\mathbf c^{\odot2},\mathbf g$ are consequently independent on the actual prefix, since $g_1=\gamma^2/2\ne0$. They are annihilated by the nonzero prefix row $\mathbf e_i^{\mathsf T}M$, where $M=CA-AC-A^2$ and $M_{ii}=-\gamma^2$. The prefix needs at least five coordinates.

The final two weights are nonzero and their clocks differ: the terminal weight cannot be dropped at this stage floor; $D(1)$ gives $b_{10}A_{10,9}=b_9(1-c_9-\gamma)$ and $c_{10}=1-\gamma$. If either $b_9=0$ or $c_9=c_{10}$, the strict tap $A_{10,9}$ is zero, and the two terminal coordinates cannot be separated by the full reverse flag. If any active off-zero stage exists, the nonzero pure row $\mathbf b^{\mathsf T}G$ spans $Z_2=\langle\mathbf b^{\mathsf T}M\rangle$. Its terminal coefficient must therefore be nonzero. At the last actual weighted stages, the literal reflected tableau uses the reversed weighted transpose only on its consecutive live suffix. The reverse quadratic defect there is proportional to $g_i$: $D(1)$ gives $(\mathbf b^{\mathsf T}M)_i=-2b_i g_i^{\rm rev}$. The proportionality follows from the preceding pure-line identity. No division by a silent weight or transpose of the full tableau is used.

## 2. Two distinct active off-zero clocks

Call the two clocks $d,e$. The two independent restrictions of $\mathbf b^{\mathsf T},\mathbf b^{\mathsf T}C$ already span the rank-two off-zero restriction of $W_3$, so the restriction of $\mathbf b^{\mathsf T}G$ forces the residual constant within each active off-zero clock group. The paid $\mathbf g,C\mathbf g$ moments then make the two ordinary aggregates separately zero. Ordinary quadrature still has at least four distinct active abscissae by Hilbert rank, so all four zero rows are active and distinct. They are all four Gauss sites.

Now $Z_3=W_1G$, since the two distinct active off-zero clocks detect both affine profiles. A zero at stage 9 would make $(\mathbf b^{\mathsf T}G A)_9=b_{10}g_{10}A_{10,9}\ne0$, contradicting cleanliness of $Z_3$ at zeros. Thus both last stages are off-zero and the four zeros are precisely stages 5–8. At least two active stages are needed at each of $d,e$ to cancel its weight. There are at most two silent off-zero stages, and all silence is among the first four. The first three physical clocks are distinct by the [literal first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md), so at least one of them is silent. If there were just one silent stage, stage 4 would repeat the clock and residual of an earlier live stage $j$. Its first three primitive reads $A\mathbf1,A\mathbf c,A\mathbf c^{\odot2}$ agree with stage $j$, since $F_3=GE_1$. Merge the equal-clock basis entries at indices $j$ and 4 in these three literal linear observations. The Vandermonde matrix of the first three clocks makes the coefficient rows identical after the merge, so $A_{4j}=0$ and the other strict coefficients of row 4 equal those of row $j$. Recursing on rooted profiles, stages 4 and $j$ are literal twins, contrary to the full forward flag. Thus there are exactly two silent stages among the first four, with one active front stage at each of $d,e$.

Orient the terminal clock as $d=1-\gamma$ and stage 9 as $e=d-\gamma v$, $v\ne0$. The reflected three-row prefix is live, has a nonzero second defect, and has a zero third defect. The [literal zero-third equation](../sdirk-eight-three-zero-d2zero-paid/README.md) gives
$$Q(v)=4v^3-12v^2+3v+2=0,\quad
g_9/g_{10}=\kappa(v)=1+2v-v^2\ne0,\quad c_8=1-\gamma(1+2v).$$

### Two consecutive supported reverse reads

Use reflected normalized time $t=(1-c)/\gamma$ and write $B=1+2v$ for the time at physical stage 8. The two supported $W_2$ rows are
$$\mathbf b^{\mathsf T}r((I-C)/\gamma),\qquad
\mathbf b^{\mathsf T}\big[p((I-C)/\gamma)-G/g_{10}\big],$$
where $r(t)=(t-1)(t-1-v)$, $p(t)=1+(2-v)(t-1)$. They vanish at every physical off-zero stage, either by the interpolated residual ratio or because its weight is zero. At the next preceding zero stage 7, with time $h=(1-c_7)/\gamma$, applying $A/\gamma$ on the right reads only the common diagonal and the tap from stage 8. The grade-three pure row is zero there. Cancel the nonzero weight at stage 7; the two legitimate equations have a common tap multiplier on $r(B)$ and $p(B)$. Eliminating that multiplier without dividing gives
$$\Psi(h)=0,\qquad
\Psi(t)=r(B)(Jp-p)(t)-p(B)(Jr-r)(t).$$
Here $J$ is the primitive in $t$, since $J^*$ in the original time divided by $\gamma$ becomes $J$ after the change of variable.

Let $y=1-2c_8$, $z=1-2c_7$. Both are distinct centered Gauss roots, so $h=B(1+z)/(1+y)$ and $\gamma=(1+y)/(2B)$, with all these denominators nonzero. Reduce the coefficients of $\Psi$ by the monic $Q/4$, and homogenize by $(1+y)^3$ to form the projection in $v,y,z$. For a mirror Gauss pair substitute $z=-y$. Otherwise $z^2+y^2=6/7$, so take a resultant in $z$ against that monic quadratic. Next take resultants in $y$ against the monic centered Gaussian quartic and in $v$ against $Q/4$. The exact norm values are
$$
-\frac{2^{34}3^7\cdot1265639}{5^9 7^9},
\qquad
\frac{2^{80}3^{14}\cdot1174307\cdot263949107}{5^{18}7^{36}}
$$
for mirror and nonmirror pairs respectively. All arithmetic and reductions use only paid denominators. These fixed polynomial operations prove that every actual characteristic must divide one numerator, even for an extension-field root. Trial division through the three square-root bounds verifies all three nonpaid factors are prime.

### The actual fifth-row clock equation

In each possible characteristic the complete common splitting field of the cubic $Q$ and the Gauss quartic has degree 2 over its prime field. Factoring both there and testing all directed distinct Gauss pairs leaves precisely these residues, all in their prime fields:

| Prime | $v$ | $y$ | $z$ | $\gamma$ | $d$ | $e$ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1265639 | 271082 | 143450 | 1122189 | 384363 | 881277 | 721186 |
| 1174307 | 534271 | 925539 | 819552 | 61751 | 1112557 | 324894 |
| 263949107 | 125965887 | 168410348 | 77082229 | 144027915 | 119921193 | 215819840 |

In all three $\gamma\notin\{d,e\}$, so stage 1 is silent. Placing the two front active stages at ordered distinct slots in $\{2,3,4\}$ and choosing the literal star or arithmetic phase determines the initial normalized gap $u=(c_2-\gamma)/\gamma$: at least one active slot is 2 or 3, whose prescribed clock determines $u$. Retain only the nonzero pure residuals and exact clock/residual-ratio incidences on the first three physical rows. In each characteristic this leaves eight reads, all with a mandated active clock at stage 4.

Use normalized forward clock $x=c/\gamma$ and residual $\eta=g/\gamma^2$. Let $P$ be the unique quadratic interpolating $\eta$ through the first three literal normalized rows, and let $a=c_5/\gamma$ be either of the two as-yet unused Gaussian zeros. The columns $\boldsymbol\eta-P(\mathbf x)$ and $X(\boldsymbol\eta-P(\mathbf x))$ (the latter means coordinate multiplication by $\mathbf x$) are zero on the first three rows. Their values at stage 5 are $-P(a)$ and $-aP(a)$. Clean grades three and four give
$$
D=P(a)-JP(a)= (A_{54}/\gamma)(\eta_4-P(x_4)),\qquad
N=aP(a)-J(XP)(a)= (A_{54}/\gamma)x_4(\eta_4-P(x_4)).
$$
Every actual row must therefore pay $x_4 D=N$. For primes in table order the 16 candidates divide into $0,4,4$ cases of $D=0$ with $N\ne0$, and $16,12,12$ cases of $D\ne0$ with the prescribed $x_4$ violating the equation. No $D=N=0$ case is removed by division or left unresolved. Thus two distinct active off-zero clocks cannot occur.

## 3. One active off-zero clock with nonzero aggregate

Let $d$ be this sole clock; the moment $\mathbf b^{\mathsf T}L_4(C)\mathbf1=0$ forces $L_4(d)=0$ because all four physical zero clocks are Gaussian and the off-zero aggregate is nonzero. Thus stage 10 is at $d=1-\gamma$, with $d\ne1/2$, and active stage 9 is at a different clock $z$ and must be zero. The supported reverse row $\mathbf b^{\mathsf T}(C-dI)$ at column 9 gives
$$
(1-z^2)/2-d(1-z)-(1-d)(z-d)=0.
$$
This is exactly the [previous directed Gaussian pair calculation](../sdirk-eight-three-zero-d2zero-paid/README.md), including its denominator exception. The only paid geometric pairs $(d,z)$ are $(7,11)$ in characteristic 17, $(97,30)$ in characteristic 103, and $(6924,2220)$ in characteristic 7793.

The next literal clock $c_8$ is either $4d-z-2$ or $2z-d$. With a nonzero weight at stage 8 this is the three-row reflected identity. If that stage is silent, $A_{9,8}$ cannot vanish: by $D(1)$ that would also make $A_{10,8}=0$ and this silent coordinate unobservable. The pure row $\mathbf b^{\mathsf T}[A,M]$ vanishes on the last two coordinates by strict triangularity, hence is zero because $Z_3=W_1M$ is detected on those two coordinates. The entry at column 8 then gives $c_8=2z-d$ directly. At the three verified pairs neither proposed clock is Gaussian or equal to $d$, so row 8 must be a silent off-zero.

The first three literal clocks are distinct and are all off-zero, so at least two of them must also be silent. But a nonzero off-zero aggregate at $d$ needs at least four distinct active residual values, by the three paid residual power moments $\mathbf b^{\mathsf T}G^j\mathbf1=0$, $j=1,2,3$: a product of at most three linear factors killing all those nonzero residuals would give a nonzero constant times the aggregate. Six physical off-zero rows can afford at most two silent ones. This contradiction does not rely on distinctness or activity of all four zero clocks.

## 4. Current exactly-four-zero census and verification

| Exactly-four-zero stratum | Status over paid fields |
| --- | --- |
| A supported $E_2$ column has nonzero $\mathbf g$ coefficient | Excluded in the [genuine-graph packet](../sdirk-eight-four-supported-paired-zero/README.md) |
| Nonzero supported pure-polynomial $E_2$ column | Excluded in the [pure-polynomial packet](../sdirk-eight-four-pure-polynomial/README.md) |
| $E_2\cap U=0$ and at least two active off-zero clocks | More than two impossible by rank; two excluded here |
| $E_2\cap U=0$, one active off-zero clock with nonzero aggregate | Excluded here |
| $E_2\cap U=0$, one active off-zero clock with zero aggregate, or none | Not decided by these packets |

No real or ordered-field hypothesis is used. These are not an unconditional four-zero exclusion or a ten-stage lower bound. The field statements also apply after reduction at any maximal ideal for which the six physical off-zero residuals, paid factorial, and common diagonal are units and the reduced clock/weight strata satisfy the stated hypotheses. For example, with two prescribed off-zero active clocks, their difference and one witness weight at each can be assumed units to preserve the two clocks if every other off-zero stage is silent or has one of the two prescribed clocks. In the one-clock case, a unit off-zero aggregate preserves that hypothesis. A merely nonzero coefficient in a ring need not survive reduction.

Run `python check_norms.py` and `python check_fibers.py` with SymPy 1.14 and Python-flint 0.8, and the linked Gaussian-pair replay for Section 3. The native Lean module `RKCert.Research.SDIRKEightFourZeroLowSupportActiveClock` checks the consecutive reverse read elimination, fifth-row clock cross-product, cubic factorization, and literal norm factorizations. The flag reduction, exact resultant arithmetic, geometric fiber enumeration, and chronology are the mathematical/replay parts, not a single Lean `HasOrder` exclusion. The supplied axiom audit was checked with stock Lean/Mathlib 4.36.0.
