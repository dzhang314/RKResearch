# Exactly four quadratic zeros are excluded over characteristic-zero fields

Let $A,\mathbf b$ be a ten-stage strict SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven. Put $\mathbf c=A\mathbf 1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and let $\gamma\ne0$ be the common diagonal. A zero means a *literal stage* with $g_i=0$, even if $b_i=0$.

**Combined result.** Exactly four physical zeros are impossible over **every characteristic-zero field**. No ordering, positivity, or real embedding is needed. Over paid positive characteristics the combined exclusions leave only the two specified finite rows of the census below. They are necessary possibilities, not constructed tableaux. This does not exclude every ten-stage strict SDIRK8 tableau.

By the [genuine-graph](../sdirk-eight-four-supported-paired-zero/README.md), [pure-polynomial](../sdirk-eight-four-pure-polynomial/README.md), and [active off-clock](../sdirk-eight-four-zero-low-support-active-clock/README.md) results, a remaining exactly-four-zero tableau has $E_2\cap\ker G=0$ and either no active off-zero clock ($n=0$) or one such clock with zero aggregate ($n=1$). The forward degree-four pure defect space $F_4=GE_2$ is clean on every zero. Each zero clock is Gaussian and all zeros are at indices at least five, as proved in the active off-clock packet. Since all ordinary off-zero weights aggregate to zero, the ordinary size-four Hilbert rank forces all four zero rows to have nonzero weights and distinct clocks. They are all four roots of
$$L(x)=70x^4-140x^3+90x^2-20x+1.$$
Reflection $x\mapsto1-x$ permutes these four roots. The last two physical weights are nonzero, their clocks differ, and $c_{10}=1-\gamma$.

## 1. A literal reverse gate when stage 8 is silent

Set $M=CA-AC-A^2$, $N=A-\gamma I$, $\widetilde C=I-C$, and $\mathbf z^{\mathsf T}=-\mathbf b^{\mathsf T}M/2$. In the saturated reverse flags the pure grade-two line is spanned by $\mathbf z^{\mathsf T}$ and the pure grade-three space $Z_3$ is detected on the last two components: $\mathbf z^{\mathsf T}$ has nonzero terminal component and $\mathbf z^{\mathsf T}N$ is zero there but nonzero at column 9. Indeed $D(1)$ gives
$$b_{10}A_{10,9}=b_9\gamma v,\qquad v=(c_{10}-c_9)/\gamma\ne0.$$
The ordinary formula for the actual normalized reverse second defect gives
$$z_{10}=b_{10}\gamma^2/2,\qquad z_9=b_9\gamma^2\kappa(v)/2,\qquad \kappa(v)=1+2v-v^2.$$
This follows directly from $\mathbf b^{\mathsf T}A=\mathbf b^{\mathsf T}(I-C)$ and $\mathbf z^{\mathsf T}=\mathbf b^{\mathsf T}\widetilde C A-\mathbf b^{\mathsf T}\widetilde C^2/2$, without assuming every weight is live. In $Z_3$ the last two components therefore prove the global identity
$$\mathbf z^{\mathsf T}(\widetilde C-\gamma I)=\kappa(v)\mathbf z^{\mathsf T}N.$$
They also prove $\mathbf b^{\mathsf T}[A,M]=0$: this row is pure of grade three and its last two components vanish since $[A,M]=[N,M+\gamma^2 I]$ is a commutator of strictly lower triangular matrices.

If $b_8=0$, then $A_{9,8}\ne0$. Otherwise $D(1)$ gives $A_{10,8}=0$ too, and column 8 is unobservable on all reverse words, contrary to the full reverse flag. The column 8 entry of the commutator gives $c_8=2c_9-c_{10}$. Now $D(1)$ on that silent column says $b_{10}A_{10,8}=-b_9 A_{9,8}$, so
$$z_8=\gamma v b_9 A_{9,8},\qquad
(\mathbf z^{\mathsf T}N)_8=\gamma^2(\kappa(v)-1)b_9 A_{9,8}/2.$$
Insert both into the global pure relation and cancel nonzero terms. This gives
$$4v^2=\kappa(v)(\kappa(v)-1),\qquad H(v)=-2+v+4v^2-v^3=0.$$
The latter uses $\kappa(v)(\kappa(v)-1)-4v^2=-v H(v)$. In particular a silent third reverse row is impossible when $\kappa(v)=0$. No normalization by $b_8$ occurs.

If $b_8\ne0$, the first three literal weighted-transposed rows can instead all be normalized. This is just a local suffix of the original tableau, not a general transpose-preserves-order claim. Let $w=(c_{10}-c_8)/\gamma$ and let $r$ be the normalized strict reverse tap from the second to third stage. The same pure-row identities give
$$
r v(2v-w)=0,\quad w q=\kappa(v)[w+r(\kappa(v)-1)],\quad
q=1+2w-w^2+2rv.
$$
If $r\ne0$, $w=2v$ (arithmetic). If $r=0$, $w=0$ or $w=v$ would make a literal reverse twin (identical normalized row incidence and clock), violating the full reverse flag. Then $q=\kappa(v)$ gives $(w-v)(2-w-v)=0$, so $w=2-v$ (star). The phase alternative and distinctness remain valid even at $\kappa(v)=0$.

## 2. No active off-zero clock

Stage 10 and stage 9 are two live Gaussian zeros. Let their reflected clocks be $x=1-c_{10}=\gamma$ and $y=1-c_9$. Thus $x\ne y$, $x\ne0$, and $v=(y-x)/x$. If stage 8 is silent, its necessary gate is $H(v)=0$. If it is live, its reflected clock must be a third distinct Gaussian root, either $s=2y-x$ (arithmetic) or $s=4x-y$ (star).

Use the two integral divided differences
$$D(X,Y)=\frac{L(Y)-L(X)}{Y-X},\qquad
B(X,Y,S)=\frac{D(X,S)-D(X,Y)}{S-Y}.$$
They are polynomials with integer coefficients; at distinct roots of $L$ both appropriate divided differences vanish. For the silent case take the resultant of $D(x,y)$ and $x^3H((y-x)/x)$ in $y$, then against $L(x)$ in $x$. For the live cases replace the silent gate by $B(x,y,s)$ at the respective candidate $s$. This excludes spurious coincidences of the third Gaussian clock with either of the first two, without any division in the resultant calculation. The absolute resultant values in order silent, arithmetic, star are
$$
2^{17}5^{13}7^6(397)(487)(69877),\quad
2^{30}3^6 5^{24}7^{16},\quad
2^{30}5^{20}7^{16}37^2 269^2 379^2 .
$$
In particular no such case occurs in characteristic zero, and no paid characteristic permits the live arithmetic case. All geometric fibers at the six remaining primes are enumerated by splitting the whole quartic. The necessary reflected prefix is:

| Characteristic | Stage 8 | $\gamma=x$ | Possible $y$ |
| --- | --- | ---: | --- |
| 397 | silent | 162 | 218 |
| 487 | silent | 144 | 344 |
| 69877 | silent | 46321 | 58162 |
| 37 | live star | 28 | one conjugate pair in $\mathbb F_{37^2}$ |
| 269 | live star | 212 | 252 or 58 |
| 379 | live star | 212 | 168 or 301 |

For the silent controls the third reflected clock is $2y-x$, not a claimed Gaussian root. At 37 and 487 the base field must contain the quadratic Gaussian splitting field, since all four Gaussian zero nodes are required.

## 3. One canceled active off-zero clock

Let $d$ be the sole active off-zero clock, which has zero aggregate. The nonzero pure grade-two row $\mathbf b^{\mathsf T}G$ implies $\mathbf z^{\mathsf T}$ is proportional to it. Thus $d=c_{10}$, and the live stage 9 at a different clock is a zero with $z_9=0$. Hence $\kappa(v)=0$, where $v=(c_{10}-c_9)/\gamma$. The silent-eighth gate is impossible. The actual live stage 8 also has a distinct clock from $d$, so it is zero. These are two distinct Gaussian nodes. Put $x=1-c_9$ and $y=1-c_8$; then
$$
\frac{y}{x}=\frac{1+2v}{1+v}\ \text{(arithmetic)}
\quad\hbox{or}\quad \frac{y}{x}=\frac{3-v}{1+v}\ \text{(star)},
\qquad v^2-2v-1=0 .
$$
Both $x$ and $1+v$ are nonzero on this chart, and $x=\gamma(1+v)$. Clear the cube of $1+v$ in $D(x,y)$ under each substitution. Taking the two successive resultants against $L$ and $v^2-2v-1$ gives absolute numerators
$$ 2^8 5^8 7^5(17)(103)(7793),\qquad
2^{30}5^8 7^4(13)^2(131)^2 .$$
Thus characteristic zero is again excluded. The complete paid fibers are:

| Characteristic | Rear phase | $\gamma$ | Number of geometric controls |
| --- | --- | ---: | ---: |
| 13 | star | 10 | 2 conjugates |
| 17 | arithmetic | 3 | 1 |
| 103 | arithmetic | 38 | 1 |
| 131 | star | 34 | 2 conjugates |
| 7793 | arithmetic | 2485 | 1 |

In all five $d=1-\gamma$ is not Gaussian and $\gamma\ne d$. At 13, 17 and 131 the coefficient field must contain the quadratic Gaussian splitting field, even though the pair determining $\gamma$ at 17 lies in the prime field.

### A varying residual at the canceled clock is impossible

The first three physical stages are off-zero and have distinct clocks, so at least two are silent. There are at most four live off-zero rows, all at $d$. If there were $k=2,3,4$ distinct residual values on these live off-zero rows, their paid residual moments of degrees 0–3 would force each residual-level group's weight to cancel; degree zero uses the aggregate-zero hypothesis. Each distinct value then consumes at least two live rows. A varying residual therefore means exactly two values, each appearing twice with opposite weights. There are exactly two silent off-zero stages, both in the first three; since $\gamma\ne d$ the early live row is stage 2 or 3. Stage 4 is live at $d$, and one of stages 5, 6, 7 is live at $d$ as well; the other two are zero.

If stage 5 is off-zero it repeats one residual pair from the earlier two live rows at $d$. As in the earlier literal twin argument, stage 4 could not already have repeated the earlier live pair: the three independent scalar clock probes make it a literal twin. Therefore the first four evaluation rows of $\mathbf1,\mathbf c,\mathbf c^{\odot2},\mathbf g$ are independent: the first three have distinct clocks and the fourth repeats a clock with a different residual. For stage 5 the four primitive reads of these columns have exactly the same outputs as at the repeated earlier pair, since $F_3=GE_1$. Merge the equal pair before applying the invertible four-evaluation matrix. The common diagonal gives zero tap to the repeated stage, and all other strict taps agree with the earlier live stage. Again there is a literal rooted twin, impossible.

Otherwise stage 5 is the first zero. Normalize by $\gamma$ as in the [fifth-row clock test](../sdirk-eight-four-zero-low-support-active-clock/README.md). Pin $d/\gamma$ at the actual live stage 2 or 3 in each forward star or arithmetic phase; this determines the first three normalized clocks and residuals. Interpolate their quadratic $P$, and try either of the remaining Gauss nodes for the first zero at normalized clock $a$. Stage 4 is live at $x_4=d/\gamma$, so the necessary identity is
$$
(d/\gamma)(P(a)-JP(a))=aP(a)-J(XP)(a).
$$
This equation never holds at any of the five complete geometric controls, including any possible vanishing coefficient of $d/\gamma$. The numbers of exact tests are $8,8,8,16,8$ respectively in the table order. The one-canceled-clock case must therefore have a constant nonzero residual across its live off-zero rows.

## 4. Scope and replay

| Remaining paid-positive-characteristic stratum | Necessary characteristic |
| --- | --- |
| No active off-zero clock, stage 8 silent | 397, 487, 69877 |
| No active off-zero clock, stage 8 live star | 37, 269, 379 |
| One canceled active off-zero clock, constant live residuals | 13, 17, 103, 131, 7793 |

The previous packets and the present result jointly exclude exactly four physical zeros over every characteristic-zero field and every paid field not in the table. At the exceptions the appropriate algebraic controls must still hold; in particular the base field must split $L$. This is a restriction on the ten-stage lower endpoint, not an unconditional stage bound. The combined exclusions also apply after reducing a nonzero commutative ring in which $8!$, $\gamma$, and the six off-zero residuals are units, if it admits a residue field outside this exception table or one that fails the required Gaussian splitting/chronology. Nonzero but nonunit residuals need not preserve the count.

Run `python check_norms.py`, `python check_n0.py` and `python check_n1.py` using SymPy 1.14 and Python-flint 0.8. The native Lean module `RKCert.Research.SDIRKEightFourZeroGaussianRear` checks the ghost cubic and its incompatibility with $\kappa(v)=0$, the live star identity under its stated distinctness guards, and the two canceled-clock norm products. It does not formalize the complete rooted ingress, resultants, geometric counts, or exactly-four nonexistence. See the stock Lean/Mathlib 4.36.0 axiom audit.
