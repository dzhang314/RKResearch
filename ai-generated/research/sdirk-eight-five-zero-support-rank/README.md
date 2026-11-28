# Exactly five quadratic zeros force a unique supported quadratic

Let $A,\mathbf b$ be a strict ten-stage SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven. Set $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. Let $\gamma\ne0$ be the common diagonal, and suppose exactly five physical stages have zero quadratic residual, with no assumption on their weights or repeated clocks.

**Result.** The actual supported grade-two space has dimension **one**, $d_2=\dim(E_2\cap U)=1$. It is either a pure quadratic in $\mathbf c$ with exactly two physical off-zero clocks, or a genuine quadratic graph with three to five physical off-zero clocks. The possible active groups are explicitly classified below. This is a necessary stratum classification, not an exclusion of all five-zero cases and not a new overall stage bound.

We use the [two-sided saturated flags](../sdirk-eight-two-zero-line/README.md) with $E_j,W_j$ the forward and reverse spaces, $F_j,Z_j$ their pure parts, and $M=CA-AC-A^2$. Write $d_j=\dim(E_j\cap U)$ and let $U_{\rm row}$ consist of literal rows supported on the five zero coordinates. The support restriction is
$$\dim(W_j\cap U_{\rm row})=5-d_{5-j}.$$
In particular, $\dim W_3=6$, $\dim W_2=4$, and $F_4=\operatorname{Ann}(W_3)$. The ordinary moment matrix of size four is nonsingular, so at least four distinct ordinary clock masses are nonzero. A live stage means $b_i\ne0$; an off-zero stage means $g_i\ne0$.

## 1. Zero support is impossible

If $d_2=0$, then $W_3$ contains every literal zero-coordinate row, so $F_4$ is clean on every zero. Every zero clock $a$ is Gaussian. Indeed give its coordinate row its at-most-cubic scalar profile $f$ (nonzero because the row pairs to 1 with $\mathbf1$); the four probes $(C-aI)C^j\mathbf1$, $0\le j\le3$, say that $(X-a)f(X)$ is proportional to the monic fourth shifted Legendre polynomial. Hence $70a^4-140a^3+90a^2-20a+1=0$. As in the [earlier clean prefix argument](../sdirk-eight-four-zero-low-support-active-clock/README.md), every zero is at index at least five: the three scalar prefix reads and pure $\mathbf g$ give four independent prefix columns in the kernel of the nonzero row $\mathbf e_i^{\mathsf T}M$.

The off-zero restriction of $W_3$ has rank one. Its ordinary row powers show there is at most one live off-zero clock. If there is one such clock, the restrictions of $\mathbf b^{\mathsf T}$ and $\mathbf b^{\mathsf T}G$ must be dependent, so all its live residuals are the same nonzero value. The first residual moment makes that entire off-zero aggregate cancel. In either case the ordinary mass is on the Gaussian zero sites. There are five zero rows but exactly four different Gaussian sites from moment rank and simple roots, so at least one pair has equal clocks.

For any pair of zero rows $i,j$ with the same clock, $\delta=\mathbf e_i^{\mathsf T}-\mathbf e_j^{\mathsf T}$ is in $Z_3=\operatorname{Ann}(E_4)$: both rows agree on all scalar polynomial representatives and on every pure grade-four value, which vanishes there. Set $N=A-\gamma I$, $\mathbf z^{\mathsf T}=-\mathbf b^{\mathsf T}M/2$. As in the [rear-tail rank calculation](../sdirk-eight-four-zero-gaussian-rear/README.md), $Z_3$ is spanned by $\mathbf z^{\mathsf T},\mathbf z^{\mathsf T}N$ and detected on the last two coordinates. Both terminal weights are nonzero, their clocks are distinct, and
$$
\kappa\,\mathbf z^{\mathsf T}N=\mathbf z^{\mathsf T}((1-\gamma)I-C),\qquad
\kappa=1+2v-v^2,\qquad v=(c_{10}-c_9)/\gamma.
$$

**No live off-zero clock.** The two terminal stages are live Gaussian zeros and $c_{10}=1-\gamma$. If stage 8 is silent, the literal ghost gate gives $c_8=2c_9-c_{10}$, nonzero $z_8$, and $\kappa\ne0$. If stage 8 is live, it is a third Gaussian zero, and the only paid possibility is a literal reverse star (no live arithmetic third survives the [native characteristic projection](../sdirk-eight-four-zero-native-rear/README.md)). In its complete geometric fibers at $37,269,379$, the second residual ratios $\kappa$ are respectively $26,156,277$, all nonzero; the relative third residual is also $\kappa$. Thus in either case the last three clocks are distinct and all three corresponding entries of $\mathbf z$ are nonzero. Since $\kappa\ne0$, any member of $Z_3$ is $\mathbf z^{\mathsf T}$ times an affine function of clock, component by component. The nonzero duplicate row $\delta$ is supported at a single clock. Of the three distinct rear clocks at least two are outside this support; the affine function must vanish at both, hence vanish identically. Contradiction.

**One live off-zero clock.** The nonzero row $\mathbf b^{\mathsf T}G$ spans $Z_2$ and its terminal component is nonzero, so stage 10 is off-zero. Stage 9 is a live zero at a different clock, whence $\kappa=0$. A silent stage 8 is excluded by the reverse ghost gate. The actual live three-row end has distinct clocks, so stage 8 is also zero. The duplicate row $\delta$ lies in $Z_3$ and does not meet stage 10. It must meet stage 9 by detection on the last two, and it cannot meet stage 8 by distinctness. Since $\mathbf z^{\mathsf T}$ has nonzero terminal component and $\mathbf z^{\mathsf T}N$ has zero terminal component, $\delta$ is a nonzero scalar multiple of $\mathbf z^{\mathsf T}N$. But $z_8=z_9=0$ by proportionality to $\mathbf b^{\mathsf T}G$, so $(\mathbf z^{\mathsf T}N)_8=0$ gives $A_{10,8}=0$. The actual reverse third therefore has no strict tap from its first stage. A star third requires such a tap, so it is arithmetic: its normalized clock gap is $2v$ and its only strict tap (from the second stage) is $2v$. The normalized third defect ratio is $1+4v-4v^2+2(2v)v=1+4v$, which must vanish because it is a zero. Together with $\kappa=0$ this gives $7=0$ from
$$16(1+2v-v^2)-7=(1+4v)(9-4v).$$
This is impossible in a paid field. All zero-support cases are now excluded.

## 2. Support dimension at most one

Let $m$ be the number of distinct physical off-zero clocks and $n$ the number of such clocks with a live off-zero stage (count only off-zero stages at a clock, even if the clock also occurs on zeros). The [one-clock exclusion](../sdirk-eight-five-zero-one-off-clock/README.md) gives $m\ge2$. For $m\ge3$, the off-zero restriction of $E_2$ already has rank at least three by the scalar Vandermonde, so $d_2\le1$. For $m=2$, the only possible exception $d_2=2$ would mean $\mathbf g$ is constant in each physical clock group, since
$$E_2=\langle\mathbf1,\mathbf c,\mathbf c^{\odot2},\mathbf g\rangle.$$
Here $F_3=GE_1$ because two different physical off-zero clocks detect both affine columns. Weighting $E_3$ into $W_3$ has image dimension $4+n$: the ordinary Hilbert moment test detects all scalar cubic profiles, and the weighted pure part $\mathbf g$ times an affine column has rank exactly $n$ at the live off-zero clocks. In the constant-residual case its entire off-zero restriction has rank exactly $n$, since all entries in a live clock group are scalar multiples of their weights with the same scalar, and the polynomial columns already detect the $n$ sites. Thus the supported image has dimension four. This contradicts $\dim(W_3\cap U_{\rm row})=5-d_2=3$. Consequently $d_2=1$.

A generator is $\mathbf q=r(\mathbf c)+\alpha\mathbf g$, with $\deg r\le2$. Its scalar trace is nonzero since the nonzero pure line $\langle\mathbf g\rangle$ has no supported vector. The two following alternatives are exhaustive.

## 3. Graph support, $\alpha\ne0$

The off-zero residual is a fixed quadratic function $-r(c)/\alpha$ of clock. Within a live off-zero clock its aggregate weight is zero: use the residual moments $\mathbf b^{\mathsf T}C^j\mathbf g=0$ through $j=m-1\le4$ and the literal clock Vandermonde. Thus every live off-clock consumes at least two live rows, and $n\le2$. There cannot be only two physical off clocks: constant residual at each would give $d_2=2$.

The off-zero restriction of $E_3$ has rank $\min(m,4)$, because the whole space consists of cubic polynomial values plus $\mathbf g$ times an affine correction (also cubic on the graph), and scalar cubics already realize that rank. Therefore $d_3=6-\min(m,4)$. For $n\ge1$, weighting is an isomorphism $E_2\to W_2$: the ordinary moment test detects the quadratic scalar profile and a live off-zero row detects the pure line. The off-zero restriction then has rank $n$, so the support identity at $j=2$ gives $d_3=1+n$. If $n=0$, the three ordinary weighted quadratic polynomial rows are supported, giving $d_3\le2$. These ranks and the five-row budget yield:

| Live off-zero clocks $n$ | Physical off-zero clocks $m$ | Necessary off-zero weights |
| --- | ---: | --- |
| 0 | 4 or 5 | All five silent |
| 1 | 4 | Two equal-residual live stages at one clock, with opposite weights; three different silent clocks |
| 2 | 3 | Two equal-residual live pairs at different clocks with opposite weights in each; one silent stage at the third clock |

The ordinary mass in each graph stratum is entirely on zero rows, so there are at least four distinct live zero clocks. They are not asserted to be Gaussian when there are five distinct ordinary sites.

## 4. Pure polynomial support, $\alpha=0$

The nonzero trace must vanish at all physical off-zero clocks; $m\ge2$ now forces $m=2$, and we can normalize $r(X)=(X-d)(X-e)$. Let $\nu$ count how many of those two physical groups have two different nonzero residual values. The restriction of $E_3$ has rank $2+\nu$, using the two scalar clock evaluations and independent affine coefficients multiplying each varying residual. Thus $d_3=4-\nu$. At least one physical group varies since $d_2=1$.

If $n=0$, the same three quadratic weighted rows supported on $U$ give $d_3\le2$, so both physical groups vary. If $n=1$, weighting $E_2$ is an isomorphism and its off-zero restriction has rank $1+\epsilon$, where $\epsilon$ is 1 if the residual varies among the live stages at the sole live clock $d$, and 0 otherwise. The support identity gives $\nu=2-\epsilon$. With $\epsilon=0$ the active residuals are constant and the ordinary group mass cancels, so there are at least two live stages at $d$. Variation there must come from a silent stage, and variation at the silent clock $e$ costs two rows. This exhausts the five off-zeros. With $\epsilon=1$ at most four stages can be live at $d$. If the aggregate there is nonzero, the first three residual moments force at least four distinct live residuals. If it is zero, residual Vandermonde through degree three forces each distinct live residual class to cancel, using at least four stages for a varying group. Thus exactly four stages are live at $d$, and $e$ is one silent stage.

If $n=2$, weighting $E_3\to W_3$ is an isomorphism because both live clock groups detect its affine pure corrections. Its off-zero restriction has rank $1+d_2=2$, already reached by its scalar polynomials. Thus residual is constant at each live group, and each group's ordinary weight cancels by the first residual moments at the two clocks. There are at least two live rows in each group, but at least one group varies physically. Hence four live stages and one silent stage supply the two constant live pairs plus the differing residual.

| Live off-zero clocks $n$ | Necessary physical group structure |
| --- | --- |
| 0 | Both distinct physical groups vary; all five weights silent |
| 1, constant live residual | Two live and one silent at $d$, two silent at $e$, both physical groups vary |
| 1, varying live residual | Four live at $d$, one silent at $e$ |
| 2 | Two constant live pairs at the two clocks, plus one silent differing residual at one of them |

No real ordering enters the arguments. For rings, this is a coefficient-**field** rank statement. The excluded $d_2=0$ branch also gives a ring contradiction if $8!$, $\gamma$, the five off-zero residuals, and a four-by-four minor of the physical off-zero $E_2$ evaluation matrix are units: reduction at a maximal ideal preserves the count and the full off-zone evaluation rank. A merely nonzero determinant over a ring does not give that result.

Run `python check_rear_star.py` with Python-flint 0.8 to replay the only new numerical guard in the zero-support argument. The native `RKCert.Research.SDIRKEightFiveZeroSupportRank` module checks the affine distinct-clock gate and adjacent tap's forced characteristic seven. The abstract rank arguments and original rooted flag/chronology ingress are the mathematical proof and earlier cited work, not a native end-to-end `HasOrder` result. Stock Lean/Mathlib 4.36.0 axiom audit attached.
