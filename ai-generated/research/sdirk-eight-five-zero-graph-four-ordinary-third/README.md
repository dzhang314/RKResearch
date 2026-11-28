# Five residual zeros: genuine graph, four ordinary sites, and literal third zero

Let $A,\mathbf b$ be a strict ten-stage SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven. Write $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, $U=\ker G$, and $\gamma\ne0$ for the common diagonal. Consider exactly five physical zeros, genuine supported graph (the nonzero $\mathbf g$-coefficient case of the [support-rank census](../sdirk-eight-five-zero-support-rank/README.md)), no active off-zero weights, and four distinct ordinary clock masses.

**Result.** The literal third physical stage cannot be a quadratic zero in this chart, over any paid field. The cases with physical third off-zero, five ordinary sites, or nonzero off-zero weights are not claimed here.

## 1. Known front and rear roots

The graph has at least four distinct physical off-zero clocks. The first two physical stages are therefore off-zero: a zero second defect would localize all nonzero residuals to one clock by the [first-three pure transition identity](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md). Normalize $\mathbf x=\mathbf c/\gamma$, $\boldsymbol\eta=\mathbf g/\gamma^2$, and $A'=A/\gamma$. With the third stage zero, the actual arithmetic phase gives
$$u=x_2-1,\quad Q(u)=4u^3-12u^2+3u+2=0,\quad a=x_3=1+2u.$$
The first two normalized residuals are $1/2$ and $(1+2u-u^2)/2$.

All nonzero ordinary clock masses are Gaussian by degree-seven orthogonality on four sites, and there are at most five live physical zeros. A live non-Gaussian zero would require another live weight at the same clock to cancel it and would leave too few actual rows to deliver four distinct Gauss sites. Therefore all live zero clocks are Gaussian. The actual last two weights are nonzero and their clocks differ; $c_{10}=1-\gamma$ makes $\gamma$ a Gaussian root as well. Physical stage 8 is either live Gaussian, hence a literal reverse star in the paid chart, or silent and subject to the silent-eighth gate. The [native characteristic projection](../sdirk-eight-four-zero-native-rear/README.md) gives exactly the allowed rear characteristics
$$37,\ 269,\ 379,\ 397,\ 487,\ 69877.$$
No case is left in characteristic zero. This rear restriction only uses Gaussian membership of the actual live endpoints, not the old exactly-four-zero hypothesis.

If $c_3$ itself is Gaussian, it is excluded by the exact coprime front/rear norms in the [pure four-ordinary-site proof](../sdirk-eight-five-zero-pure-four-ordinary/README.md). That part uses only $L_4(\gamma)=L_4(\gamma(1+2u))=Q(u)=0$, independent of the form of support. It remains to consider $c_3$ non-Gaussian, in which case it is the unique silent zero, and the four other physical zeros are the four distinct live Gaussian sites.

## 2. Interpolate the graph with the first live zero

On every off-zero row, $\eta_i=P(x_i)$ for some scalar polynomial $P$ of degree at most two, since the supported column has nonzero coefficient of $\mathbf g$. Matching the two actual initial residuals therefore gives
$$P(T)=P_0(T)+\lambda R(T),\quad P_0(T)=2T-1-T^2/2,\quad R(T)=(T-1)(T-1-u).$$
In particular the leading baseline really matches the normalized second residual $(1+2u-u^2)/2$. Let $\mathbf q=P(\mathbf x)-\boldsymbol\eta$; this is the actual supported vector with normalized scalar trace $P$.

In normalized time put $D=1/\gamma$, $J f(T)=\int_0^T f$ as a polynomial primitive, and $L(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4$. The pure grade-four restriction to $U$ has dimension at most one because $GE_2$ vanishes there and has codimension one in $F_4$. The restriction of the pure vector $L(\mathbf x)$ is nonzero only at the silent zero $a$, so it spans this line and gives actual grade-four cleanliness at every live Gaussian zero. At the first live zero of normalized clock $b$, the supported input $(C-\gamma aI)\mathbf q$ (rescaled by $\gamma$) has zero value at the silent earlier zero, and has no other supported earlier stage. Thus the normalized diagonal read is
$$J[(T-a)P](b)=(b-a)P(b).$$
As a linear equation $E_0+\lambda E_1=0$, its coefficient $E_1$ does not vanish on these controls: it is exactly the pure non-Gaussian first-zero front gate excluded over every allowable rear characteristic by the [same coprime projection](../sdirk-eight-five-zero-pure-four-ordinary/README.md). Hence the candidate graph coefficient is uniquely recovered. The geometric replay explicitly checks this pivot, the distinct Gauss roots, the non-Gaussian silent zero, and the graph value's nonvanishing at each needed literal stage.

## 3. A three-zero constraint from the two pure modes

The pure grade-three space $F_3=GE_1$ is clean on all zeros, so the actual $A'_U P$ read is $JP$. On the live Gaussian zeros the grade-four read of $A'_U(TP)$ is also exact. In grade five, the [graph support rank](../sdirk-eight-five-zero-support-rank/README.md) gives $\dim(E_3\cap U)=2$, so $\dim GE_3=4$ inside the six-dimensional $F_5$. The pure restriction $F_5|_U$ therefore has dimension at most two. It is spanned by the scaled shifted Legendre values of degrees three and four, namely
$$\ell_3(T)=T^3-\tfrac32DT^2+\tfrac35D^2T-\tfrac1{20}D^3,\qquad L(T).$$
Both belong to $F_5$ by ordinary scalar orthogonality and are independent as evaluations on the five distinct physical zero clocks. On the live Gaussian zeros $L$ vanishes, so the pure grade-five discrepancy is always a common multiple of $\ell_3$ there.

At the first live zero $b$, the input $T^2P$ to the grade-five primitive read has just the one possible earlier supported tap from the silent zero $a$. Using its lower $P$ read, the literal discrepancy is
$$
d_b=b^2P(b)+a^2[J P(b)-P(b)]-J(T^2P)(b).
$$
At the second live zero $c$, there can additionally be a tap from $b$. For those two supported tap contributions $p,q$ including their $P$ values, the readings supply $p+q=J P(c)-P(c)$ and $ap+bq=J(TP)(c)-cP(c)$. Thus $a^2p+b^2q=(a+b)(ap+bq)-ab(p+q)$, even if $P(a)$ or $P(b)$ happened to vanish. The actual discrepancy is
$$
d_c=c^2P(c)+(a+b)[J(TP)(c)-cP(c)]-ab[J P(c)-P(c)]-J(T^2P)(c).
$$
The two pure restrictions imply
$$\ell_3(b)d_c-\ell_3(c)d_b=0.$$
This scalar test needs no division by a tap or by a graph value. It is independent of any later off-zero stages or block completion.

## 4. Complete finite controls

In each of the six rear characteristics, split both the Gaussian quartic and the front cubic in their full common finite extension. The live star rear has its two finite orientations and fixes which Gauss site is first live. The silent rear has its unique actual gap pair and allows both orders of the two unused Gaussian roots. In all cases test every one of the three front cubic roots. The coordinate search is geometric, not just a prime-field search. There are six admissible phase-and-clock tuples per characteristic before the final scalar constraint. All fail that constraint. In characteristic order above, the product across the six geometric values of the left side is
$$9,\ 148,\ 343,\ 88,\ 336,\ 40048,$$
respectively nonzero in those prime fields. All conjugates are included, and the replay also asserts that each individual value is nonzero.

Run `python check_fibers.py` with Python-flint 0.8. The native `RKCert.Research.SDIRKEightFiveZeroGraphFourOrdinaryThird` module checks the two-tap polynomial reduction and the cross-gate over an arbitrary commutative ring. The rooted and coefficient-domain classification, finite geometric controls and pure-mode reduction are the source proof and exact replay, not one native `HasOrder` theorem. Stock Lean/Mathlib 4.36.0 axiom audit attached. No overall stage bound changes.
