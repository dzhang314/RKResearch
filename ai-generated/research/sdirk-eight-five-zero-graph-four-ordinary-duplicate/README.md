# A Gaussian duplicate cannot complete the four-ordinary-site graph

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight, with common nonzero diagonal $\gamma$, over a field of characteristic zero or greater than seven. Let $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $U=\ker G$. Suppose exactly five physical quadratic residuals vanish, that the unique supported degree-two column is a genuine graph, and that all off-zero weights are zero.

**Result.** There cannot be only four nonzero ordinary clock masses in this chart. Together with the [corresponding pure-support theorem](../sdirk-eight-five-zero-pure-four-ordinary/README.md) and the [support classification](../sdirk-eight-five-zero-support-rank/README.md), every candidate with five literal zeros and no active off-zero stage must have **five distinct live zero clocks**. That genuine-graph five-ordinary-site case, and cases with active off-zero stages, are not addressed by this proof.

## 1. Find exactly where grade four is clean

The [non-Gaussian-zero exclusion](../sdirk-eight-five-zero-graph-four-ordinary-nongauss/README.md) makes all five physical zero clocks Gaussian if there are four ordinary sites. Thus one Gaussian site occurs twice, and every other Gaussian site occurs once. A singleton site's weight is nonzero; the two duplicate weights have nonzero sum but either one of them may be zero.

Use $A'=A/\gamma$, $\mathbf x=\mathbf c/\gamma$, $\boldsymbol\eta=\mathbf g/\gamma^2$, and the actual supported graph column $\mathbf q=P(\mathbf x)-\boldsymbol\eta$ for a degree-two scalar polynomial $P$. The pure grade-four space restricted to $U$ is a line, because $GE_2$ is clean on $U$ and has codimension one in $F_4$. The restriction of $M\mathbf q$, $M=CA-AC-A^2$, is nonzero, since its component at the earliest nonzero entry of $\mathbf q$ is $-\gamma^2$ times that entry. It therefore spans the line.

Each degree-three weighted clock polynomial row is supported on $U$, since every off-zero weight vanishes, and is orthogonal to $F_4$ by the grade-seven pairing. Take the cubic that vanishes at the three other distinct Gaussian sites. At a singleton Gaussian site its literal factor and weight are nonzero, so every $F_4$ value is zero at that singleton. Thus the line $F_4|_U$ is supported **only on the two occurrences of the duplicate clock**. This does not assert that the two duplicate values are equal or clean. A degree-three cardinal test at the duplicate gives weighted cancellation of those two values, including when one weight is zero.

Because $M\mathbf q$ is supported there on $U$, the earliest nonzero $\mathbf q$ component must occur at a duplicate row. Both duplicate entries equal $P(a)$, where $a$ is their common normalized clock, so $P(a)\ne0$ and the first nonzero entry is the earlier duplicate. A singleton zero cannot precede it: at such a singleton, with normalized clock $s\ne0$, the actual $P(s)$, $A'\mathbf q$, and $A'(\mathbf x\odot\mathbf q)$ all vanish by chronology. Their reads are clean (first from $F_3=GE_1$ since at least two physical off-zero clocks exist, and second by the singleton $F_4$ proof). Hence $P(s)=JP(s)=J(TP)(s)=0$. The [native nonzero-clock primitive lemma](../sdirk-eight-five-zero-graph-four-ordinary-nongauss/README.md) makes a quadratic with all these reads zero identically, contradicting $P(1)=1/2$. Therefore **the first physical zero is the first occurrence of the duplicate clock**.

## 2. Only two clean diagonal gates are needed

At the first zero $a$, the actual $A'\mathbf q$ read is diagonal and grade-three clean, hence $JP(a)=P(a)$. At the first singleton zero, of normalized clock $b$, the supported input $(\mathbf x-a\mathbf1)\odot\mathbf q$ vanishes at **both** duplicates, regardless of their order relative to $b$. It has no earlier nonzero coordinate and its grade-four read at $b$ is clean. Thus
$$
JP(a)-P(a)=0,\qquad J[(T-a)P](b)-(b-a)P(b)=0 .
$$
Here $J$ is simply the polynomial primitive from zero. No denominator involving a graph value, duplicate weight, or strict tap is introduced.

The [literal third-zero graph obstruction](../sdirk-eight-five-zero-graph-four-ordinary-third/README.md) leaves all first three physical stages off-zero in this chart. They have distinct clocks. The graph $P$ is therefore their unique actual residual interpolant, expressed using their star or arithmetic phase. With $u=x_2-1$, $\kappa=1+2u-u^2$, and $H=1,j=0$ (star) or $H=-2+u+4u^2-u^3,j=3u-2$ (arithmetic), it is
$$
P(T)=\frac{H(2T-1-T^2/2)+j(T-1)(T-1-u)}{H}.
$$
All three literal values are checked in the exact replay. The two diagonal equations are homogeneous in $P$, so the finite algebra uses its cleared numerator and then strips only the forbidden literal guards. These are $u\ne0$, $\kappa\ne0$, $P(a)\ne0$, and either $u\notin\{1,2\}$ for the star or $H,j,g_3\ne0$ for arithmetic. When physical stage 8 is a known off-zero ghost its graph value must also be nonzero.

## 3. Complete geometric rear and duplicate order

The actual last two weights are live Gauss sites at distinct clocks, so the [native Gaussian rear projection](../sdirk-eight-four-zero-native-rear/README.md) gives only $37,269,379$ for a live third (star), or $397,487,69877$ for a silent third. The silent-third stage's arithmetic ghost clock is not itself Gaussian in any of its three complete rear controls, as checked exactly. Thus that stage must be off-zero, not the silent duplicate. In the live-star cases, physical stages 8, 9, 10 are three distinct live Gaussian clocks.

If stage 8 is live and the duplicate clock is in the three-stage rear, the two early zeros are the first duplicate and the unique missing Gaussian singleton. Otherwise the two early zeros are both duplicates and the first singleton is stage 8. In the silent-stage-8 chart, both stage 9 and stage 10 are live Gaussian zeros, and the first three zeros precede stage 8. If the duplicate is one of the two rear clocks, the first zero is that duplicate and the two other early zeros are the two missing Gaussian sites in either order. If both duplicates are early, the single other early Gaussian site is the first singleton, independently of which position the second duplicate takes after the first.

For completeness, the literal duplicate weight cases are covered as follows; counts are **per listed prime** and refer to relative zero order and forward phase, not the interleavings of unrelated off-zero stages.

| Rear | Projected diagonal-gate charts | Relative zero order/phase with both duplicate weights live | Relative zero order/phase with exactly one duplicate weight live |
| --- | ---: | ---: | ---: |
| Live star at $37,269,379$ | 16 | 16 | 20 |
| Silent third at $397,487,69877$ | 12 | 16 | 24 |

If one occurrence is in the actual live rear, only the earlier duplicate can be silent; if both are early either one can be silent. Both cannot be silent, because that Gaussian site's aggregate is nonzero. The silent-third projection merges the two relative early positions of the second duplicate where they give the same first singleton. The diagonal equations are independent of all duplicate weight splits, hence the 84 projected charts cover every such literal activity choice.

The replay splits the entire Gaussian quartic, enumerates every allowed rear and duplicate position, then takes the gcd of the two cleared diagonal equations in $u$ over that complete control field. After removing only the literal guards, the gcd is constant in every chart. This rejects any possible algebraic $u$, including roots in arbitrary further extensions of the control field. No grid restriction is used.

Run `python check_fibers.py` with Python-flint 0.8. `RKCert.Research.SDIRKEightFiveZeroGraphFourOrdinaryDuplicate` proves the singleton pure-value step from the literal cubic moment over an integral domain. The rooted flags, first-nonzero chronology argument and finite algebraic fibers remain the mathematical proof and exact replays, not one native `HasOrder` theorem. Stock Lean/Mathlib 4.36.0 audit attached. No overall stage interval changes.
