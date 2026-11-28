# The baseline (star-front) graph is excluded in characteristic zero

Suppose a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field has exactly five physical quadratic zeros, genuine graph support, and all off-zero weights zero. Normalize time and residuals by its common nonzero diagonal $\gamma$: $T=X/\gamma$, $D=1/\gamma$, and $\boldsymbol\eta=\mathbf g/\gamma^2$. Assume its off-zero graph is
$$P_0(T)=2T-1-T^2/2.$$
This is necessarily the graph in the literal star-front phase with the initial three physical rows off-zero, because those distinct actual clocks and their exact residuals match $P_0$. The proof is also valid for this graph whenever it occurs by any other mechanism.

**Result.** The chart is impossible over every characteristic-zero field, without real or ordered-field hypotheses. Other graph profiles and paid positive characteristics are not decided here.

## 1. A fixed normalized first-zero cubic

All five physical zeros are live at distinct clocks by the [no-four-site theorem](../sdirk-eight-five-zero-graph-four-ordinary-duplicate/README.md). Write $\mathbf q=P_0(\mathbf c/\gamma)-\boldsymbol\eta$ for the actual supported graph column. The first zero clock $a$ is diagonal-only for $A'\mathbf q$, where $A'=A/\gamma$. Its grade-three pure part is clean on all zeros because $F_3=GE_1$ (there are at least two distinct off-zero clocks). Therefore $JP_0(a)=P_0(a)$ with $J$ the normalized primitive from zero, giving
$$ Q_a(a)=a^3-9a^2+18a-6=0.$$
The replay checks irreducibility over $\mathbb Q$. The grade-four pure restriction on the zero set is the line of the scaled fourth Legendre polynomial $L_4$, as in the [actual two-zero line gate](../sdirk-eight-five-zero-pure-silent-eighth/README.md). Moreover $L_4(a)\ne0$: if it vanished then the diagonal of $M$ at the first zero would give $P_0(a)=0$ because $M\mathbf q$ spans the same line on the zero set. The clean reads at $a$ would then give $P_0(a)=JP_0(a)=J(TP_0)(a)=0$ at a nonzero Gauss clock, which the [native quadratic primitive lemma](../sdirk-eight-five-zero-graph-four-ordinary-nongauss/README.md) excludes.

## 2. Live eighth stage

The last three physical zeros are live at $D-1-w,D-1-v,D-1$, with $w=2-v$ or $2v$. The four known zero clocks are these and $a$. Take their monic product $P_4$ and moments $M_i=I_D(T^iP_4)/D^i$, with $I_D(T^j)=D^j/(j+1)$. The fifth literal zero weight is nonzero and its clock $b$ distinct from all four, so the exact pivot $M_0=b_{\text{second zero}}P_4(b)\ne0$ gives $b=D M_1/M_0$. The two ordinary moment minors and the grade-four second-zero line gate are exactly those in the [pure live-eighth elimination](../sdirk-eight-five-zero-pure-live-eighth/README.md), using $P=P_0$ instead of its pure quadratic and working over $\mathbb Q(a)$.

The complete pairwise resultants in the reverse gap (or $V=(v-1)^2$ for a star) have monic common factor $D^4$ times a degree-five factor for a rear star; for a rear arithmetic they have $D^8$ times factors of degrees two and eight. The exact replay checks the factorization, reconstructs the actual reverse parameter polynomial in each non-$D$ quotient, and verifies that its monic linear gcd divides $M_0$ there. Thus every purported solution violates $D\ne0$ or $M_0\ne0$. In the rear star the two terminal clocks occur symmetrically in $P_4$, and the second-zero gate does not depend on which is third-from-rear, so this rules out both orientations.

## 3. Silent eighth stage

A silent stage 8 is off-zero. The reverse ghost identity makes $v$ a root of $v^3-4v^2-v+2$. The [joint cubic method](../sdirk-eight-five-zero-graph-third-silent-eighth/README.md) works here with the $Q_a$ cubic. The generator $a+2v$ has irreducible degree nine, and the replay verifies both recovered gap coordinates in the original two-equation quotient.

The three known zero clocks are $a,D-1-v,D-1$. Their ordinary moment Hankel determinant in $D$ has exact factors $D^6$ and one degree-nine factor. The common factor with the principal Cramer pivot is precisely $D^2$, so no rank-drop ambiguity remains after $D\ne0$. Recover the two interior zero clocks as roots of a monic quadratic by the exact inverse of that pivot, agreeing with all three moments. In this quadratic algebra the two signs exchange the order of those clocks. Substitute the first interior clock into the same second-zero line gate with $P_0$. The exact sign norm is nonzero (a degree-eight residue in the degree-nine $D$ field), excluding both orders. All fields and residual inverses are verified algebraically; no real or prime-field search is involved.

Run `python check_live.py` and `python check_silent.py` with SymPy 1.14. The companion Lean source `RKCert.Research.SDIRKEightFiveZeroGraphStarFront` records the integral scalar identity for the first zero cubic. The full flag ingress and exact characteristic-zero tower computations are the mathematical source proof and replays, not a native end-to-end `HasOrder` theorem.
