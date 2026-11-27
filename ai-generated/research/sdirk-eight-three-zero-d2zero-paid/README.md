# Three distinct quadratic-zero clocks without a supported quadratic: paid-field exclusion

Assume a ten-stage strict SDIRK tableau of order at least eight has **exactly three literal quadratic-residual zeros at pairwise distinct clocks**, and no nonzero grade-two column supported on those three rows, i.e. $E_2\cap U=0$ for $U=\ker\operatorname{diag}(g)$. This is impossible over any field of characteristic greater than seven. The result includes silent rows and does not require their locations. It does **not** address three distinct zeros with $E_2\cap U\ne0$, three zeros at only two distinct clocks, or a general ten-stage minimum.

Use the [older low-support proof](../sdirk-eight-three-zero-silent/README.md) up to its scalar checks, with the earlier [three-zero rank split](../sdirk-eight-three-zero-exclusion/README.md). These structural arguments use invertible Hilbert matrices of size at most four, nonzero factorials through eight, triangular commutator pivots, exactly the paid Legendre polynomials, and the scalar trace calculus, not the real interval certificate. In particular the $d_3=3$ case on three distinct axes gives all three zero masses $2\gamma$; the explicit formula $(y^2-11/21)/(4(y^2-3/7))$ for a Gaussian mass in centered time is injective in $y^2$ in every paid characteristic and hence cannot give three equal masses. The $d_3=0$ case contradicts consecutive Legendre traces. Thus the only cases are $d_3=\dim(E_3\cap U)=1,2$ and at least one silent off-zero row.

## The common finite support facts

Write $d$ for the unique active off-zero clock with nonzero total weight. In either rank branch, $d$ and the three zero clocks are distinct Gaussian nodes of the fourth Legendre rule, all three zero rows are live, and at least four distinct nonzero residual values must occur at $d$. Indeed the paid $g,g^2,g^3$ moments separate the active off-zero clocks; a polynomial of degree at most three vanishing on the nonzero residuals at $d$ would contradict its nonzero aggregate mass. There is one active off-zero clock when $d_3=1$, or exactly two when $d_3=2$. In the latter case the other clock $e$ has exactly two active rows, equal nonzero residuals and canceling weights, and there is exactly one silent row. These are the algebraic rank/support consequences in the previous packet. All zeros occur at or after physical row 5, since $F_4=GE_2$ is clean on $U$ and the prefix commutator sees the independent columns $1,c,c^2,g$.

The last two weights are nonzero and their clocks differ, by the saturated reverse scalar-word rank. The terminal clock is $1-\gamma$ and terminal residual nonzero by $b^\mathsf T G$ proportional to $b^\mathsf T M$. The reverse control below uses only the actual suffix of scalar words, always retaining any silent column unless explicitly normalized on a non-silent suffix. It does not assume a complete weighted transpose method when a weight is zero.

## One active off-zero clock

The last clock is $d$ and $\gamma=1-d$. The penultimate row is live with a different clock, so it is the latest zero $z$. The old necessary gate is
$$
 (1-z^2)/2-d(1-z)-(1-d)(z-d)=0.
$$
For directed Gaussian pairs, its denominator-cleared resultant numerator has support beyond $2,3,5,7$ only at 17,103,7793, with direct checking at 13 because of the primitive pair coordinate denominator. `check_support.py` verifies the ordered mirror/nonmirror pair presentation and all norm support identities, just as in the [paid two-zero packet](../sdirk-eight-two-zero-paid/README.md). `check_further.py` includes all four Gaussian roots in the splitting extension, not just the rational roots over the prime field. The only actual pairs are $(7,11)$ at 17, $(97,30)$ at 103, and $(6924,2220)$ at 7793.

At these pairs, either algebraic possibility for physical row 8's clock, $4d-z-2$ (star) or $2z-d$ (arithmetic), is neither $d$ nor Gaussian. The arithmetic possibility follows from the global $b^\mathsf T[A,M]=0$ and $A_{10,9}\ne0$ when $A_{9,8}\ne0$. If $A_{9,8}=0$ and row 8 were silent, the first reverse scalar condition would also give $A_{10,8}=0$, making its coordinate zero on all reverse words. This violates full rank. If row 8 were live, its actual normalized three-row suffix would yield the usual star or arithmetic incidence. Hence row 8 is silent off-zero and the arithmetic clock is forced.

The first three front clocks are distinct and none a zero. The first clock $\gamma$ differs from $d$ (the Gauss polynomial is nonzero at $1/2$). At least two of the first three weights are silent. With row 8 silent, exactly three rows are silent and exactly four off-zero rows are live at $d$. The live first-three row at $d$ is row 2 or 3, fixing the choice of gap in each of the two actual front phases. Row 4 is live off-zero at $d$ as well.

Let $T$ interpolate the normalized quadratic defects at the first three normalized clocks, with coefficients $T_0,T_1,T_2$, and let $x=d/\gamma$. The row-four read of $g-T$ gives the same affine gate in $g_4$ as its earlier row at the clock $d$. The coefficient of $g$ in this equation is
$$
 \sigma(x)=-(x-1)/\kappa(u)+T_1+T_2\bigl(4/3+2(\kappa(u)+1)(x-1)/(3\kappa(u))\bigr).
$$
The four live residuals at $d$ must all differ, so $\sigma(x)=0$ is necessary. At 17 none of the four allowed front readings has the actual nonzero second and third defects and a valid adjacent tap. At 103 the four $\sigma$ values are $34,31,34,62$; at 7793 they are $1763,7390,1763,1623$. All are nonzero. This excludes the one-clock branch without assigning any free taps at the silent rows.

## Two active off-zero clocks

Use the eight possible forward clock orders and terminal choices in the previous packet. There is one silent row among the first three, so the last three are live. The first-grade reverse words give $Z_3=W_1G$, since the two distinct off-zero clocks detect both scalar degrees. In particular $b^\mathsf T G A$ vanishes at every quadratic zero. The penultimate residual cannot be zero: at that column the same product would have the sole nonzero contribution $b_{10}g_{10}A_{10,9}$ because the penultimate residual would vanish. Hence the two last clocks are exactly $d,e$ in some order. The ordinary local suffix normalized by its live weights has three distinct clock values by the outer three-row identities. Its third row must therefore be a zero, as there is no third active off-zero clock. Since its second defect is nonzero, this phase is arithmetic. Physical row 8 is the latest zero, with clock $z=2c_9-c_{10}$ distinct from $d,e$, and normalized gap $u=(c_{10}-c_9)/\gamma$ satisfying
$$
 4u^3-12u^2+3u+2=0.
$$
The scalar factorization for this last implication is native. The latest supported-zero gate from the reverse $W_2$ line is
$$
 (1-z^3)/3-(d+e)(1-z^2)/2+de(1-z)-\gamma(z-d)(z-e)=0 .
$$

For each of the eight clocks/diagonals, substitute the now forced linear $z(d)$ and clear the powers of $\gamma$ in the normalized gap. Take the gcd of the norms of the last gate, the cubic numerator, and $70L_4(z)$ over the monic Gauss root field in $d$. Each polynomial uses only paid denominators. Beyond $2,3,5,7$ the only candidate primes are 103 in case 4 and 3517 in case 6. The full splitting-field census leaves **no** actual candidate at 103. At 3517 the sole case is $(d,z,e,\gamma)=(1718,1800,1759,1800)$ with actual front order $(\gamma,e,d)$. This front must be the arithmetic phase in case 6. Its second gap is $338$, with nonzero $H(338)$ and nonzero second defect. Its third defect is zero, as the literal arithmetic formula checks modulo 3517. This contradicts the actual first zero index being at least five.

Run `python check_support.py` and `python check_further.py` with SymPy 1.14 and python-flint 0.8. The exact norm support, split finite census and chronology are the paper/replay portions of the argument. `RKCert.Research.SDIRKEightThreeZeroLowSupport` kernel-checks the arithmetic zero factorization, the repeated clock slope implication over fields, and the final 3517 front computation; it is not a native end-to-end `HasOrder` exclusion.
