# The remaining arithmetic/zero chronology and the uniform exactly-three-zero exclusion

Let $A,b$ be a strict ten-stage SDIRK tableau over a field of characteristic zero or greater than seven, with a common nonzero diagonal $\gamma$, ordinary order at least eight, $c=A1$, and $g=Ac-c^{\odot2}/2$. A *physical quadratic zero* is a literal $g_i=0$, whether or not $b_i=0$.

**Combined result.** Exactly three physical quadratic-zero rows are impossible over every such field. This packet closes the final **A/Z** chronology of the remaining asymmetric supported graph; the states and links assembling the exactly-three result are below. It is **not** a general exclusion of ten stages. Zero-free tableaux and tableaux with at least four physical zero rows are outside the combined result.

## 1. Remaining chart and guarded inverse gap

For the new part assume three distinct zero clocks and reduce using the earlier paid results to a genuine supported centered quadratic trace $r(y)=y^2+ky+q$, $y=2c-1$, with $k\ne0$, no midpoint zero, all weights live, and all regular pivots. The [singular-pivot lemma](../sdirk-eight-asymmetric-singular-pivots/README.md) contains the exact hypotheses and shows the two actual second-gap denominators and the diagonal denominator are nonzero. The weighted reflected tableau is legitimate, so reflect if necessary to make the off-zero arithmetic third row (**A**) forward and the zero arithmetic third (**Z**) reflected.

Write $u,v$ for the two actual normalized second gaps, forward and reflected. Put
$$H(u)=-2+u+4u^2-u^3,\quad Q(u)=4u^3-12u^2+3u+2,\quad \kappa(u)=1+2u-u^2.$$
The [literal endpoint reads](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) give $Q(v)=0$. At the A end we know $u\ne0$, $\kappa(u)\ne0$, and a nonzero actual adjacent tap. Its third residual ratio $\zeta$ is nonzero, with
$$H(u)\zeta=-\kappa(u)Q(u).$$
Thus $Q(u)\ne0$. Also $H(u)$ is nonzero by its actual tap equation, and $3u-2\ne0$ by the nonzero tap. The graph equation $D H(u)=2R(3u-2)$ with $D=R+4\gamma^2$ gives
$$R (u-1)^2(u-2)=4\gamma^2H(u).$$
In particular $u\ne1,2$, because the respective values of $H$ are 2 and 8. Therefore $t=1/(u-1)$ is well defined and the following factor product is nonzero:
$$t(t-1)(t+1)(t+3)(2t^2-1)(4-9t^2-3t^3).$$
Each factor comes respectively from the inverse, $u\ne2$, $u\ne0$, $3u-2\ne0$, $\kappa(u)\ne0$, and $Q(u)\ne0$. No unsupported choice of pivot is made in this chart.

## 2. One conic, the literal pin, and a genuine primitive anchor

Set $s=2\gamma-1$, $\delta=1-t$, and $f(t)=(t+1)(t+2)$. The two arithmetic forward read equations give exactly
$$\begin{aligned}
k&=2-2(s+1)f(t)=K_n/\delta,\\
q&=Q_n/\delta,\ \quad
K_n=[2-2(s+1)f(t)]\delta,\\
Q_n&=(s+1)^2[-\delta+2t^2(t+3)]-s^2\delta-K_n s .
\end{aligned}$$
These follow from $R=(s+1)^2[-1+2t^2(t+3)/(1-t)]$ and $R=s^2+k s+q$, as in the [paired arithmetic calculation](../sdirk-eight-two-arithmetic-thirds/README.md).

The *actual* second reverse gap on the same quadratic graph gives
$$
E(s,t)=-[s(1-v)-1]K_n+(2-v)Q_n-[v(2s^2+2s+1)+2s]\delta=0.
$$
This has degree two in $s$, degree three in $t$. Given $v$, the physical originally oriented clock on the reflected third zero is $y_b=1-(s+1)(1+2v)$. It must be a root of the true signed Cramer cubic $P$. Thus its literal pin is $P(y_b)=0$, cleared by $\delta^3$. The independent clean grade-seven diagonal identity is $90(s+1)\mathcal A-\mathcal B=0$, cleared by $\delta^5$. Finally at the *first chronological* physical zero the supported column pays its clear grade-three primitive read. So the actual forward cubic $P(y)$ and
$$H_{\rm front}(y)=2y^3+(3k-6(s+1))y^2+(6q-6(s+1)k)y+
2-3k+6q-6(s+1)q$$
have a common root. This is the forward anchor resultant, not a guessed pin at the forward third (which is off-zero).

## 3. All resulting primes and every algebraic fiber

Use $\mathbb Q[v]/(Q(v))$; the monic equation of the coordinate $v$ is exactly $Q/4$. For the three terms (rear pin, diagonal, forward anchor), compute each resultant in $s$ against $E$. The resulting polynomials in $t$ have degrees **39, 53, and 129**, respectively. The first two have common monic factor $(t-1)^6$ over the rational gap field. Strip any guard factors from the three projections only if they divide the guarded inverse-gap product in Section 1. The exact polynomial and guard quotients check coefficient-by-coefficient with only the paid denominator primes $2,3,5,7$.

Let $f_1,f_2,f_3$ be the remaining polynomials in $t$, in that order. A genuine common zero gives vanishing of $\operatorname{Res}_t(f_1,f_2)$ and $\operatorname{Res}_t(f_1,f_3)$ in its gap extension. Their norms are calculated by the ordinary resultant against the monic defining equation $Q(v)/4$. This covers any algebraic residue-field root $v$, not only those in $\mathbf F_p$; all leading coefficients used in the coordinate identification are paid. Fixed Sylvester determinants make this a necessary test even at a degree drop. The gcd of their exact integer norm numerators, after stripping only the paid primes, is
$$
13^6\,37^3\,9767\,9883\,156347\,383099\,231631013129\,1423306149647.
$$
The last two primes are the verified factorization of the remaining 79-bit composite support, not an assumption that that cofactor is prime. All eight distinct primes in the displayed product have literal independent recursive Lucas/Pocklington certificates.

For each of these primes the complete **regular A/Z** bivariate fiber reduction of the [169-domain census](../sdirk-eight-three-zero-169-paid-characteristics/README.md) is run at that individual modulus. It factors the full univariate $q$ projection. For each factor, the actual gate gcd in the other variable is computed over a finite extension containing the $q$ representative; Frobenius conjugacy covers all its conjugates. Only factors whose zeros kill the exact nonzero guard product are discarded. The surviving gcd is always 1, including at all prime factors outside the original 169 examples. The finite check therefore handles extensions of any degree, not just a list of trial diagonal or gap values. This excludes A/Z over every paid field.

## 4. Assembly, precise lower-bound scope, and verification

For exactly three physical zeros, the [two-clock proof](../sdirk-eight-two-clock-triple-paid/README.md) and the earlier coincident-clock rank argument exclude fewer than three distinct clocks. At distinct clocks, the [low-support proof](../sdirk-eight-three-zero-d2zero-paid/README.md) excludes $E_2\cap\ker G=0$. For positive support rank, the [constant](../sdirk-eight-constant-zero-trace/README.md), [affine/null](../sdirk-eight-affine-null-trace/README.md), and [silent](../sdirk-eight-three-zero-silent-paid/README.md) exclusions force an all-active genuinely quadratic graph. The [even](../sdirk-eight-even-quadratic-trace/README.md), [asymmetric midpoint](../sdirk-eight-asymmetric-midpoint-zero/README.md), and [singular-pivot](../sdirk-eight-asymmetric-singular-pivots/README.md) arguments leave the three actual arithmetic chronologies treated in the [A/A](../sdirk-eight-two-arithmetic-thirds/README.md), [Z/Z](../sdirk-eight-both-zero-thirds/README.md), and present A/Z results. This is an exhaustive exactly-three conclusion, with no assumption about signs or ordering of the coefficient field.

As a ring corollary, in a nonzero commutative ring with $8!$, $\gamma$, and **all seven other residuals** units, exactly three literal residual zeros are impossible: reduce modulo a maximal ideal. All the rooted conditions and the physical zero count survive, even if distinct clocks collapse, because the combined field result addresses every zero-clock pattern. Nonzero but nonunit residuals do not suffice for this reduction.

Run `python check_projection.py`, `python prime_certificates.py`, and `python check_primes.py` with SymPy 1.14 and Python-flint 0.8. The primality verifier alone uses only the standard library. `RKCert.Research.SDIRKEightMixedArithmeticZeroThirds` proves the arithmetic gap factorization, an inverse-gap coordinate identity, and the numeric support factorization. The entire causal reduction and exact resultant arithmetic are the supplied source proof and independent replays, not one native `HasOrder` theorem. Lean/Mathlib 4.36.0 audit attached. No overall stage-bound change is claimed.
