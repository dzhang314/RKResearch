# Paid cutoff erratum for the moving-terminal weighted reproducer

This is a separate source correction to §1 of dirk_moving_terminal_nullity_and_core_feed_20261126.md, identified in Mark's independent review. The original note is not overwritten. The nullity conclusions and degree cutoffs are unchanged. No compiler, numerical replay, or repository operation was used.

In the weighted reproducer test write \(W=x^e(1-x)^f\), let \(n\) bound the quotient profile degree, and suppose moments are paid through \(m\ge n+2\). An actual nonzero midpoint null gives the identity \(\int_0^1 W h H=r_0 H(t)\) with \(\deg h\le n\) and \(r_0\ne0\). Construct the monic \(W\)-orthogonal polynomials \(P_j\) through \(j=n+1\) and their norms \(d_j\). These are paid: the largest norm cutoff is \(\deg W+2n+3\le p\). Testing \(P_{n+1}\) gives \(P_{n+1}(t)=0\). Consecutive coprimality gives \(P_n(t)\ne0\), from the ordinary three-term recurrence through index \(n\) with paid norm ratios. When \(n=0\), simply use \(P_0=1\).

At the tight cutoff, constructing a *fully orthogonal* monic \(P_{n+2}\) can require the additional moment denominator \(p+1\). It is not needed. Use instead the degree-\((n+2)\) test
\[
 G(x)=xP_{n+1}(x)-\frac{d_{n+1}}{d_n}P_n(x).
\]
This is orthogonal to all degrees at most \(n\): for degrees below \(n\) move \(x\) to the other factor; against \(P_n\), the inner product of \(P_{n+1}\) with \(xP_n\) is \(d_{n+1}\) by monicity and lower-degree orthogonality. All these inner products use only already paid norms. Yet \(G(t)=-(d_{n+1}/d_n)P_n(t)\ne0\). The ordinary test of degree \(n+2\) would give \(0=r_0G(t)\), contradiction.

The one-extra-test case, where a root of \(P_{n+1}\) remains the exact possible scalar locus, is unchanged. The adaptive lower-triangular core-feed tests and concrete diagnostics are untouched.
