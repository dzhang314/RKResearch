# Structural consequence and the exact budget limitation

## A genuinely long-word obstruction

At any hop length h, a nonzero polynomial relation of degree d
holding on all live actual h-hop gap words, or even on their
surviving signed net tuples, rules out \(p\ge2h+2d+1\).
For example a topology enforcing \(\delta_3=\delta_1\) on every
live three-edge path cannot have order 9, even if the adjacent
gap pairs may each vary freely. More generally a fixed
k-period recurrence \(\delta_{j+k}=\delta_j\) on all relevant
paths is detected at \(h=k+1\), so \(p\le2k+4\).
A union of low-degree relation sets can be tested by their
product when the total degree is paid. This is information about
actual composability at a specified lag, not a scalar support
size estimate.

Write \(q=\lfloor(p-1)/2\rfloor\). For each \(1\le h\le q\),
choosing \(r=q-h\) forces at least \(\binom qh\) distinct net
h-hop words. Near the middle h this is at least
\(2^q/(q+1)\) for q≥2. The growth is in the **joint word support**.
It does not force exponentially many stages, independent
branches, or disjoint paths and does not improve an unstructured
physical stage count by itself. In a strictly triangular
topology each contributing walk is a genuine advancing path;
its different incarnations may still reuse vertices.
Earlier intermediate hops can enter weight-zero stages, so
one must not replace the set of actual eligible words by
the alphabet of the one-step *live* marginal.

## Why ordinary tensor flattenings are much smaller

Across an actual intermediate cut after k hops, the composed
measure factors through that stage into its prefix and suffix
profiles. Consider a rectangular moment flattening: powers
on the first k gaps have total degree ≤r_L; powers on the
remaining gaps have total degree ≤r_R, with
\(r_L+r_R+2h+1\le p\); both sides nonempty.
After dividing numerator factorial factors from rows and
columns, the entries depend only on the two total degrees:
\[
                     (2h+1+|\alpha|+|\beta|)!^{-1}.
\]
So it factors through only \(\min(r_L+1,r_R+1)\) degree
classes. The consecutive degree minor of that size is a
unit: multiply row i by the factorial with the largest
column degree to get evaluations of monic descending-degree
polynomials, and use the Vandermonde. Thus the minimum
free-factor size for this complete rectangular moment
flattening is exactly that number. Its cut-profile conclusion
grows linearly with remaining budget, not binomially.
The larger Gram uses sums of exponent vectors on the *same*
h variables, not a disjoint-variable cut; it does not give
a binomial lower bound on the number of stages at a cut.

At the maximal paid hop length \(h=q\), there are at most one
extra degree and no nontrivial universal square test: r=0
gives only nonzero total mass for the unit Gram. A separately
paid linear moment can still refute a particular affine
relation if its prescribed mean differs. No claim of richer
degree-r shape is made beyond the budget \(2h+2r+1\le p\).

## Optional reuse of the same proof

A seed tree of size n, forest factorial F, has ideal start
\(x_0^{n-1}/F\) instead of 1. With a mixture of A and H
letters of integration costs \(d_i=1,2\), integrating out the
initial location changes the leftover Dirichlet parameter to
\(d_0=n+1\) and multiplies the functional by
\(1/(nF\prod_i(d_i-1)!)\). The paid size is
\(N=n+\sum_i d_i+|\alpha|\). The cleared numerator is
\[
       \frac{(n-1)!}{F}
       \prod_i\frac{(\alpha_i+d_i-1)!}{(d_i-1)!};
\]
each quotient is integral. This fits the same Gram lemma
with \(\Lambda\) scaled by a unit, provided
\(n+\sum_i d_i+2r\le p\). No need to interpret an A hop
as a strict clock change, unlike H.

Mathematical scope only. No Lean, compiler, runtime, source
audit, fixed-case work, or repository operation.
