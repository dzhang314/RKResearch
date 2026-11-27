# The central repeated-clock family has no point over \(\mathbb Z[1/30]\)

The [published repeated-clock chart](order-five-five-stage-repeated-clock.md) of five-stage rational strict SDIRK order-five tableaux has centered clocks \((a,u,v,v,-a)\). No member has every coefficient in \(S=\mathbb Z[1/30]\), even before requiring the diagonal to be a unit. This excludes that chart and, by scalar reflection, the mirror clock pattern \((a,v,v,u,-a)\). It does not exclude every other five-stage chart.

Put
\[
P(a)=5a^2+5a+1,\quad Q(a)=3a^3-3a-1,\quad
R(a)=3a^2-1,\quad E(a)=5a^2-3.
\]
The chart formulas yield \(5Q(a)v=-P(a)\) and \(R(a)P(a)u=E(a)Q(a)\). If all clocks belong to \(S\), the identities
\[
\begin{aligned}
(45a^2-30a-24)P(a)-(75a+25)Q(a)&=1,\\
(4-5a)P(a)+(5a+1)E(a)&=1,\qquad 5R(a)-3E(a)=4
\end{aligned}
\]
force \(Q(a)\), \(P(a)\), and \(R(a)\) to be units, in that order. Indeed \(Q\) divides \(P\), then \(P\) and \(R\) divide \(E\). The polynomial identities pay the relevant Bézout witnesses without assuming primitive roots of any polynomial.

Write \(a=m/n\) in lowest terms, \(n>0\), so \(n\) has no prime factors outside \(2,3,5\). The homogeneous integer numerators
\[
p=5m^2+5mn+n^2,\qquad q=3m^3-3mn^2-n^3
\]
must both be nonzero and have no other prime factors. They are both odd for primitive \((m,n)\). The polynomial for \(p\) admits no root modulo \(3\) on projective residue pairs, and its \(5\)-adic valuation is one if \(5\mid n\) and zero otherwise. The polynomial for \(q\) admits no root modulo \(5\) on projective residue pairs, and its \(3\)-adic valuation is one if \(3\mid n\) and zero otherwise. These statements follow directly by reduction, using \(m\) a unit at each prime dividing \(n\). Thus \(p\in\{1,-1,5,-5\}\) and \(q\in\{1,-1,3,-3\}\).

## Complete integer elimination

The equation for \(p\) reduces the equation for \(q\) to \(U m=V\), where \(U=3(p-n^2)\) and \(V=2n^3+3np+5q\). Multiplying the quadratic by \(U^2\) and inserting \(Um=V\) yields
\[
0=5V^2+5nUV+(n^2-p)U^2
=-n^6+18pn^4+25qn^3+117p^2n^2+225pqn-9p^3+125q^2 .
\]
If the constant term is nonzero, \(n\) divides that constant. Otherwise divide by \(n>0\), so \(n\) divides \(225pq\). In both cases \(n\le3375\). This is an effective exhaustive bound, not a height cutoff on a search for rational points. For \(U\ne0\) the candidate \(m=V/U\) is fixed; the only \(U=0\) case has \(p=n=1,q=-1\), then \(m\in\{0,-1\}\). The [exact checker](verify-order-five-paid-central-repeat-exclusion.py) covers all sixteen sign/value combinations and produces precisely these seven possible parameters before checking \(R\):

| \(a\) | Failure |
|---:|---|
| \(0\) | Two endpoint clocks coincide; the four-site chart degenerates. |
| \(-1\) | The diagonal is zero. |
| \(-3/4\) | \(3m^2-n^2=11\), so \(R(a)\) is not a unit. |
| \(-2/5\) | \(3m^2-n^2=-13\), so \(R(a)\) is not a unit. |
| \(-1/2\) | The forced singleton weight at \(u\) is \(1/1404\), with prime \(13\) in the denominator. |
| \(-2/3\) | The forced singleton weight at \(a\) is \(31/78\), with prime \(13\) in the denominator. |
| \(-1/3\) | The forced singleton weight at \(u\) is \(1/1160\), with prime \(29\) in the denominator. |

Every aggregate weight is forced by degree-three interpolation on the four distinct sites, regardless of how the weight at the repeated node is split. The remaining weight obstructions therefore are already scalar; no division by an individual physical weight over \(S\) was used. The proof is arithmetic and independently checkable, not a new Lean lower-bound theorem for all tableaux.
