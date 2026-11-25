# A standalone 19-site rational rule of order 20

The nodes are \(u/128\) for
\[
 u=1,3,6,11,18,26,34,44,54,64,74,84,94,102,110,117,122,125,127.
\]
These are distinct, strictly interior rational sites. Write \(U\) for
this set of numerators. For each \(u\in U\) define the weight exactly as
\[
 b_u=\frac{\displaystyle\int_0^1
              \prod_{v\in U\setminus\{u\}}(128X-v)\,dX}
            {\displaystyle\prod_{v\in U\setminus\{u\}}(u-v)}.
\]
The integral is only the rational polynomial functional
\(X^k\mapsto1/(k+1)\), so this defines explicit rational numbers.

These Lagrange weights give exactness through degree 18. Reflection
pairing \(u\mapsto128-u\) leaves the weights unchanged by the
uniqueness of the degree-18 interpolation rule. The centered odd
monomial \((X-1/2)^{19}\) has zero in both the rule and the uniform
functional, yielding degree-19 exactness as well.

The [independent exact arithmetic check](verify-standalone-19.py)
derives the weights from the formula, confirms every weight is
positive, checks all 20 required moments by integer arithmetic,
and finds a nonzero defect at degree 20. The exact coefficient
table is also in the archive's
[standalone rule lemma](../../lean/RKCert/ReviewedNative/PositiveRationalRule19.lean).

Together with the [four-shift lower bound](proof.md), this brackets the
minimum number of contributing rational sites at quadrature order 20
between 17 and 19. Attainability at 17 or 18 is not established here.
This rule is **not** a Runge–Kutta tableau or a stage upper bound for any
RK class.
