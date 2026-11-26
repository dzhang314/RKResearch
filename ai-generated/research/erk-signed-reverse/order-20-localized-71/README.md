# A 71-stage explicit Runge–Kutta method of exact order 20

Let
$$
P \coloneqq 37\cdot 911\cdot 15901\cdot 1120673\cdot 86775809\cdot 1034700137,
\qquad R \coloneqq \mathbb Z[1/(20!P)].
$$
The [tableau](tableau-20-localized-71.json) gives an explicit Runge–Kutta method of exact order 20 with coefficients in any nonzero commutative ring in which both $20!$ and $P$ are units. It uses one fewer stage than the [72-stage factorial-unit tableau](../tableau-20-weighted.json), which does not require the extra inversions.

## Why the zero split can be omitted

In the [weighted construction](../WEIGHTED-SITE-RANK.md), the first reverse polynomial that the original chart does not recover is known at the two endpoints. Its discrepancy therefore has the form $H(v)q(v)$, where $H(v)\coloneqq 1-v^2$, $v$ is the centered reverse clock, and $q$ has degree at most seven. The 72-stage construction uses an extra observation at zero to recover this polynomial without dividing by any ordinary quadrature mass.

The two signs at each of the four radii below give eight distinct sites. These eight observations are enough to recover $q$ over $R$.

| Radius | Mass at either sign | Part of the numerator not inverted by $20!$ |
|---:|---:|---:|
| $2/3$ | $1034700137/36212176000$ | $1034700137$ |
| $5/6$ | $231772976/1980353375$ | $911\cdot15901$ |
| $7/6$ | $-663438416/940667853125$ | $37\cdot1120673$ |
| $4/3$ | $86775809/3168565400000$ | $86775809$ |

Every difference between distinct selected sites and every value of $H$ there is a unit after inverting $20!$. Inverting $P$ makes all eight masses units as well. At a selected site $a$ with mass $\lambda_a$, the observation is $\lambda_a H(a)q(a)$. Its contribution to the interpolant is this observation times $H(v)\ell_a(v)/(\lambda_a H(a))$, where $\ell_a$ is the Lagrange cardinal polynomial on the eight selected sites. The site $-1/6$ remains in the quadrature rule but has no role in the interpolation. Thus the extra split at zero can be omitted without changing the old endpoint data, the scalar quadrature, or the signed late correction.

## What the exact check proves

The [receipt checker](check71.py) verifies the identities in the [finite proof](../order-15-certificate/README.md) for the new tableau. In particular, it checks the weighted adjoint relation, all 20 scalar moments, and 394 forward attachments through tree size ten. The chart recovers the forward tree weights through size nine. An error in a suffix stage derivative can first occur at size eleven; a child with a nonzero forward reconstruction error has size at least ten. Their product would have size at least 21. Thus through size 20 the rooted recurrence contains only linear error terms. The checker verifies 194 transitions generating the dual tests that annihilate these terms, including all pairings needed for the size-ten forward error. This proves the order conditions by induction, without sampling or enumerating the order-20 trees.

The checker also verifies that the 116 virtual rows fold to exactly 71 distinct physical rows. It checks equality of the summed incoming coefficients along each alias and of the summed output weights. The fold preserves each Butcher weight vector after pulling it back to the virtual rows, so it preserves the order conditions. The common denominator of the physical tableau divides $(20!P)^4$. Its part relatively prime to $20!$ is exactly $P$.

Finally, the checker evaluates two specified size-21 trees on the new tableau. Their defects, meaning the left-hand side of the order condition minus one, satisfy
$$
(-1843683372185354813767680)\delta_0
+657975095613776939581440\,\delta_1=1.
$$
At least one size-21 order condition therefore fails after any allowed base change to a nonzero ring. The method has exact order 20 in each such ring, not merely order at least 20.

## Reproduction

From this directory, with Python 3.10 or later (without `-O`):

```sh
python3 check71.py .. tableau-20-localized-71.json receipt-20-localized-71.json
```

The checker uses only the standard library. The optional constructor uses SymPy and writes its outputs to a separate directory:

```sh
python3 construct71.py .. output
```

These are exact arithmetic checks, not Lean certificates. The 72-stage tableau is unchanged.
