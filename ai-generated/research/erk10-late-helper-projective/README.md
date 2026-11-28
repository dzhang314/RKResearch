# A projective residue sieve for the rational ERK10 late-helper chart

This is a necessary filter for the
[distinct late-helper construction](../erk10-late-helper/README.md),
not an unrestricted stage obstruction. In each residue field the
sieve retains exactly the available horizons of the three cleared
scalar equations, with a *split* early pair. It includes all
projective poles, repeated residues, and rank-deficient nodal rows.

## Exact reduction

Use primitive projective numerator-denominator pairs for the
six nonanchor scalar sites and for the dense endpoint horizon.
In an ordinary polynomial variable \(X\), a site \([a:b]\)
contributes \(bX-a\). The two ordinary nodal moments of the
eight scalar sites have the common endpoint factor \(X(X-1)\).
For each of the \(X^k\) tests, \(k=0,1\), integrating the remaining
monomials uses \(-1/((j+k+2)(j+k+3))\). Clear denominator factors
once on each entire linear form, over the integers.

With late sites \(d,e,\xi\) and remaining donor \(z\) fixed
projectively, the two nodal moments are linear on the three
coefficients of the early pair polynomial. A nonzero cross
product determines its only possible projective coefficient
tuple. Retain that tuple only if it is a product of two site
factors, allowing either or both factors at infinity.
If the cross product vanishes, check all split pairs
on the one nontrivial row, or all pairs when both rows vanish.

For the remaining terminal condition, the two
\(\kappa\) values are linear on those same early coefficients.
The normalized source functional is polynomial in the horizon
after the global factors already cleared in the linked proof.
If \(\xi=[u:v]\), the \(j\)-th basis weight uses
\(u^jv^{3-j}\) along with the corresponding normalized
horizon coefficient and the supplied polynomial for \(d,e\).
This homogenization arises by clearing a common factor from
both tests and remains necessary at poles. The program matches
the projective ratio of the two \(\kappa\) values with the
ratio of the two functional values, allowing either pair
to be identically zero.

All these scalar equations are cleared over the integers, so
the calculations at 2, 3, 5 and 7 are legitimate numerator
filters for rational tableaux, not existence claims in those
characteristics. A passed residue class is not in general a
lift or a tableau. The associated
[five-prime packet](../erk10-sixteen-late-helper-primes/README.md)
constructs and independently verifies particular regular
lifts. This sieve retains all five corresponding seeds.

## Replay

    python3 -B projective.py 2 3 5 7 11 13 17 19 23 29 31 37 41 --emit /tmp/rk-erk10-masks
    python3 -B seed-audit.py
    sha256sum -c sha256.txt

The masks use indices \(0,\ldots,p-1\) for affine site values
and \(p\) for infinity. The \((d,e)\) column is unordered.
The known excluded class \((18,19,22)\bmod29\) has zero mask.
