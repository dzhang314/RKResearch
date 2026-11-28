# The six-site origin hull forces ramification divisible by four

Let \(K\) be a characteristic-zero discretely valued field of residue
characteristic two. Normalize \(v(2)=1\) and write its value group as
\((1/e)\mathbb Z\). If a quadrature over \(K\) is exact through degree
nine and its at-most-six possible sites include the origin, then
**\(4\mid e\)**. In particular, for a number field this is required
at every place above \(2\), so the field degree is divisible by four.
This is a necessary scalar condition, not a construction or an
unrestricted ERK stage bound.

Pad the sites with zero-weight distinct clocks if needed, and normalize
the split hull of the five nonzero sites to constant coefficient one.
The [four anchored moment rows](README.md) give the complete hull
\[
 P(X)=1+tX+(-70-28t/3)X^2+(280+28t)X^3
      +(-378-168t/5)X^4+(168+14t)X^5.
\]
The four-by-four matrix in coefficients 2–5 is invertible; the
[exact replay](check_ramification.py) computes the determinant,
checks this formula, and verifies the valuations of its coefficients.

For coefficient \(a_i\), consider the quantity \(v(a_i)-i/4\), with
\(v(0)=+\infty\).
If \(v(t)<1/4\), the least value is \(v(t)-1/4\) and it is attained
exactly at indices 1 and 5. If \(v(t)>1/4\), it is zero and is attained
exactly at 0 and 4. This includes \(t=0\). If \(v(t)=1/4\), its
minimizing indices are \(0,1,4,5\). At indices 2 and 3 the valuations
are always strictly above these minima. These checks use only the
strict dominance of the lower-valued term, except at indices whose
terms would still be strictly above the minimum.

For the product of any two polynomials the least and greatest
minimizing indices add. Indeed, at either proposed extremal index,
the product of the two corresponding extremal terms is the only term
of the lowest possible weighted valuation, so it cannot cancel. In
each of the three cases for \(P\), the minimizing index set has width
four. Since \(P\) splits over \(K\), at least one of its linear factors
must have both coefficients minimizing. For a factor
\(1-X/x\), this means \(-v(x)-1/4=0\). Thus \(v(x)=-1/4\) lies in
\((1/e)\mathbb Z\), proving the claim. This argument needs no
restriction on the residue extension. For a number field, summing
\(e_{\mathfrak p}f_{\mathfrak p}\) over primes above \(2\) proves the
degree divisibility.

This strengthens the origin-only parity result. It does not replace
the separate two-endpoint seven-site test or remove the structural
hypotheses in the [dirty-relay construction exclusion](../erk10-dirty-relay-four-visible/README.md).
