# No rational degree-eight rule on six scalar sites with both endpoints

Over \(\mathbb Q\), there is no degree-at-least-eight scalar quadrature on at most six distinct rational sites that include both \(0\) and \(1\) as nodes. The outputs can be signed, the endpoints may have zero weights, and the other sites need not lie in \([0,1]\). This is a rational scalar obstruction, relevant to a thirteen-stage ERK9 study only if the candidate is known to have that six-site endpoint shape. It does not exclude arbitrary rational thirteen-stage ERK9 and does not change the unrestricted rational **13–14** interval.

## The exact endpoint pencil

If necessary, pad the scalar rule with zero-weight rational sites to get six distinct sites including \(0,1\). Let \(P\) be the monic quartic whose zeros are its four other sites. Exactness through degree eight implies
\[
                \int_0^1 X(1-X)P(X)X^j\,dX=0,\qquad j=0,1,2 .
\]
The three equations on degree-at-most-four polynomials are independent: the first three monomial columns have rational determinant \(1/1512000\). The kernel is therefore the span of the two independent polynomials
\[
        L_4=42X^4-84X^3+56X^2-14X+1,\qquad
        L_3=14X^3-21X^2+9X-1 ,
\]
which each satisfy those integrals. The monic normalization gives \(42P=L_4+\lambda L_3\) for some \(\lambda\in\mathbb Q\). Thus a rational rule would make this quartic split over \(\mathbb Q\).

## Modulo 11 with multiplicity and possible denominator poles

Homogenize the degree-four pencil as \(L_{4,h}(X,Y)+\lambda YL_{3,h}(X,Y)\). A rational split homogeneous binary polynomial has, after scaling to primitive content over \(\mathbb Z_{(11)}\), a split reduction into homogeneous linear factors: normalize each rational linear factor to have a unit coefficient. Their reductions are nonzero, and their product over the residue field is nonzero, so the normalization agrees up to a unit. This works even when several roots collide within the residue field or a factor has its root at infinity.

If \(\lambda\) is 11-integral, the quartic leading coefficient \(42\) is a unit, so reduction is one of the 11 finite members \(L_4+\bar\lambda L_3\) with degree exactly four. **None is completely split over \(\mathbb F_{11}\)**, even allowing repeats. If \(\lambda\) has negative 11-adic valuation, multiply the whole polynomial by \(\lambda^{-1}\). Its primitive leading unit occurs in degree three, and its homogeneous reduction is \(Y L_{3,h}\). The cubic \(L_3\bmod 11\) is also not completely split: it is \(3(X+5)(X^2-X-3)\), with nonsquare quadratic discriminant \(13\equiv2\). Thus the denominator pole cannot bypass the obstruction.

The code strips every possible linear factor with multiplicity, not just counting distinct roots. In particular this proof is different from checking seven distinct scalar sites directly over the finite field: it rules out all rational six-site rules, including denominator primes or collisions in reduction.

## Exact proof audit

Two finite split-census statements are kernel-checked with no axioms on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The rational moment argument and the projective reduction are mathematical. The independent Python replay uses only the standard library.

From ai-generated:

    python3 -B research/erk-rational-six-endpoint-quadrature/replay.py
    sha256sum -c research/erk-rational-six-endpoint-quadrature/sources.sha256

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.RationalERKEndpointSixMod11
    lake env lean AuditRationalERKEndpointSixMod11.lean
