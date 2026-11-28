# Four exact real tableaux from the fixed-q 29-adic witness

The same degree-20 coefficient tuple that gives the
[15-stage 29-adic ERK10 method](README.md) gives exactly four
distinct ordered real tableaux of exact order ten, one at each
real embedding of its coefficient field. The field has signature
\((4,8)\): four real embeddings and eight pairs of nonreal
complex embeddings. The real stage interval remains **14–15**.

## Exact real roots of the two defining polynomials

Write \(P\) for the published degree-ten polynomial,
\(c\) for its selected root, and \(a\) for the selected root of
the head quadratic \(Y^2-s_h(c)Y+p_h(c)\). The
[coefficient-field proof](../erk10-fifteen-prime-density/THREE-WITNESSES.md)
identifies the field of the actual ordered tableau with
\(\mathbb Q(c,a)\), of degree 20. In particular the literal
row sums at stages 11 and 14 recover \(1-c\) and \(1-a\).

An exact signed Sturm sequence for \(P\) has variation counts
6 and 4 at negative and positive infinity. These counts also
drop by one across each of the two rational brackets below.
Independently, transformed Descartes tests on ten bounded
intervals and two tails give the same count. All brackets for
\(c\) below have denominator \(10^{20}\); the head intervals
and determinant intervals have denominator \(10^9\).

| Numerators for \(c\) | Sturm endpoint variations | Numerators for \(s_h^2-4p_h\) | Numerators for head determinant |
|---|---:|---:|---:|
| 79001089317030856056 to 79001089317030856057 | 6, 5 | 645172776 to 645172777 | −10883784 to −10883783 |
| 85314051436405470022 to 85314051436405470023 | 5, 4 | 737493556 to 737493557 | −136394680 to −136394679 |

The bounds use exact rational endpoint arithmetic on the
[actual origin formulas](origin_polynomial.py) and
[head Cramer solve](algebraic_lift.py), and check that
every division used for these enclosures has an interval
denominator avoiding zero. The equality of the two origin
cofactor terms with opposite sign at a decic root is the
[exact origin identity](LEAN-ORIGIN.md). Both head discriminants
are positive, giving two ordered head choices over each real
decic root. There are no other real embeddings.

## Why these are exact tableaux, not numeric approximations

The original literal construction takes place in the coefficient
field, using the pivots selected at its 29-adic realization. All
pivots nonzero there are nonzero elements of that field and
remain nonzero under every embedding. The rooted order equations
through ten, strict triangularity, and the nonzero scaled
order-eleven bush defect likewise transfer. The tableau recovers
both generators from its row sums, so the four embeddings give
four distinct ordered matrices and weight vectors taken together.
This is an exact consequence of the existing mathematical order
proof; it is not an end-to-end Lean certificate of real order.

Run the following with SymPy:

    python3 -B verify-real-embeddings.py | diff -u real-embeddings-exact-replay.txt -
