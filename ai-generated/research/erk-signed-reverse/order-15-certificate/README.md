# A small exact certificate for the 40-stage order-15 tableau

The [literal order-15 method](../tableau-15-weighted.json) has 40 stages and coefficients in \(\mathbb Z[1/15!]\). The [construction proof](../WEIGHTED-ORDERS-11-16.md) verifies its order. This folder supplies a second exact check based on small linear spaces, rather than a replay of all order-15 rooted trees.

~~~sh
python check.py receipt-15.json ..
~~~

The verifier uses only Python's standard library. It checks the actual 66-row tableau before merging, the owner of each row and its folded incoming coefficients, and the equality of the merged output weights with the archived tableau. It verifies that every denominator divides a power of \(15!\), that the weighted observation matrix has a left inverse, and that the primal and reverse blocks are adjoint with the stated weights. None of these tests divides by an individual quadrature mass.

The suffix test spaces have widths \(1,2,4,6,9,11,15\). The verifier checks that multiplication by the clock and application of the reverse matrix send each earlier space into the next one. It also checks a small augmented forward space at each tree size through eight: the stage-vector part and the exact scalar factor are carried together. A root attachment is bilinear in its two inputs, so checking it on the supplied generators is sufficient. The source terms are zero on the indicated suffix tests, with the size-eight forward generators used at the first possible error. The resulting induction is the single-error proof in the construction chapter: two first errors would need at least 17 vertices, so none occurs through order 15.

The final two checks compute the actual defects in the order conditions for two size-16 trees and a linear combination equal to one. Accordingly exact order survives any extension to a nonzero commutative ring in which \(15!\) is a unit. This is an exact arithmetic certificate and checker, not a proof already checked by Lean.
