# Native small real-algebraic SDIRK witnesses

These proofs certify two classical tableaux directly against the reviewed
`RKResearch.FiniteRootedTree`, `Φ`, and `HasOrder`. The matrices are lower
triangular with equal, nonzero diagonal entries, so they also give DIRK
upper bounds.

| Tableau | Stages | Exact order | First failing reviewed tree |
| --- | ---: | ---: | --- |
| Nørsett–Crouzeix | 2 | 3 | Order-four chain; scaled value `−2x` |
| Crouzeix | 3 | 4 | Order-five bush; scaled value `15/16 + 5x²/48` |

The two-stage tableau is the plus sign in Table 7.2 of
[Hairer, Nørsett and Wanner, *Solving Ordinary Differential Equations I*, §II.7](https://link.springer.com/book/10.1007/978-3-540-78862-1).
Both tableaux are documented in [Kennedy and Carpenter, NASA/TM–2016–219173, equation (50)](https://ntrs.nasa.gov/api/citations/20160005923/downloads/20160005923.pdf).
For the three-stage tableau, see also the [INL MOOSE implementation](https://mooseframework.inl.gov/docs/doxygen/moose/classAStableDirk4.html)
and [Crouzeix's 1975 thesis record](https://catalogue.bnf.fr/ark:/12148/cb35916462x).

Write `x = 2γ − 1`. The two-stage relation is `x² − 1/3 = 0`.
The three-stage relation is `x³ − x − 1/3 = 0`. For the latter tableau, the
code uses `(3 − 3x² + x)/2` as the outer weight and proves that it equals
the published `1/(6x²)` at a root. This substitution makes the residuals
polynomial; it is not a change of the tableau.

- [AlgebraicOrderCheck](RKCert/ReviewedNative/AlgebraicOrderCheck.lean) turns
  exact divisibility of every residual in the existing finite checker into
  `HasOrder` when the common relation vanishes. It does not introduce a
  polynomial-evaluation oracle or a second tree/order datatype.
- [SmallSDIRK](RKCert/ReviewedNative/SmallSDIRK.lean) gives rational polynomial
  cofactors for all four and all nine ordered tree encodings through the
  respective orders. Lean checks each identity and the two first failures
  over any characteristic-zero field containing a root.
- [SmallSDIRKRealAlgebraic](RKCert/ReviewedNative/SmallSDIRKRealAlgebraic.lean)
  proves the real roots exist and are isolated in `(1/2, 2/3)` and
  `(1, 6/5)`. The endpoint values are `(-1/12, 1/9)` and `(-1/3, 73/375)`.
  The sign-change proof uses the real supremum and explicit factor bounds,
  with no floating-point approximations. The resulting tableau witnesses
  are in Mathlib's actual `algebraicClosure ℚ ℝ`, the subfield of real
  algebraic numbers.

The formal claims are order, tableau shape, and exact next-order failure.
They do not formalize the methods' stability or a lower bound on the whole
method class.

## Replay

This delta needs the reviewed root at
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5` and the earlier native
`RKCert.ReviewedNative.FiniteOrderCheck`. From the same existing
`ai-generated/lean` Lake package:

```sh
lake build RKCert.ReviewedNative.SmallSDIRKRealAlgebraic
lake env lean AuditReviewedSmallSDIRK.lean
lake env leanchecker --verbose RKCert.ReviewedNative.AlgebraicOrderCheck \
  RKCert.ReviewedNative.SmallSDIRK RKCert.ReviewedNative.SmallSDIRKRealAlgebraic
```

All three new modules and the audit were checked offline with Lean v4.36.0
and Mathlib v4.36.0 (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).
Nine previously uncached Mathlib modules were compiled in a private overlay
to obtain real completeness and the existing relative algebraic closure;
no package dependency was added. The receipts record check times, source
hashes, and theorem axioms.
