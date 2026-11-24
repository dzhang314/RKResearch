# Native rational upper bounds

These modules use the reviewed `RKResearch.FiniteRootedTree`, its positive order
and factorial, the reviewed stage weight `Φ`, and `RKResearch.HasOrder`.
They do not import the old RKCert tree, order, enumeration, or any order bridge.

- [FiniteOrderCheck](RKCert/ReviewedNative/FiniteOrderCheck.lean) generates
  the trees of order `n + 1` by splitting their vertex budget between the two
  arguments of the reviewed Butcher product. `mem_treesOfOrderSucc` proves exact
  membership; `checkOrder_iff` proves the Boolean check equivalent to the
  reviewed `HasOrder` over any finite stage set and commutative semiring with
  decidable equality. Through order seven there are 197 ordered encodings;
  the checker keeps both orders of sibling branches rather than assuming a quotient.
- [RationalUpper](RKCert/ReviewedNative/RationalUpper.lean) certifies classical
  RK4 (four explicit stages, exact order four), implicit midpoint (a one-stage
  strict SDIRK, exact order two), and the three-stage midpoint extrapolation
  (variable diagonal, exact order four). Their first unpaid bush conditions
  evaluate to **25/24**, **3/4**, and **185/192**, respectively, not one.
- [RationalDIRK7](RKCert/ReviewedNative/RationalDIRK7.lean) checks the existing
  seven-stage rational DIRK tableau on nodes `(0,3,4,8,10,13,14)/14`.
  All reviewed order conditions through seven hold. The order-eight bush has
  weight **167931/1344560**, not **1/8**. The matrix is lower triangular with a
  nonzero and nonconstant diagonal (not all entries of the diagonal are nonzero).
  This is the zero-central-parameter concrete tuple, not a family or minimality proof.
- [RationalUpperBaseChange](RKCert/ReviewedNative/RationalUpperBaseChange.lean)
  uses the native [ChangeCoefficients](RKCert/ReviewedNative/ChangeCoefficients.lean)
  module. An injective coefficient map both preserves and reflects order, so
  all four exact-order tableaux yield actual shaped witnesses over any
  characteristic-zero field.

Proofs of the positive rational order statements use `decide +kernel`,
not native-code trust. The negative statements use the reviewed
`order_bushyTree`, `factorial_bushyTree`, and `Φ_bushyTree` directly.

From the existing `ai-generated/lean` Lake package in a checkout containing
the reviewed root, run:

```sh
lake build RKCert.ReviewedNative.RationalUpperBaseChange
lake env lean AuditReviewedRationalUpper.lean
lake env lean AuditReviewedRationalFields.lean
```

The first audit also tests the negative Boolean results and enumerator grade
counts. Both audits print declarations and axiom dependencies. The four source
modules were separately replayed using Lean 4.36.0's `leanchecker` against the
reviewed root at `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5` and Mathlib
v4.36.0 (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The seven-stage module
compiled in 9.058 seconds and replayed in 8.534 seconds in the offline cache
check. No additional axioms or runtime arithmetic oracles were used.

Historical rational coefficients for classical RK4 and the order-seven DIRK
can be compared with `RKCert/RK4.lean` and `RKCert/RationalDIRK7.lean`.
Only the numerical tableau data from those files are used here; the proofs
are on the reviewed objects.
