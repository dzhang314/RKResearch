# Native tagged census for a ten-stage explicit order-eight tableau

The reviewed theorem [order8_native_one_or_four_with_horizon](../../RKCert/ReviewedNative/ERKOrderEightTaggedCensus.lean)
takes a literal `A : Matrix (Fin 10) (Fin 10) K`, `b : Fin 10 → K`,
strict lower triangularity of A, and `RKResearch.HasOrder 8 A b`,
over any characteristic-zero field. It concludes the actual
`ERKEvenHorizon A b 4` and that the off-tagged support has cardinality
one or four. The sibling `order8_native_tagged_census` also gives
exactly five clean-tagged clocks in the four-off branch.
A clock can occur with both tags: the tags use the actual quadratic
stage defect on each row, and physical rows are not identified.

The horizon pays the ranks and physical endpoint. The proof uses
actual tagged cancellation, origin-anchored moments, and the cubic
Lobatto primitive tests. It uses no clock ranges, weight signs,
order-nine hypothesis, or legacy tableau conversion. Neither the one-off
nor the four-off branch is ruled out here. This does **not** certify an
eleven-stage floor or change any stage-minimum entry.

## Checked sources and receipts

- [Pure cubic Lobatto arithmetic](../../RKCert/ReviewedNative/ERKOrderEightLobattoScalar.lean),
  [tagged profile and moment support](../../RKCert/ReviewedNative/ERKTaggedHorizonSupport.lean),
  and the [census](../../RKCert/ReviewedNative/ERKOrderEightTaggedCensus.lean)
  compiled from the exact published source bytes in the ledger below.
  The scalar layer uses the reviewed polynomial primitive directly. The
  tagged support uses the reviewed `GradedProducts` closure.
- The standalone [support audit](../../AuditReviewedNativeERK8ThinSupport.lean)
  and [census audit](../../AuditReviewedNativeERK8TaggedCensus.lean)
  both passed without producing an object. The census audit checks the
  ordered-field compressed statement and the characteristic-zero tagged
  statement on the literal ten-stage tableau. Their unedited
  [support](support-axiom-audit.txt) and [census](census-axiom-audit.txt)
  output each reports three named theorems, with only `propext`,
  `Classical.choice`, and `Quot.sound`.
- [Warm checks](warm-checks.tsv) list all 36 measured object builds and
  both no-output audits, in successful replay order. Every row records
  the repository-relative source path, source and raw log hashes, actual
  compiler exit, and any compiled artifact hashes. The census build
  emitted five unused-section-variable linter warnings and no errors.
  The existing 33 project provider source bytes and package configuration
  are identical at the integration base
  `12a6517d8819865f0bad1898237f4efcf6248546`.
- The check used `Lean 4.36.0` and the locked Mathlib revision
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Project objects were
  built in one isolated family using already available pinned external
  package objects. This is warm kernel and typed-audit evidence, not a
  cold dependency build or a separate `leanchecker` run. No compiled
  objects or machine-local paths are included.

## Replay

With the pinned toolchain and dependencies available, check the source
ledger from the repository root, then build the named target and run
the two audits from the certificate package:

~~~sh
receipts=ai-generated/lean/evidence/reviewed-native-erk-order-eight-tagged-census
awk -F '\t' 'NR > 1 {print $5 "  " $4}' "$receipts/warm-checks.tsv" | sha256sum -c -
cd ai-generated/lean
lake build +RKCert.ReviewedNative.ERKOrderEightTaggedCensus
lake env lean -j1 -M3000 AuditReviewedNativeERK8ThinSupport.lean
lake env lean -j1 -M3000 AuditReviewedNativeERK8TaggedCensus.lean
~~~

The historical run built one module at a time, using one Lean thread.
For low-memory replay, use the object rows of the ledger in order.
