# Causal defect pivots in the actual strict prefix

Import `RKCert.ReviewedNative.CausalDefectPrefix`. The checked
`RKResearch.Certified.Graded.DefectPrefix.paid_prefix_pivots`
is a local theorem over an arbitrary field and stage width.
It uses a strictly lower-triangular tableau, actual incoming
quadratic-defect polynomial probes through degree `d` vanishing at
the recipient row, agreement of the nonzero defect at earlier off
copies of the same clock, and a nonzero weighted clock receipt from
those earlier off rows.

The conclusion is at least `d + 2` distinct earlier off clock groups
with nonzero grouped incoming residue, as well as a `TriangularPrefix`
witness of size `d + 2`. Its pivots are physical indices strictly
before the recipient. Each column vanishes at every physical index
before its pivot and is nonzero there; their restrictions to the actual
leading prefix are linearly independent. Pivot representatives are the
first off occurrences of their clocks, not necessarily the nonzero
taps themselves. There is no RK order premise or conclusion, earned
band-equality assertion, stage-bound update, or implicit-tableau claim.

## Exact measured check

The [body](../../RKCert/ReviewedNative/CausalDefectPrefix.lean) and the
[standalone no-output audit](../../AuditReviewedNativeCausalDefectPrefixCore.lean)
exited zero with Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The two typed clients
check the expanded input interface and the actual prefix witness.
The [unchanged raw audit](typed-audit-output.txt) reports exactly
`propext`, `Classical.choice` and `Quot.sound` for the named theorem.
The audit emitted no object.

[Acceptance](acceptance.tsv) records the two measured source hashes,
compiler exits, raw log hashes and, for the body only, the admitted
primary object hash. No object is shipped. All 14 previously reviewed
project predecessor sources match their measured bytes in integration
base `d703297556dc6779b15f066900aacf289304d78c`. The measured
replay used one project object root and 3,538 pinned external modules,
not a cold package build. The two narrow elaboration repairs inline
the unchanged fibre filter instead of publishing a private helper,
and specify the existing sum's field-valued summand. They do not
change the public types or underlying mathematical argument.

From the repository root with the pinned toolchain and dependencies
already present:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-causal-defect-prefix-20261125/checked-sources.sha256
cd ai-generated/lean
LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.CausalDefectPrefix
LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeCausalDefectPrefixCore.lean
```
