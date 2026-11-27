# Cubic purity of the six-stage SDIRK7 tail in the paid-head chart

Stock Lean 4.36.0 and the pinned Mathlib check the conditional
conclusion from the actual rooted order predicate. This is not
a lower bound for arbitrary nine-stage candidates.
See the [proof and independent linear-algebra replay](../../../research/strict-sdirk7-dirty-tail/README.md).

From `ai-generated/lean`:

```sh
sha256sum -c evidence/strict-sdirk7-cubic-purity-20261127/sources.sha256
lake build RKCert.Research.SDIRKSevenTailCubicPurity
lake env lean -j1 evidence/strict-sdirk7-cubic-purity-20261127/AuditCubicPurity.lean
```
