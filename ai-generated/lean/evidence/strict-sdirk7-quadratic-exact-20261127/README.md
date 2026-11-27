# Exactness of the quadratic nine-stage strict SDIRK7 tableau

Stock Lean 4.36.0 and the pinned Mathlib check these theorems from the
actual rooted order predicate. See the [construction and independent
tree replay](../../../research/strict-sdirk7-quadratic-exact/README.md).
The new primary and mixed-primary results are upper bounds only.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/strict-sdirk7-quadratic-exact-20261127/sources.sha256
lake build RKCert.Research.SDIRKNineStageOrderSevenQuadraticExact
lake env lean -j1 evidence/strict-sdirk7-quadratic-exact-20261127/AuditQuadraticExact.lean
```
