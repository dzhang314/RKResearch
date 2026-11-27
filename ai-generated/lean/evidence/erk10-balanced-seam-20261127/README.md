# Exact root and determinant receipts for the balanced ERK10 exclusion

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the closed
integer interval computations: four Lobatto-root brackets and
separation of all twenty-four seam determinants from zero.
The [actual tableau proof](../../../research/ERK10-BALANCED-SEAM-EXCLUSION.md)
turns these into the characteristic-zero exclusion of one equality
branch, not an unrestricted stage-floor theorem.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk10-balanced-seam-20261127/sources.sha256
lake build RKCert.Research.ERK10BalancedSeamDeterminants
lake env lean -j1 evidence/erk10-balanced-seam-20261127/AuditSeam.lean
```
