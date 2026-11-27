# Literal completion of a paid missing column

The native module `RKCert.ReviewedNative.OneDefectCompletion` checks
three reusable facts over fields: projecting along a missing direction
does not change a response that kills it; completion by an actual
numerical observation preserves the literal physical row when the
same column has been paid; and a last live representative's paid
column forces its shifted primitive to vanish. Lean 4.36.0 with
matching Mathlib also passed the separately typed import audit
with standard axioms only. The rank and real-coordinate instantiations
in the [coupled-stage note](../../../research/real-sdirk13-coupled-one-defect/README.md)
have exact external receipts, not further Lean theorems here.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk13-coupled-one-defect-20261127/sources.sha256
lake build RKCert.ReviewedNative.OneDefectCompletion
lake env lean -j1 evidence/sdirk13-coupled-one-defect-20261127/AuditCompletion.lean
```
