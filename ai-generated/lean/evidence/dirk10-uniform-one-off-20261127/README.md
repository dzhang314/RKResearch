# Exact finite arithmetic for the uniform DIRK10 one-off exclusion

The two finite polynomial certificates are kernel-checked on
Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The [actual tableau
argument and independent modular replay](../../../research/causal-profile-reduction/dirk-order10-uniform-one-off-exclusion.md)
connect the arithmetic to characteristic zero without a weight or
signed-block census. That connection is not yet a native theorem.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/dirk10-uniform-one-off-20261127/sources.sha256
lake build RKCert.ReviewedNative.DIRKOrderTenUniformOneOffPolynomialScalar
lake env lean -j1 AuditDIRKOrderTenUniformOneOffPolynomialScalar.lean
```
