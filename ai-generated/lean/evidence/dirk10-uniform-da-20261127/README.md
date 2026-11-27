# Uniform paid DA obstruction for an eleven-stage DIRK10 skeleton

Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1 check the generic
field identities and the exact fixed-clock gates. The [actual
tableau proof](../../../research/causal-profile-reduction/dirk-order10-uniform-paid-da-obstruction.md)
derives the signed skeleton obstruction and transports the finite
checks to characteristic zero. It is not a complete native lower
bound for arbitrary DIRK10 tableaux.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/dirk10-uniform-da-20261127/sources.sha256
lake build RKCert.ReviewedNative.DIRKOrderTenPaidDAField RKCert.ReviewedNative.DIRKOrderTenPaidDAObstructionScalar
lake env lean -j1 AuditDIRKOrderTenPaidDAObstruction.lean
```
