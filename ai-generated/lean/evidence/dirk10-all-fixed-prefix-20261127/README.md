# DIRK10 all-fixed, one-dirty-clock arithmetic

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the scalar guards
and exclusions for the characteristic-zero proof in the
[tableau argument](../../../research/causal-profile-reduction/dirk-order10-all-fixed-prefix-exclusion.md).
The reduction from rooted order conditions and the transfer from
the modular arithmetic are mathematical parts of that argument.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/dirk10-all-fixed-prefix-20261127/sources.sha256
lake build RKCert.ReviewedNative.DIRKOrderTenAllFixedPrefixScalar
lake env lean -j1 AuditDIRKOrderTenAllFixedPrefixScalar.lean
```
