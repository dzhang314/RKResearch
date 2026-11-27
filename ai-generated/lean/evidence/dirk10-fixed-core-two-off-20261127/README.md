# Scalar checks for the fixed-core, two-off-head DIRK10 chart

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the late-event
guards and the split finite checks for the early cases. The [actual
tableau argument](../../../research/causal-profile-reduction/dirk-order10-active-fixed-core-two-off.md)
derives the scalar gates under the active nonconstant fixed-core
hypotheses. It does not decide the unrestricted stage bound.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/dirk10-fixed-core-two-off-20261127/sources.sha256
lake build RKCert.ReviewedNative.DIRKOrderTenFixedCoreTwoOffScalar
lake env lean -j1 AuditDIRKOrderTenFixedCoreTwoOffScalar.lean
```
