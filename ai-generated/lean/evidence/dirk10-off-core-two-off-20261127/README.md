# Scalar gates for the active DIRK10 off-core two-off-clock cases

The finite gates for the [terminal-unique](../../../research/causal-profile-reduction/dirk-order10-active-off-core-two-off-unique-terminal.md)
and [head-at-one](../../../research/causal-profile-reduction/dirk-order10-active-off-core-head-at-one.md)
cases were checked on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.
Their source mathematical bridges and independent modulo 419/719
replays are separate from the native finite checks.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/dirk10-off-core-two-off-20261127/sources.sha256
lake build RKCert.ReviewedNative.DIRKOrderTenOffCoreTwoOffScalar RKCert.ReviewedNative.DIRKOrderTenOffCoreHeadOneScalar
lake env lean -j1 AuditDIRKOrderTenOffCoreTwoOffScalar.lean
lake env lean -j1 AuditDIRKOrderTenOffCoreHeadOneScalar.lean
```
