# Corrected finite scalar gates for the DIRK10 one-off case

The three finite certificates are checked by the Lean kernel on
4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. They concern the modular
scalar equations only. The [mathematical reduction and independent
Python replays](../../../research/causal-profile-reduction/dirk-order10-paid-one-off-repair.md)
explain how those equations arise in an actual tableau and how the
finite tests are transported to characteristic zero.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/dirk10-paid-one-off-repair-20261127/sources.sha256
lake build RKCert.ReviewedNative.DIRKOrderTenPaidOneOffRepairScalar
lake env lean -j1 AuditDIRKOrderTenPaidOneOffRepairScalar.lean
```
