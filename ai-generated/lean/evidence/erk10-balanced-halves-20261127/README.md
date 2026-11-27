# Scalar gates for the balanced ERK10 two-half chronology

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check seven
arithmetic gates. The [actual-tableau proof](../../../research/ERK10-BALANCED-SEVEN-SEVEN.md)
uses them to locate the paired defects across the middle split and
derive a new paid mixed order condition. The unrestricted stage
bound is unchanged.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk10-balanced-halves-20261127/sources.sha256
lake build RKCert.Research.ERK10BalancedHalfGate
lake env lean -j1 evidence/erk10-balanced-halves-20261127/AuditBalanced.lean
```
