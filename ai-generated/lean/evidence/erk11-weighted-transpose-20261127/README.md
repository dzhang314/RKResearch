# Weighted-transpose gates in the all-live ERK11 endpoint chart

The five typed gates check abstract dual-flag transfers, the scalar
midpoint obstruction, an early-stage tap calculation, and the
integration-by-parts arithmetic on Lean 4.34.1, 4.35.0, 4.36.0,
and 4.37.0-rc1. The [actual tableau argument](../../../research/ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md)
uses these gates, rather than claiming a complete native reversal theorem.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk11-weighted-transpose-20261127/sources.sha256
lake build RKCert.Research.ERK11ReversalGate
lake env lean -j1 evidence/erk11-weighted-transpose-20261127/AuditReversal.lean
```
