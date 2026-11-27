# Native strict grouped protected-coordinate obstruction

Lean 4.36.0 with matching Mathlib checked the physical
protected-coordinate implication at exactly the stage count,
interpolation on the live representatives, the two-source
commutator calculation, and the final active triangular
solve. A separate typed import verifies both order-specific
count substitutions; only standard axioms are present.
The [ordinary and stage-level application](../../../research/real-sdirk15-overlapping-terminal/README.md)
makes the exact bridge and fixed-stem hypotheses explicit.
Other releases were not independently run here.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk-protected-terminal-refund-20261127/sources.sha256
lake build RKCert.ReviewedNative.ProtectedTerminalRefund
lake env lean -j1 evidence/sdirk-protected-terminal-refund-20261127/AuditProtectedRefund.lean
```
