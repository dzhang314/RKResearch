# Native grouped-terminal refund

`RKCert.ReviewedNative.GroupedTerminalRefund` verifies the
nodal clock frame, annihilator rank and actual next-word refund,
the four-block paid commutator dimension argument, and the
conditional 26-/34-stage count inequalities. The
[stage-level explanation](../../../research/real-sdirk-grouped-terminal-refund/README.md)
states which actual bridge and exact algebraic stem hypotheses
are used separately. Lean 4.36.0 with matching Mathlib compiled
the module and a typed downstream audit. Only standard axioms
are present. Other versions were not independently run here.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk-grouped-terminal-refund-20261127/sources.sha256
lake build RKCert.ReviewedNative.GroupedTerminalRefund
lake env lean -j1 evidence/sdirk-grouped-terminal-refund-20261127/AuditRefund.lean
```
