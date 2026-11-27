# Modular determinant receipts for the five-opening ERK10 obstruction

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the explicit
mod-227 rank and determinant computations. The [exact tableau replay
and mathematical proof](../../../research/erk10-stepanov-five-opening/README.md)
verify the fourteen-stage order-nine control and the obstruction
to order ten with the specified high-block conditions.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk10-five-opening-20261127/sources.sha256
lake build RKCert.Research.ERK10StepanovFiveOpeningMod227
lake env lean -j1 evidence/erk10-five-opening-20261127/AuditFiveOpening.lean
```
