# Exact arithmetic gates for the fourteen-stage ERK10 equality case

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the thirteen
scalar gates. The [actual tableau argument](../../../research/ERK10-FOURTEEN-STAGE-EQUALITY.md)
derives the equality ranks and the two remaining all-live quadratic
defect profiles under its independence hypothesis. Zero-weight and
dependent-defect branches remain separate. This is not an exclusion
of arbitrary fourteen-stage tableaux.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk10-fourteen-stage-equality-20261127/sources.sha256
lake build RKCert.Research.ERK10EqualityClockGate
lake env lean -j1 evidence/erk10-fourteen-stage-equality-20261127/AuditERK10Equality.lean
```
