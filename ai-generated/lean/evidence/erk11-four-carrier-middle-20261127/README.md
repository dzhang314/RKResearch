# Algebraic gates for the ERK11 four-carrier middle block

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the nine
scalar gates for the [actual two-ended tableau argument](../../../research/ERK11-FOUR-CARRIER-MIDDLE-GATES.md).
The ordered-field middle tap pattern is not a native exclusion of
the 17-stage endpoint.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk11-four-carrier-middle-20261127/sources.sha256
lake build RKCert.Research.ERK11MiddleDefectGate
lake env lean -j1 evidence/erk11-four-carrier-middle-20261127/AuditMiddle.lean
```
