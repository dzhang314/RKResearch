# Scalar gates for the nonhalf, low-carrier ERK11 schedule

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the four-column
independence and the Bézout identity. The [tableau and quadrature
argument](../../../research/ERK11-LOW-CARRIER-CLEAN-JACOBI-SCHEDULE.md)
uses the scalar gates but is not a native exclusion of the whole
17-stage endpoint.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk11-clean-jacobi-20261127/sources.sha256
lake build RKCert.Research.ERK11CleanJacobiGate
lake env lean -j1 evidence/erk11-clean-jacobi-20261127/AuditCleanJacobi.lean
```
