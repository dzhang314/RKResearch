# Algebraic gates for the ERK11 two-front noninvariance argument

Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 check the three
scalar gates for the [mathematical tableau
reduction](../../../research/ERK11-TWO-FRONT-CLOCK-NONINVARIANCE.md).
The full 17-stage endpoint remains open.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk11-two-front-gram-20261127/sources.sha256
lake build RKCert.Research.ERK11TwoFrontGramGate
lake env lean -j1 evidence/erk11-two-front-gram-20261127/AuditTwoFront.lean
```
