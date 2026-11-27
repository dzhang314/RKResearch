# ERK11 four-carrier tap gates

Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1 check the five
elementary scalar and path gates in the [actual two-ended tableau
argument](../../../research/ERK11-FOUR-CARRIER-FIVE-TAP.md).
The argument does not decide the whole 17-stage endpoint.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk11-four-carrier-tap-20261127/sources.sha256
lake build RKCert.Research.ERK11FourCarrierTapGate
lake env lean -j1 evidence/erk11-four-carrier-tap-20261127/AuditFourCarrier.lean
```
