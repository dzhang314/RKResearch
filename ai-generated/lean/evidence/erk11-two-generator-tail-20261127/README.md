# Scalar gates for the 17-stage ERK11 endpoint

The four versioned transcripts check the scalar gates natively under
Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The gates do not
formalize the actual tableau and rank arguments. See the
[two-generator reduction](../../../research/ERK11-TWO-GENERATOR-ENDPOINT-TAIL.md),
[all-live refinement](../../../research/ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md),
and [adjoint duality](../../../research/ERK11-ADJOINT-PURE-DUALITY.md).
The order-eleven interval stays 17–18 stages.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/erk11-two-generator-tail-20261127/sources.sha256
lake build RKCert.Research.ERK11LiveTailGate RKCert.Research.ERK11TwoGeneratorTailGate
lake env lean -j1 evidence/erk11-two-generator-tail-20261127/AuditTail.lean
```
