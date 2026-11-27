# Literal early-tap receipts for strict SDIRK order eight

Stock Lean 4.36.0 with the pinned Mathlib checks the early cubic
from two literal taps and its incompatibility with the five-site
Hankel gate in the eight relative phases. The [mathematical
tableau reduction and five exact replays](../../../research/sdirk-eight-half-equal/README.md)
cover more cases separately; this is not a native theorem excluding
the full eight-order ten-stage endpoint.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk8-half-pair-20261127/sources.sha256
lake build RKCert.ReviewedNative.SDIRK8HalfPairReceipts
lake env lean -j1 evidence/sdirk8-half-pair-20261127/AuditHalfPair.lean
```
