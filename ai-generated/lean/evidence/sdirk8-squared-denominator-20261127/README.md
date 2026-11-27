# Squared-denominator gates for the strict SDIRK8 endpoint pair

Stock Lean 4.36.0 with the pinned Mathlib checks the residue-profile
independence and determination across a squared denominator. The
[tableau reductions and exact replays](../../../research/sdirk-eight-half-rational/README.md)
use those ingredients to rule out special profiles and reduce the
generic ones. They do not exclude all ten-stage methods.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk8-squared-denominator-20261127/sources.sha256
lake build RKCert.ReviewedNative.SDIRK8SquaredDenominatorReceipts
lake env lean -j1 evidence/sdirk8-squared-denominator-20261127/AuditSquaredDenominator.lean
```
