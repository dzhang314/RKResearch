# Exact algebraic gates for the finite SDIRK8 quadratic-profile reduction

Stock Lean 4.36.0 and the pinned Mathlib check the ring-generic
cleared Vandermonde, affine elimination, and six-peg Hankel
identities. The [actual-tableau proof and quotient replays](../../../research/sdirk-eight-half-quadratic/README.md)
prove the finite-profile result separately. They do not exclude its
finite survivors.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk8-half-quadratic-20261127/sources.sha256
lake build RKCert.ReviewedNative.SDIRK8HalfQuadraticReceipts
lake env lean -j1 evidence/sdirk8-half-quadratic-20261127/AuditHalfQuadratic.lean
```
