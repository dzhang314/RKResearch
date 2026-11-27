# Arithmetic gates for the degree-324 strict SDIRK7 field

Stock Lean 4.36.0 and the pinned Mathlib check the factor-degree
intersection and the bounded CRT uniqueness rule. The [exact
polynomial replay and embedding proof](../../../research/strict-sdirk7-dirty-number-field/README.md)
apply those gates separately; Lean does not rerun the 408-prime
resultant computation or establish the embedding end to end.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/strict-sdirk7-dirty-number-field-20261127/sources.sha256
lake build RKCert.Research.SDIRKSevenDirtyDegreeReceipt
lake env lean -j1 ../research/strict-sdirk7-dirty-number-field/projection-audit.lean
```
