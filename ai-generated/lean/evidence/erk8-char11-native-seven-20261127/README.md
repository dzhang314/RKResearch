# Native exclusion of the characteristic-11 seven-off ERK8 branch

Stock Lean 4.36.0 and the pinned Mathlib check the actual ten-stage
tableau exclusion from strict explicitness, order eight, characteristic
11, and the seven-off count. The [proof chain and source digests](../../../research/erk8-char11-native-seven-exclusion/README.md)
explain the native census corollaries and which other branches are
not covered.

From `ai-generated/lean`:

```sh
lake build RKCert.ReviewedNative.ERK8CharElevenHighExclusion
lake env lean -j1 evidence/erk8-char11-native-seven-20261127/AuditSevenOff.lean
```
