# Native exclusion of the characteristic-11 five-off ERK8 branch

Stock Lean 4.36.0 and the pinned Mathlib check the exclusion from
the actual strict ten-stage tableau and order-eight conditions.
The [proof chain and source digests](../../../research/erk8-char11-native-five-exclusion/README.md)
give the native field census and identify the remaining branches.

From `ai-generated/lean`:

```sh
lake build RKCert.ReviewedNative.ERK8CharElevenFiveExclusion
lake env lean -j1 evidence/erk8-char11-native-five-20261127/AuditFiveOff.lean
```
