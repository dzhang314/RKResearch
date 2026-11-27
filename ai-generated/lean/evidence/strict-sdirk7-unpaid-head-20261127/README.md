# The genuinely unpaid strict SDIRK7 witness and rational reduction

Stock Lean 4.36.0 with the pinned Mathlib checks the literal F19
tableau, the rational distinction between paid and cubic-dirty
helpers, and the denominator-cleared terminal scalar. The [research
packet](../../../research/strict-sdirk7-unpaid-head/README.md) proves
the all-power Hensel lift and algebraicity separately, with exact
replays. Those lifting and assembly arguments are not native Lean
theorems.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/strict-sdirk7-unpaid-head-20261127/sources.sha256
lake build RKCert.Research.SDIRKSevenSixActiveHead RKCert.Research.SDIRKSevenSixActiveTerminalScalar RKCert.Research.SDIRKSevenSixActiveDirtyF19
lake env lean -j1 ../research/strict-sdirk7-unpaid-head/proof-audit.lean
```
