# Checked Lean and Mathlib releases

The [latest four-pair release report](../release-compatibility-b083e10/README.md) verifies the 469-module proof tree at `b083e10` with its cumulative portability patch. On x86-64 Linux, the same source passed matched Lean and Mathlib versions v4.34.1, v4.35.0, v4.36.0, and the current v4.37.0-rc1. Each clean run compiled all 469 proof modules and the umbrella, compiled all 43 audit scripts (875 queries), and ran 43 named kernel replays.

The proof edits are applied to the matching files in this commit. The default pins remain Lean and Mathlib v4.36.0. The report and reproduction commands cover only the exact tested source, not proof files added after `b083e10`. Historical release candidates and mismatched Lean/Mathlib pairs are not tested.

Earlier snapshots: [280 modules](../release-compatibility-eb274e3/README.md), [192 modules](../release-compatibility-1e545bba/README.md), [152 modules](../release-compatibility/README.md).
