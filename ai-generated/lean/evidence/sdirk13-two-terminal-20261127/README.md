# Exact two-terminal mixed determinant

`RKResearch.Certified.MixedTwoTerminal.no_two_terminal_cancellation`
proves over every characteristic-zero field that two distinct nonzero
terminal primitives cannot cancel on both the quadratic terminal hull
and its first marked version, when an actual terminal coefficient
is nonzero. The determinant is
\(a^2b^2(a-b)^3/24\). Lean 4.36.0 with matching Mathlib checked the
source and separately typed import with only standard axioms.
The [eight-site application](../../../research/real-sdirk13-joined-interface/README.md)
uses exact directed algebraic receipts for the two residual ranks,
rather than claiming their formalization in this module.

From `ai-generated/lean`:

```sh
sha256sum -c evidence/sdirk13-two-terminal-20261127/sources.sha256
lake build RKCert.ReviewedNative.MixedTwoTerminal
lake env lean -j1 evidence/sdirk13-two-terminal-20261127/AuditMixed.lean
```
