# Reviewed-native odd saturation, exact 91f4ab1 proof inputs
These five additive proof leaves work directly with the reviewed
`RKResearch.HasOrder`, over arbitrary fields. No legacy-tree bridge is imported.

- `OddHorizon`: ordinary odd floor, and exact actual reverse flag at a saturated midpoint. The first-seed-zero branch has an earned last-active marked coordinate.
- `OddForwardBudget`: next-grade origin/Cauchy room and `odd_short_frame`, conditional only on the explicitly stated forward rank surplus and stage cap.
- `TerminalCapacity`: arbitrary-grade paid saturation and actual last-active collateral; a genuinely unused output suffix can be dropped solely to earn physical last output nonzero at the ordinary floor.
- `ReverseInvariantBudget`: each jointly invariant plane in the actual annihilator pays its own dimension in addition to all paid reverse gains; no nonzero such plane remains at a saturated unmarked cap.
- `OrderNineReverseChart`: complete native reverse chart in the hypothetical physical twelve-stage order-nine rank-ten branch. It does not exclude that branch by itself.

These modules use the pinned Lean and Mathlib 4.36.0 toolchain.
To check them from `ai-generated/lean`:

```sh
lake build RKCert.ReviewedNative.OrderNineReverseChart RKCert.ReviewedNative.OddForwardBudget
lake env lean AuditReviewedNativePaidRoom.lean
lake env lean AuditReviewedNativeOddSaturation.lean
```
