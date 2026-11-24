# Native order-nine one-off forward chart

This source-only additive delta targets the human-reviewed `RKResearch` commit
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. It uses the reviewed
`FiniteRootedTree`, `Φ`, `HasOrder`, and matrix submatrix throughout.
All 16 modules are in `RKCert.ReviewedNative`, with dependent definitions
and theorems under `RKResearch.Certified.Graded` and its `OneOff` namespace.
The named prerequisites are exact native leaves, not an order-conversion bridge.

## Actual scope

`OneOffConstantAmplitude` exports
`RKResearch.Certified.Graded.OneOff.order9_constant_amplitude_of_capacity`.
For any characteristic-zero field, a strictly lower 12-stage matrix with
reviewed `HasOrder A b 9`, exactly one distinct nonzero-defect clock, and
`finrank K (treeSpace A 4) ≤ 8` has a `ConstantAmplitude A a d i j`
certificate. The theorem proves the earliest physical off row, the real
first integrated-quadratic innovation, the two possible initial event forms,
and the exclusions of both independent-square branches and the nonconstant
dependent-square branch. It gives a clean nonzero first innovation,
its exact coefficient equations, and globally constant off amplitude.
`ConstantAmplitude.off_weight_cancel` pays the actual aggregate output
coefficient of the off rows from the reviewed order with the native probe.

`OneOffReceiverPrefix` consumes that form: `receiver_order_two` proves
reviewed `HasOrder` for the rescaled incoming row and the whole literal
leading submatrix (not a state quotient), and `predecessor_defect_space`
identifies its grade-three defect space as the span of its own quadratic
defect. `grade_two_span` uses the reviewed finite tree enumerator.
The audit imports the final module independently and applies the public
order-nine theorem to certify the actual leading tableau at its receiver.

The reverse capacity input is explicit. It is not postulated as an axiom
and is not silently discharged by old `RKCert` order. This package does
not port the reverse saturation, the one-off terminal contradiction, the
good-prime arithmetic, or the full numerical bound p9 >= 13.

## Pinned build and exact prerequisites

* Lean v4.36.0, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
* Mathlib v4.36.0, `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
* Additive graded-spine packet based on the same reviewed commit:
  `rk-native-graded-spine-91f4ab1b-20261124.zip`,
  SHA-256 `dffb6176594b760f3e6f8d0aa2d80bf2bc2cf55efe89aa38b3adbccb20f84c52`,
  including its existing dependencies `RootMomentCuts` and `BushyMoments`.
* Existing `RKCert.ReviewedNative.FiniteOrderCheck` from the native
  compatibility packet, source SHA-256
  `f775b8a1c81fdc0a6c3a97491bd0d3b946ccd4c541c0970327749445b8508a27`.

All source leaves compiled without warnings with cached exact native
imports and no legacy package objects on LEAN_PATH. No determinant tapes,
`native_decide`, `sorry`, custom axioms, or whole-project builds were used.
All 14 public audit declarations report only `propext`,
`Classical.choice`, and `Quot.sound`.

To check the sources from `ai-generated/lean`:

```sh
lake build RKCert.ReviewedNative.OneOffReceiverPrefix
lake env lean checks/NativeOrderNineAudit.lean
```
