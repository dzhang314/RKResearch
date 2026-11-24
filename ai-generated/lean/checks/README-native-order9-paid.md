# Native order-nine one-off paid and maximal physical chart

This is an additive source-only packet against the reviewed RKResearch
source at commit `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. The existing
native one-off forward proof has been integrated on main `9282401`;
these files are new `RKCert.ReviewedNative` leaves, not changes to it or
the reviewed definitions. The tableau, prefix, tree weights, and order
predicate are native reviewed data throughout.

## Main theorem and boundary

`RKResearch.Certified.Graded.OneOff.order9_one_off_maximal_chart`
in `RKCert.ReviewedNative.OneOffMaximal` assumes only a characteristic-zero
field, a strict lower physical twelve-stage tableau, reviewed `HasOrder A b 9`
and one distinct clock with nonzero quadratic defect. It proves the global
normal form and exact ordered first four physical feature rows; the fifth
physical row is clean at the same doubled clock as the fourth but has
different integrated quadratic defect. It proves grade-five rank ten and
identifies the whole grade-five column space with the genuine ten-column
polynomial/defect profile. It proves the anchored Radau polynomial is
nonzero at the doubled clock and that clock differs from 1.

The preceding grade-four reverse cap is **derived**, not assumed. In
`OrderNineOneOffPaid`, the native paid capacity proves that order nine and
at most twelve stages force exactly twelve stages and exact ranks
F3=2, F4=3, E3=6, E4=8. The one-off theorem derives the full constant-amplitude
chart and reviewed order 2 of its first clean receiver's rescaled literal
prefix with no rank premise. `MergeEqualRows` preserves reviewed order and
strictness over a commutative semiring when contracting literally identical
incoming rows; the stage floor prohibits duplicates in the actual p9
physical chart. It does not merge rows merely because they have a common node.

The anchored profile uses `Polynomial.ofFn` and the reviewed probes.
`OrderNineGradeFive` consumes the canonical native reverse chart to show a
maximal grade-five space contains the live physical final unit coordinate
at node 1, but grade four does not. Multiplying by that coordinate pays
the terminal zero for every grade-three defect at full fifth rank.
`OneOffDefectSeparation` then proves pointwise `g A * h A = 0` on the
actual tableau (no assumptions on the individual b values).

This packet does **not** close the one-off terminal contradiction or
establish a native numerical lower bound of thirteen. It does not
check or change any good-prime arithmetic tape or legacy order certificate.

## Verification and prerequisites

* Lean v4.36.0 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`;
  Mathlib v4.36.0 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
* Prerequisite graded-spine packet:
  `rk-native-graded-spine-91f4ab1b-20261124.zip`, SHA-256
  `dffb6176594b760f3e6f8d0aa2d80bf2bc2cf55efe89aa38b3adbccb20f84c52`.
* Prerequisite native one-off forward packet:
  `rk-native-order9-one-off-forward-91f4ab1b-20261124.zip`, SHA-256
  `7c6694477cb2882612bc372397e04828e9badda9e572a9f1cc9d4600753fd83f`.
* Prerequisite shared native paid endpoint packet:
  `rk-reviewed-native-paid-endpoint-count-91f4ab1-20261124.zip`, SHA-256
  `b5f9ff08bc09f91a190c492f5cc7933658d24697dc5ef63f3a1d35f40c74134a`.
* Prerequisite native reverse-saturation packet:
  `rk-reviewed-native-odd-saturation-91f4ab1-20261124.zip`, SHA-256
  `70c299b59cabb9f49605fb835dacc8cffddfbacedc0f806fc23691a5c9371fd0`.
  The concrete consumers here are `EndpointAdjoint`, `OrderNineReverseChart`,
  and the audited imports of those two native modules.

Each new leaf compiled without warnings in the listed topological order.
An independent import-only audit coerces the actual input to no other
tree/order API, and proves the terminal consequences without extra
assumed rank, node, or weight hypotheses. It checks 18 public declarations
and reports only `propext`, `Classical.choice`, `Quot.sound`. No legacy
objects were on LEAN_PATH; no `sorry`, `native_decide`, custom axioms,
or broad Lake rebuilds were used.

To check these sources from `ai-generated/lean`:

```sh
lake build RKCert.ReviewedNative.OneOffMaximal
lake env lean checks/NativeOrderNinePaidAudit.lean
```
