# Order-eight explicit Runge–Kutta methods need eleven stages

This gives a direct proof of the established order-eight lower bound
in the project's reviewed rooted-tree formulation. The **Lean-checked**
ten-stage census uses strict lower triangularity and reviewed order
eight to reduce a ten-stage tableau to one or four distinct defective
clocks. The two exclusions below are **mathematical proofs, not yet
Lean certificates**.

* [One defective clock](one-off.md). The rank-nine grade-five profile
  and the physical seventh row force two incompatible roots of the
  terminal Lobatto cubic.
* [Four defective clocks](four-off-closure.md). First
  [locate the actual repeated tag and clean rows](four-off-physical.md)
  and [resolve the early Newton action](four-off-cyclic-relaxation.md).
  A divided-difference transfer then reduces the actual early
  primitive equations to a fixed clean-side calculation. It eliminates
  both possible physical positions of the first nonzero clean row.
  The [exact checker](clean_chronology.py) verifies the six fixed clean
  Lobatto orders and does not search any off clock or tableau.

The cases exhaust the verified census. Trailing zero-stage padding
preserves order and strict lower triangularity, so excluding ten
stages excludes every smaller count too. No novelty of the classical
stage minimum or full native Lean proof is claimed.

[Lean census and audits](../../lean/evidence/reviewed-native-erk-order-eight-tagged-census/README.md).
