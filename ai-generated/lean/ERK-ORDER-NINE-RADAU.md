# Order-nine Radau proof delta, without a numerical promotion

The lower-order ingredients are the [early structural reductions](ERK-LOW8-9.md) and [the order-eight interpolation argument](ERK-ORDER-EIGHT-REDUCTIONS.md).

## Theorem scope

* `RKCert.Paired.order9_five_off_five_on_rank_nine_impossible`
  excludes a genuine twelve-stage order-nine tableau with five distinct
  on nodes, five distinct off nodes and dimension nine of the fifth
  full tree space, over all characteristic-zero fields. It derives
  state-valuedness from the actual rank budget, the clean fifth-grade
  tests from output aggregate cancellation, and the ratio of the
  two earliest distinct nonzero on nodes from the true primitive tests.
  The fixed Radau quartic ratio is excluded by a rational Bézout proof.
* `RKCert.Paired.order9_five_on_off_stage_five_split` establishes that
  in the same two-five count any remaining candidate has rank ten:
  a rank-nine state profile plus the non-state-valued terminal coordinate.
* `RKCert.Paired.fixedRadau_late_scalar_gate` is the manuscript's
  rank-ten fixed-Radau **scalar endpoint**, with explicit hypotheses:
  four distinct roots of the fixed Radau quartic and both affine F/G
  equations for their common shape parameter. The arithmetic uses all
  24 assignments at prime 353 and the common integral split-root
  theorem. It does not assume those F/G relations for an actual tableau
  silently. The stage-row-to-F/G bridge remains open in this packet.
* `RKCert.Paired.orderAdjoint_annih` gives the true unreflected weak
  adjoint row at every paid order budget. `orderAdjoint_of_D1` rewrites
  it in the late-column signed form. These two are over arbitrary fields
  when the stated tree order holds (no characteristic-zero axiom).

This package **does not** establish order nine requiring thirteen stages.
The rank-ten state/chronology extraction to F/G, the p9 free six-on terminal
gate, and the other remaining p9 branches are not included. 
Public leaves: `RKCert.ERKOrderNineFiveRankNine`,
`RKCert.ERKOrderNineFixedRadauCharZero`, `RKCert.ERKLowAdjoint`.

For the separate physical seven-off result, see [the exact root certificates](RADAU-ROOT-CERTIFICATES.md).
