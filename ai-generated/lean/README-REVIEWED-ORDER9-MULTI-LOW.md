# Order nine: native multi-off lower census

Six additive leaves against reviewed `RKResearch.HasOrder`; no new tableau,
tree, order predicate or compatibility bridge. No human source changes.
The unchanged human basis is commit 91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5.
The one-off endpoint is the separately checked 9d798055… source packet.

* For a strict explicit 12-stage order-nine tableau in characteristic zero,
  the distinct quadratic-defect clock count is either one or at least five:
  `RKResearch.Certified.Graded.MultiOff.order9_low_census`.
* Over an ordered field the existing one-off exclusion also applies, so
  **every explicit order-nine tableau with at most four distinct defective
  clocks requires at least thirteen stages**. The new theorem is
  `explicit_order_nine_at_most_four_off_at_least_thirteen`, in the same namespace.
* If there are between three and seven defective clocks, every defective
  clock has zero aggregate output weight and at least five clean clocks remain
  (`order9_multi_quadrature`). Four or more such defective clocks permit at
  most six clean clocks. The weights of clean rows sharing defective clock
  values are never incorrectly cancelled.
* The growing polynomial-clock bands are ranges of actual native degree
  evaluation maps. Two clocks saturate the third homogeneous grade and violate
  outgoing Hermite gain. Three clocks saturate grade four and violate incoming
  gain; unlike the legacy chronology this proof has no three-row case split.
  Four-clock exclusion uses complete grade-five interpolation and an unanchored
  reflected rank gain when grade five is not full.
* The independent scalar handoff `six_on_witness_impossible` consumes the
  checked `RKCert.CompactResidue.sixOn_atlas_impossible` with only scalar
  hypotheses. Neither the large residue rows nor their factorization were
  replayed. This handoff alone does not supply the physical (5,6) witness.

## Scope and remaining work

This packet is not the arbitrary-tableau numerical stage bound. The native
physical (5,6) atlas and the remaining large/middle counts must still be
discharged. For the legacy dependency route see ERKOrderNineCensus,
ERKOrderNineFiveSixAtlas and ERKOrderNineCompactPrime at the reviewed baseline.
The generic linear and polynomial facts use original (not merged) stage rows.

## Validation

Lean 4.36.0 (611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9), mathlib
v4.36.0 (fc4f59e577feb1a4956671bc04ac18aaaf8cd842). Each new leaf was
compiled with lean -j 1 against the previously checked native and arithmetic
objects. Import order: OrderNineMultiHead, OrderNineMultiMoments,
OrderNineMultiStates, OrderNineMultiFour, OrderNineMultiLow; OrderNineMultiScalar
is independent. See AuditReviewedNativeOrderNineMultiLow.lean for a direct
reviewed consumer, exported signatures and transitive axiom checks.
