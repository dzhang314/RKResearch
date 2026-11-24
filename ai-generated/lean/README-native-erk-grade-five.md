# Native explicit grade-five surplus

This additive delta proves `RKResearch.Certified.Graded.grade_five_surplus`:
over every characteristic-zero field, a strictly lower tableau that is
polynomial-separated through grade five has at least five independent actual
grade-five defects. It needs neither weights nor an assumed order. In
`grade_five_surplus_of_reviewed_order`, the separation is discharged directly
by actual reviewed `RKResearch.HasOrder` for any p≥10.

`order15_ordinary_forward_head` removes the sole grade-five-rank premise from
the earlier native forward head. On a strict tableau with reviewed order 15
and at most 22 stages, it forces exactly 22 stages and a single physical clock
chain from grades 5 through 7, with invariant core, head length at least 2,
and an eight-dimensional first escape space. This is not the full marked
midpoint mesh or the 23-stage obstruction.

* The dependent-quadratic fork reuses the checked native OneOff profiles. If
  grade five has rank four, the first two defect columns have disjoint
  support. The first doubled clean clock calibrates the grade-five mixed
  primitive. It then blocks a changed amplitude at that clock by two scalar
  relations on the **original** chronological rows. No distinct-row premise,
  old five-row packet, or order transfer enters this fork.
* The independent fork constructs the first clean nonzero receiver on the
  original tableau. The reusable `explicit_order_on_first_profiles` preserves
  reviewed order when retaining the earliest physical representative of
  each label and aggregating its incoming and output weights. The receiver's
  order-five floor forces five distinct earlier off clocks and the ensuing
  quartic primitive contradiction. Repeated physical rows are allowed.
* Both forks use the same existing quadratic defect and the same graded
  spaces, `FiniteRootedTree`, `Φ`, and `HasOrder`. No legacy RK predicate
  or conversion is imported.

## Verification

Checked incrementally on Lean 4.36.0
(`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`), Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, with the exact local reviewed
core at `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`, frozen native odd,
native p9 forward and profile modules, and the shared head algebra.
The earlier forward seal SHA-256 is
`400355e0aca050c6c9aea551639c7e06ef33d760e9d10fbad56ab16151bc5433`.
`IMPORTS-erk-grade-five.sha256` records the complete project-source closure.
The three module names outside ReviewedNative and RKResearch are the same
pure linear/polynomial algebra as in that earlier seal: OneEscape,
NodalPrimitive, NodalHermiteRank.

The independent consumer imports only the new public entry. All fifteen
named declarations report only propext, Classical.choice, and Quot.sound.
No human-source edits, network operations, large arithmetic replays, or
remote writes were performed. For a recheck with these local prerequisites,
use the included scoped checker with ERKGradeFiveProfiles,
ERKGradeFiveDependent, ERKProfileCompression, PrimitiveHeadFactor,
ERKGradeFiveIndependent, ERKGradeFiveSurplus, then AuditReviewedNativeERKGradeFive.
