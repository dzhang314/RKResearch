# Native explicit order-15 forward midpoint

**Scope.** Four new additive modules plus an independent consumer and axiom audit.
The proof uses the reviewed `RKResearch.HasOrder 15 A b` directly over a
characteristic-zero field, on the original matrix. The pinned human sources
are from `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. The existing explicit
order-15 endpoint in the older representation is not imported.

* `order15_clock_escapes` assumes only strict triangularity, reviewed
  order 15 and at most 22 stages. At each of grades 5, 6 and 7, the physical
  clock sends an actual homogeneous defect outside its own grade.
* `order15_head_of_grade_five` in addition assumes at least five independent
  grade-five defects. It gives exactly 22 stages, an invariant core U, and a
  single physical head w with r≥2 and dim U+r=5. At grades 5+n, n=0,1,2,
  the defect spaces are precisely U plus the first r+n clock powers of w.
  Adjoining the next clock action on grade 7 yields exactly eight dimensions;
  the newly exhibited power lies outside the original grade-seven space.
* `ordered_hermite_outgoing` permits arbitrary chronological permutations,
  seed vectors, and target spaces, paying primitive defects directly with the
  native integral. `clock_invariant_incoming` and `clock_invariant_outgoing`
  use the strict-tableau gain floor((j+1)/2). The separation-only failed-node
  count uses a single simultaneous prefix lift from the existing pure Hermite
  algebra, not a second moment-replay packet.
* `NativeClockStaircase` is shared with the diagonal-retaining rank route.
  The proof imports the shared `ClockBlockDetection.clock_mask_invariant`;
  it does not redeclare clock masks, chain/core, tree type, elementary
  weights, RK order, or an RK-order conversion.

**Delimitation.** This is the forward part of the `head_chart_short`/
`odd_seven_chart` precursor, not a new global stage bound and not a complete
native proof that order 15 requires 23 stages. The grade-five surplus is
a separate premise of the single-head theorem, not inferred by that theorem.
No scalar arithmetic tape is included or rerun. No reviewed source was edited.

**Recheck.** Use Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`)
and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. All transitive
project-source digests are in `IMPORTS-erk15-forward.sha256` (Mathlib and
Lean excluded). Only three old RKCert module names occur outside ReviewedNative:
NodalPrimitive, NodalHermiteRank, and OneEscape. Each is pure polynomial or
subspace algebra with no RK type or order import. They were rechecked from
the exact local reviewed snapshot. The two prerequisite native odd seals are
`70c299b59cabb9f49605fb835dacc8cffddfbacedc0f806fc23691a5c9371fd0` and
`b5f9ff08bc09f91a190c492f5cc7933658d24697dc5ef63f3a1d35f40c74134a`.
Shared ClockBlockDetection source SHA-256 is
`16a70627ccc08ff7acb9e426ef7e1b3873c5e7c9846272d2a22012a3f2e8a2ec`.

Run the new modules in the sequence NativeClockStaircase, OrderedNodalGain,
ForwardNodalGain, ERKOrder15ForwardEdge, followed by AuditReviewedNativeERKOrder15Forward.
The audit's independent single-import witness compiles; all ten named declarations
report only propext, Classical.choice and Quot.sound. No broad dependency build,
remote write or human-source change was performed.
