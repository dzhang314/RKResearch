# The native order-fifteen width-22 chart has head length two

The actual stage space, clock, matrix and order statement are from the
reviewed RKResearch API. In particular the consumer takes
`RKResearch.HasOrder 15 A b` without any conversion. No branch changes the
tableau or assumes distinct physical stage clocks.

* `PhysicalHeadKnot`: The first stage not represented by the live core or
  head has nonzero tested polynomial, zeros the same paid mesh, and has
  zero native primitive on the entire paid window. The X and X(X-u)
  filters give two distinct nonzero omitted physical clocks. If G=P·Q,
  they are actual roots of Q, not P.
* `ERKOrder15LargeKnots`: The actual grade-six space pays degree at most
  three in head multipliers, and the actual grade-seven space supports
  the primitive defects. The grade-eight first-escape mesh is retained.
* `PhysicalEndpointMomentPorts`: Pure polynomial normalization to the
  reviewed exact `EndpointPhysical.normalize` and `Endpoint.match3`.
  There is no repeated fixed-degree arithmetic or legacy tree import.
  The same interface supplies the already-reviewed ordered quartic rule.
* `ERKOrder15RankTwoChart`: The checked P·Q mesh and its two physical
  pivots exclude r≥3 over every characteristic-zero field. Thus
  `order15_rank_two_staircase` earns r=2 on every hypothetical width≤22
  native order-fifteen tableau.
* `ERKOrder15PaidQuarticCut`: A short shared consumer. If the rank-two
  chart has a disjoint degree≤4 head already in grade four, the same
  knot argument forces the native terminal mark and actual entry in E8
  over an ordered field. Extraction of this rank-two profile is not
  asserted. The remaining marked terminal and scalar pencil endgame,
  and the full stage lower bound, are not asserted.

Lean: pinned v4.36.0, `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
Mathlib: `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
Reviewed snapshot: `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
`checks/build.sh` compiles the two reviewed tree-free scalar files and
two shared native/core leaves from their exact source; it reuses the
prior head-isolation objects and pinned Mathlib. All new objects are
placed under /tmp. The audit replays all five new modules independently
and checks the declarations through a single final import.
