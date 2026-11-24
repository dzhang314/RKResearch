# Native physical endgame for the ERK17 zero-seed branch

This packet is additive to the exact reviewed input
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5` and the checked ERK17 scalar packet.
It places the remaining upstream producer obligation on the original strict
matrix. No old tableau or order conversion is used.

`RKResearch.Certified.ERK17.PhysicalFourPort A w θ P` needs:

- A degree-at-most-five polynomial. Exactly four different clocks carry a
  nonzero signed measurement w. At each such clock, P does not vanish.
- The feeder θ vanishes at inactive rows except possibly the very last
  physical row, which is never an earlier source. If the first physical
  measurement is absent, P vanishes at zero.
- The signed degree-ten quadrature rule against (1−X)P and the degree-two
  actual primitive rule at live measurements (both with the formal primitive
  normalized at zero).

There is no assumed count of active rows, no need for the original RK output
weights in the record, no positivity of the four signed measurements, and no
pencil shape. A tight old proof may have additional information such as exact
active-row count or equality θ=P(c) at active rows; the final consumer does not
need those additional fields.

`ERK17PhysicalPorts` compiles on a native-only dependency root. With the
origin active, `mesh_of_origin` picks the first nonzero active physical
clock. All earlier active clocks are zero. Causality applied to X and X² makes
the two local moments zero; the quadrature on the three nonzero clock values
then gives the checked cubic-cofactor mesh. With no active origin,
`no_origin_of_quartic` writes P=XQ and picks the first active clock and the
first distinct active clock. Three tests at the first and two tests
annihilating its clock at the second give exactly the scalar quartic gate.

`ERK17PhysicalFromReplay.no_physical_four_port` closes both branches over
every ordered field, with the frozen norm pair and the existing ordered
quartic polynomial lemma. That scalar adapter privately imports legacy
files, but does not consume an old method theorem. In Lean the theorem is
`RKResearch.Certified.ERK17.no_physical_four_port`. The consumer checks the
exact reviewed `HasOrder A b 17` on 26 stages while explicitly assuming the
geometric record as a premise.

To finish native ERK17, derive this record from the actual zero-seed
width-26 rank/hidden/contrast geometry, and handle the separate nonzero-seed
branch at width 26. The checked `StagePadding` lemma then lifts an exact-width
exclusion, without a separate preliminary uniform count theorem. This packet
does not establish either of the upstream physical branches.

Run `python3 checks/run_small.py` for the two scoped new source builds, their
independent kernel replays, and the client/axiom checks. All old objects are
read only; the native front end never sees the legacy algebra/replay modules.
