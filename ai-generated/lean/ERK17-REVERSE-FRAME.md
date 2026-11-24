# Native ERK17 width and reverse support dispatch

Target input: the exact reviewed `RKResearch.HasOrder` at
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. Everything in this packet uses that
predicate directly. The four new module sources are under
`ai-generated/lean/RKCert/ReviewedNative/`; no old source is changed.

- **ReverseClockGain** is order- and width-parametric. For the literal
  all-monomial flag `primitiveBack A b n`, clock invariance and n+2≤p pay
  floor((n+2)/2) new dimensions at n+1. The flag gains actual reflected
  primitives by its known monomial credits. A finite Cauchy detector and
  the exact reflected bush moments give the required number of failed blocks.
  The existing outgoing Hermite theorem supplies the rank gain. No positivity
  or legacy tableau/tree conversion is used.
- **WeightedClockBand** is tree-free. Its polynomial evaluation rank is the
  degree cap when there are enough distinct nonzero-weight clock values.
  At saturation, the short band equals the entire weighted-evaluation range,
  by reduction modulo the genuine nodal polynomial. The full range is
  clock-invariant. Theorems also cover zero active clocks and zero dimension.
- **ERK17WidthFrame** earns the unconditional 25-stage floor in characteristic
  zero by consuming the independently checked grade-five surplus.
  At width 26, dim F8 is eight or nine. At nine, the exact reviewed midpoint
  has 18 forward dimensions and eight complementary dimensions; the two
  seed branches have their true annihilator cover and exact flags.
  The vanishing first seed gives a genuine last-active stage at clock 1
  and a zero quadratic seed on that stage. Making that index the *final
  physical row* requires the grade-eight surplus also on any trimmed
  prefix; the theorem with that premise makes the dependence explicit.
  At every n=2,…,7 the actual primitive reverse flag then cannot be clock
  invariant. At n=7 the zero branch is charged the real terminal mark.
- **ERK17ReverseSupport** excludes 3–8 distinct weighted clock values of
  a nonzero linear first seed. Either it has at most two values or it has
  at least nine and its degree-≤7 evaluation band is the whole actual
  grade-eight annihilator. For a vanishing first seed, if the quadratic
  seed has two or more distinct clock values, it has at least eight; the
  degree-≤6 evaluation band is the actual terminal-zero annihilator.
  The lone quadratic-site case is not closed here.

Remaining: show the uniform grade-eight surplus (or independently dispose
of the width-26 rank-eight alternative), the broad/tiny nonzero exclusion,
and the actual zero-seed hidden/contrast geometry that produces the
four-clock data. The reverse dispatch is not a bound of 27 by itself.
The earlier scalar and physical endgame packets and StagePadding are unchanged.

`checks/run_small.py` uses only already checked Lean 4.36 source-matched
objects and runs four named builds, four exact named independent replays,
and one exact-reviewed consumer audit. The source closure contains only
reviewed/native or tree-free prerequisites, not a legacy RK proof, norm
pair, arithmetic leaf or order bridge.
