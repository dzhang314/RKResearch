# Order 16, width 24: the ordinary four-site contrast

The reviewed order-first `RKResearch.HasOrder 16 A b` is used throughout.

* `weak_four_carrier_four_impossible` excludes carrier rank four in the
  ordinary weak head with four reflected contrast sites. It derives
  the physical count, distinctness and active origin from the given
  tableau and the rank selector.
* `weak_four_inactive_origin_shared_clock_impossible` excludes the
  rank-three case with four physical contrast rows, inactive physical
  origin and an active row with reflected clock one.

These are ordered-field results. Neither theorem supplies an unconditional
stage-count improvement. The rank-three case with a separately inactive,
unshared origin is not covered by these two statements.

The nine added modules compiled and each replayed with `leanchecker` on the
pinned Lean and Mathlib 4.36.0, using the checked dependency bank. The two
typed endpoint audits elaborated and report only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. This is targeted verification
and does not assert a full clean rebuild or cross-version compatibility.
