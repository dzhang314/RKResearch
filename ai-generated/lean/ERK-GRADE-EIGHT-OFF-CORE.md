# The native rank-three F4 core is impossible

This packet uses the pointwise-closed intrinsic core from the checked
grade-eight cubic closure. It avoids legacy objects and new arithmetic.

`NativeLiveCore` obtains the support indicator over any field via the
existing disjoint-head theorem on the constant vector 1. Clock invariance
then puts the weighted polynomial band of that indicator in the core;
its rank counts the genuine distinct live clocks. No fake padded or
merged method is used.

`rank_three_off_core_clocks` is characteristic-zero and does not require
order conditions. When the actual core is F4 (rank three) and F3 has rank
two, each off-core row of A restricted to the core annihilates F3. These
row maps therefore lie on one line. Let h be the first nonzero off-core
clock. Its row is nonzero by the paid primitive of X. At any first
different nonzero off-core clock, test the derivative of X²(X−h)².
That derivative vanishes at all earlier off-core clocks (0 or h).
At h its normalized primitive vanishes, so the same line of row maps
forces it to vanish at the later clock as well, a contradiction.

Thus all actual stage clocks lie in at most five values: at most three
distinct live clocks, plus 0 and h. `no_rank_three_clock_core_at_order_ten`
excludes this already at reviewed order ten by native degree-five
separation. `ordered_grade_eight_quartic_only` therefore eliminates
the rank-three ordered ERK branch and leaves exactly the rank-four
flat grade-4→8 quartic chart. It does not claim that final chart
has been excluded or that the uniform grade-eight surplus is proved.

Small Lean 4.36 builds, independent exact-name replays and the reviewed
width-26 client are recorded in `checks/receipt.json`. The rechecker
writes Lean objects only into a new temporary tree; no old source,
proof object, or other artifact is modified.
