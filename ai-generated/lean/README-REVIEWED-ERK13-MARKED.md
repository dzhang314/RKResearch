# Native explicit order thirteen: marked grade-eleven saturation

For an actual strictly lower 19-stage tableau with
`RKResearch.HasOrder 13 A b` over any characteristic-zero field and
`firstSeed A b = 0`, this additive leaf proves two statements:

* `order13_marked_reverse_first_escapes`: the actual one-dimensional
  adjoint flag cannot be invariant under the reflected clock.
* `order13_marked_grade_eleven`: the exact marked forward grade 11 is
  the whole original 19-dimensional column space. It equals grade 10
  joined with its clock image.

The marked grade-8 and grade-9 step debits rule out reverse invariance
at credits 3 and 2. The independently checked neutral reverse lemma
then consumes the two actual monomial residual memberships. The marked
grade-10 space has rank 18; first reverse escape forces one more
physical forward direction.

This is not the 19-stage exclusion: it does not rule out either type
of tableau by itself or assert the lower bound of twenty stages.
Pinned Lean and Mathlib 4.36.0. Dependencies:
reviewed base `91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`, the
previous `rk-reviewed-native-erk13-frame-20261124.zip` (SHA-256
`eda327121586ab72156b22f111e163cfb87530cb78095f217a084cb338f56f7e`),
and the separate neutral `ReverseLocalized` source packet. No human
source changed and no scalar arithmetic was replayed. The independent
audit checks both axioms lists and the literal native endpoint type.
