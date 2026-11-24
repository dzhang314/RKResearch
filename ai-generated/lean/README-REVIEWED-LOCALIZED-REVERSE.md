# Physical rank-one reverse obstruction on reviewed order

This adds a neutral native entry point for a terminal marked reverse
chart in exact order proofs. It takes a strictly lower original matrix,
`RKResearch.HasOrder p A b` over any characteristic-zero field with
`10 ≤ p`, the actual vanishing first reverse seed, and these hypotheses:

* the dimensions of the native pair adjoint flags `back A b n` are
  `n` through (n=4);
* their second and third flags already have clock escape;
* the actual normalized cubic and quartic reflected row residuals belong
  to the second and third flags.

`localized_native_reverse_impossible` concludes that the first flag is
not invariant under the reflected clock. No positivity is assumed.
`normalizedResidual` simply scales the existing native
`reflectedStageRow`. The ranked spaces, greatest nonzero reflected
pivot and live-clock node witness are on the original coordinates.
The legacy reuse consists of the tree-free `ReverseRows` coefficient
identities, `reduce_reverse_rows`, and `two_node_confinement`; no
legacy tree-order bridge or arithmetic replay is used. Earlier native
terminal and moment modules are unchanged.

Pinned Lean and Mathlib 4.36.0; reviewed base
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`. Additive build order:
`ReverseLocalizedInputs`, then `ReverseLocalized`. The independent
audit checks the exact native consumer type and standard axioms.
