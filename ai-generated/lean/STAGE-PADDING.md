# Reviewed-native stage padding

`RKCert.ReviewedNative.StagePadding` uses the original `RKResearch.Φ` and
`RKResearch.HasOrder`, over any commutative semiring. It uses the existing
`Fin.castLE` prefix embedding and `sum_prefix_zero_tail`; there is no legacy
tree or order conversion, coefficient extension, arithmetic replay, or human
source change.

## Exact scope

`zeroPadMatrix A n` copies the original leading submatrix when the width
`s ≤ n`, with all new rows and columns zero. `zeroPadVec b n` sets new
output weights to zero. The original columns of each tree agree literally
on original stage indices. The padded leaf may still evaluate to one on
the appended rows; the zero output weights, not a claim that every padded
tree entry is zero, are why elementary weights remain unchanged.

`hasOrder_zeroPad_iff` preserves and reflects reviewed order at every p,
even without triangularity. `zeroPadMatrix_strict_iff` and
`zeroPadMatrix_lower_iff` preserve and reflect the explicit and full
lower-triangular assumptions respectively. Thus
`strict_stages_gt_of_exact_exclusion` turns an actual width-26 reviewed
order-17 explicit exclusion into the bound of 27 stages, with no need
to first prove a separate stage-count floor. The analogous
`lower_stages_gt_of_exact_exclusion` applies to lower-triangular
classes allowing zero diagonal entries. Neither theorem supplies
its exclusion premise or the rank assumptions within the exact-width proof.

A newly appended diagonal entry is zero.
`zeroPadMatrix_nonzero_diagonal_iff` shows the condition that the whole
diagonal is nonzero can survive only when the original and target widths
are equal. In particular this construction does not turn an exact-width
exclusion for nonsingular common-diagonal SDIRK into a general stage bound.

## Verification

The source is staged additively against reviewed input
`91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5`.
`python3 checks/run_small.py` verifies the pinned native graded archive and
uses only its necessary native/reviewed cached leaves plus Mathlib, compiles
and independently kernel-replays the single new small module, and typechecks
both dispatchers for an explicit order-17 and lower-triangular order-15
hypothesis. See `checks/receipt.json` for source and object digests and axiom
checks. Nothing in the frozen backend is rebuilt.
