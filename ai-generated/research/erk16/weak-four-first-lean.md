# Lean certificate for the ERK16 weak-four exclusion

The order-16 lower-bound proof reduces a hypothetical 24-stage explicit
tableau to scalar cases. This replay closes the weak-four case over any
ordered field. It uses the actual chronological packet from the reviewed
`HasOrder 16 A b` proof, not a separate condition imposed on the tableau.

The main scalar theorem is
`RKResearch.Certified.ERK16.weakFourScalarExclusion_of_first_stop`.
It proves `WeakFourScalarExclusion K` by checking four finite families
of rational polynomial sign certificates, and applies the checked
certificates to the continuous parameter regions. The file
`RKCert.ReviewedNative.ERKOrder16OrderedAssemblyWeakFourFirst` then
uses the existing physical split, strong obstruction and padding.
Its theorem `ordered_erk16_stage_floor25_of_weak_five_scalar_exclusion`
shows that a strictly lower triangular order-16 tableau has at least
25 stages, **conditional on** `WeakFiveScalarExclusion K`. There is
no separate weak-four or tableau-structure premise.

This does not yet supply an unconditional Lean proof of the
[mathematical 25-stage bound](order-sixteen-twenty-five-stages.md).
The weak-five scalar exclusion is the remaining premise.

The two typed audits and the source order and axiom receipts are under
`ai-generated/lean`. The source build passed all 294 project modules
in the stated order on Lean 4.36.0 with its pinned Mathlib. The main
scalar endpoint and the assembly were independently replayed with
`leanchecker`. The checked decisions use kernel reduction.
