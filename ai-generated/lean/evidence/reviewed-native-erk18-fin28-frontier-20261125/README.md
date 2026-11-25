# Native explicit order-18 Fin28 rank frontier

The module `RKCert.ReviewedNative.ERK18Width28Frontier` gives necessary
rank alternatives on the original width-28 tableau. It assumes reviewed
`HasOrder 18 A b`, strict triangularity, and an ordered field. With
`F_j = zeroSpace A j` and `r₀ = finrank K (back A b 0)`, the possible
`(dim F₉, r₀)` are `(10, 0)`, `(10, 1)`, or `(11, 0)`. The first two
have `dim F₈ = 9`; the third permits 9 or 10. The same module gives exact
native grade-seven reverse and primitive annihilators in the saturated
cases. The numerical stage statement in the source is the existing
27-stage floor, not an exclusion of widths 27 or 28. There is no
29-stage claim or terminal argument in this certificate.

The measured one-root build completed the three public imports
`CoefficientField`, `TwoSeedRank`, `ERKCharZero`, and the literal
`ERK18Width28Frontier` body with zero exits and empty diagnostic logs.
The independent `AuditReviewedNativeERK18Width28CoreOnly.lean` imports only
that core and was checked without producing objects. It types the width
alternatives and the reverse saturation, and its two exact axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`. The measured
source and object digests, precise audit output, and the exact committed
source closure are recorded in [result.json](result.json).

For a scoped reproduction with the pinned Lean 4.36.0 and Mathlib inputs:

```sh
cd ai-generated/lean
lake build RKCert.ReviewedNative.ERK18Width28Frontier
lake env lean AuditReviewedNativeERK18Width28CoreOnly.lean
```
