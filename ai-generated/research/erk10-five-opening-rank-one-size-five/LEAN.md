# Native scope and replay

The standalone scalar source has no Mathlib dependency:

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10RankOneTiltScalars.lean

It checks the exact two-functional cubic probe, nonproportional
scalar primitive, integration commutator and the last rank-one
scalar cancellation. At this source freeze it has a completed
stock Lean 4.34.1 receipt (standard axioms only). The remaining
release runs were started but did not finish before freezing this
packet; they are not asserted checked here.

The separate standalone functional erasure source is:

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10TiltSilentErasure.lean

It encodes the raw word equality using the untouched-prefix
hypothesis. Its compile was queued, without a completed check
in this packet; the erasure proof and exact 63-word nontrivial
fixture are separately present and verified.

The proposed native rank floor and width identity use the already
verified Mathlib-based endpoint plateau module:

    cd ai-generated/lean
    lake build RKCert.ReviewedNative.ERK10EndpointPlateau
    lake env lean --threads=1 RKCert/ReviewedNative/ERK10DirtyPlateauRank.lean

The new rank-floor check was queued, without a completed result
in this packet. The mathematical floor is proved directly in
the README using the already published native plateau primitives.
The physical old-to-high interface, rooted source rank, and
chronological rank-one exclusion are mathematical here, with
exact rooted and scalar arithmetic replays rather than a
native all-tableau order theorem.
