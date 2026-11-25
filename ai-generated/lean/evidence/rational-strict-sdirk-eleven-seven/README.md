# Eleven-stage rational strict SDIRK of exact order seven

The named checked theorem is
`RKResearch.Certified.exists_eleven_stage_rational_strictSDIRK_exact_seven`.
It gives a rational lower-triangular tableau on `Fin 11` with common
nonzero diagonal `1/7`, the reviewed `HasOrder 7 A b`, and
`¬ HasOrder 8 A b`. The exact eight-vertex tall-tree weight is
`18371 / 711541152`, rather than `1 / 40320`.

- [Native source with the literal tableau](../../RKCert/ReviewedNative/RationalStrictSDIRKElevenStageSevenUpper.lean)
- [Typed audit](../../AuditReviewedRationalStrictSDIRKElevenStageSevenUpper.lean)
- [Project source SHA-256 pins](dependencies.sha256)
- [Four axiom checks](axioms.log)

The witness and audit both passed using the normal Lean 4.36.0 frontend
(commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`) and Mathlib 4.36.0
(revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The witness uses
the checked split-22 proof: thirteen segments of the reviewed rooted-tree
enumeration and a separate exact integer tall-tree computation. Both
processes exited zero. The axiom checks list only `propext`,
`Classical.choice` and `Quot.sound`.

To check input fingerprints, run `sha256sum -c ai-generated/lean/evidence/rational-strict-sdirk-eleven-seven/dependencies.sha256`
from the repository root. The project import closure reuses
`RKResearch.FiniteRootedTree` and `RKResearch.OrderConditions`, then
`ChangeCoefficients` and `FiniteOrderCheck`, then
`FiniteScaledOrderCheck`. With these providers and the pinned toolchain
in one module namespace, elaborate the witness before the typed audit.
No rebuilt provider or compiled object is included here.

This is a constructive upper bound over the rationals, not a minimal-stage
or stability claim. It does not change the nine-stage real-algebraic
upper endpoint for order seven.
