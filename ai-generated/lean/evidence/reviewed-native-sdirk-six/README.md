# Strict SDIRK at six: native lower bound

For a lower triangular matrix over any characteristic-zero field, the reviewed
`HasOrder A b 6` and one common **nonzero** diagonal imply seven physical stages.
No positivity, ordering, distinct stage nodes, invertible weights, or stiff
accuracy is presumed. This proves necessity, not attainability at seven.

## Consumers

* `RKResearch.HasOrder.sdirk_order_six_stages_field`: field theorem.
* `RKResearch.HasOrder.sdirk_order_six_stages`: a shared unit in a
  characteristic-zero commutative ring, including rings with zero divisors.
* `RKResearch.HasOrder.sdirk_order_six_stages_marked`: a ring and shared
  coefficient γ with `∀ n k : ℕ, 0 < n → (n:R)*γ^k ≠ 0`. This is exactly
  avoidance of zero in simultaneous integer/marker specialization. Mere
  nonzeroness in a commutative ring does not imply this hypothesis.
* `strict_sdirk_stage_floor_field`, `strict_sdirk_stage_floor`, and
  `strict_sdirk_stage_floor_marked` in `RKResearch.HasOrder`: for every positive
  order p the lower bound is 7 at p = 6 and `((p+1)^2/4+1)/2` otherwise
  (natural-number division). The latter case is the existing quadratic floor.

## Argument and dependency boundary

The existing paid native commutator census gives six stages and, at equality,
grade dimensions 1, 2, 4, 5, 6, 6. Its injectivity and annihilation, together
with paid Cauchy probes, give six independent rows in the stage dual. The last
two physical rows then have nonzero weights and distinct nodes as *conclusions*.
A two-dimensional silent cubic space forces the physical front to satisfy the
normal-form identities; the weighted adjoint defect fixes the reflected terminal
seed. Both possible values (zero/nonzero) of the third-row tap are excluded by
the order-paid word evaluations and scalar polynomial certificates.

All tableau and tree arguments use the reviewed `Matrix`, `FiniteRootedTree`,
`Φ`, and `HasOrder`. No legacy tableau, trees, or order conversions are imported.
The sole older numerical module is the unchanged `RKCert.SDIRK6Elimination`,
which contains only Mathlib scalar polynomial definitions and elimination
identities. Its two direct imports are `Mathlib.Tactic.LinearCombination` and
`Mathlib.Tactic.NormNum` (SHA-256 of source:
`f466193fe8eb01aa6c06be2ea0e72df039965265975b39911b8d1198948b5597`).
The uniform floor additionally uses the separate reviewed-native
`NonsingularDIRKQuadraticFloor`; it is not needed by the strict field theorem.

## Checks

Run `lake env lean AuditReviewedSDIRKSix.lean` from the aggregate Lean project
after building the modules. The consumer fixes the six-stage matrix size and
also tests marker specialization and the endpoint jump versus the adjacent
orders and p=21. The JSON receipt records the pinned toolchain, source hashes,
kernel replays and axiom output. This is an additive source-only delta.
