module

import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 8 RationalStrictSDIRKFifteenStageEightUpper.A
    RationalStrictSDIRKFifteenStageEightUpper.b :=
  RationalStrictSDIRKFifteenStageEightUpper.order_eight

example : RationalStrictSDIRKFifteenStageEightUpper.b ⬝ᵥ Φ (tallTree 9)
    RationalStrictSDIRKFifteenStageEightUpper.A = (189383 / 63417876480 : ℚ) :=
  RationalStrictSDIRKFifteenStageEightUpper.ninth_tall_weight

example : ¬ HasOrder 9 RationalStrictSDIRKFifteenStageEightUpper.A
    RationalStrictSDIRKFifteenStageEightUpper.b :=
  RationalStrictSDIRKFifteenStageEightUpper.not_order_nine

example :
    ∃ (A : Matrix (Fin 15) (Fin 15) ℚ) (b : Fin 15 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/8) ∧ (1/8 : ℚ) ≠ 0 ∧
        HasOrder 8 A b ∧ ¬ HasOrder 9 A b :=
  exists_fifteen_stage_rational_strictSDIRK_exact_eight

#print axioms RationalStrictSDIRKFifteenStageEightUpper.order_eight
#print axioms RationalStrictSDIRKFifteenStageEightUpper.ninth_tall_weight
#print axioms RationalStrictSDIRKFifteenStageEightUpper.not_order_nine
#print axioms exists_fifteen_stage_rational_strictSDIRK_exact_eight
