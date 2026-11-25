module

import RKCert.ReviewedNative.RationalStrictSDIRKElevenStageSevenUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 7 RationalStrictSDIRKElevenStageSevenUpper.A RationalStrictSDIRKElevenStageSevenUpper.b :=
  RationalStrictSDIRKElevenStageSevenUpper.order_seven

example : RationalStrictSDIRKElevenStageSevenUpper.b ⬝ᵥ Φ (tallTree 8)
    RationalStrictSDIRKElevenStageSevenUpper.A = (18371 / 711541152 : ℚ) :=
  RationalStrictSDIRKElevenStageSevenUpper.eighth_tall_weight

example : ¬ HasOrder 8 RationalStrictSDIRKElevenStageSevenUpper.A
    RationalStrictSDIRKElevenStageSevenUpper.b :=
  RationalStrictSDIRKElevenStageSevenUpper.not_order_eight

example :
    ∃ (A : Matrix (Fin 11) (Fin 11) ℚ) (b : Fin 11 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/7) ∧ (1/7 : ℚ) ≠ 0 ∧
        HasOrder 7 A b ∧ ¬ HasOrder 8 A b :=
  exists_eleven_stage_rational_strictSDIRK_exact_seven

#print axioms RationalStrictSDIRKElevenStageSevenUpper.order_seven
#print axioms RationalStrictSDIRKElevenStageSevenUpper.eighth_tall_weight
#print axioms RationalStrictSDIRKElevenStageSevenUpper.not_order_eight
#print axioms exists_eleven_stage_rational_strictSDIRK_exact_seven
