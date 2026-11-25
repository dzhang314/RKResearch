module

import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 9 RationalStrictSDIRKTwentyThreeStageNineUpper.A RationalStrictSDIRKTwentyThreeStageNineUpper.b := RationalStrictSDIRKTwentyThreeStageNineUpper.order_nine

example : RationalStrictSDIRKTwentyThreeStageNineUpper.b ⬝ᵥ Φ (tallTree 10) RationalStrictSDIRKTwentyThreeStageNineUpper.A = (672263002006281827534440264169 / 2489086143060781104997013158963200000 : ℚ) :=
  RationalStrictSDIRKTwentyThreeStageNineUpper.tenth_tall_weight

example : ¬ HasOrder 10 RationalStrictSDIRKTwentyThreeStageNineUpper.A RationalStrictSDIRKTwentyThreeStageNineUpper.b := RationalStrictSDIRKTwentyThreeStageNineUpper.not_order_ten

example :
    ∃ (A : Matrix (Fin 23) (Fin 23) ℚ) (b : Fin 23 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/9) ∧ (1/9 : ℚ) ≠ 0 ∧
        HasOrder 9 A b ∧ ¬ HasOrder 10 A b :=
  exists_twenty_three_stage_rational_strictSDIRK_exact_nine

#print axioms RationalStrictSDIRKTwentyThreeStageNineUpper.order_nine
#print axioms RationalStrictSDIRKTwentyThreeStageNineUpper.tenth_tall_weight
#print axioms RationalStrictSDIRKTwentyThreeStageNineUpper.not_order_ten
#print axioms exists_twenty_three_stage_rational_strictSDIRK_exact_nine
