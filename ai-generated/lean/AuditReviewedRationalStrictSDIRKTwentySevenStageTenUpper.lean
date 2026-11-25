module

import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 10 RationalStrictSDIRKTwentySevenStageTenUpper.A
    RationalStrictSDIRKTwentySevenStageTenUpper.b :=
  RationalStrictSDIRKTwentySevenStageTenUpper.order_ten

example : RationalStrictSDIRKTwentySevenStageTenUpper.b ⬝ᵥ Φ (tallTree 11)
    RationalStrictSDIRKTwentySevenStageTenUpper.A = (5946972394780345710421384301593 / 224017752875470299449731184306688000000 : ℚ) :=
  RationalStrictSDIRKTwentySevenStageTenUpper.eleventh_tall_weight

example : ¬ HasOrder 11 RationalStrictSDIRKTwentySevenStageTenUpper.A
    RationalStrictSDIRKTwentySevenStageTenUpper.b :=
  RationalStrictSDIRKTwentySevenStageTenUpper.not_order_eleven

example :
    ∃ (A : Matrix (Fin 27) (Fin 27) ℚ) (b : Fin 27 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/9) ∧ (1/9 : ℚ) ≠ 0 ∧
        HasOrder 10 A b ∧ ¬ HasOrder 11 A b :=
  exists_twenty_seven_stage_rational_strictSDIRK_exact_ten

#print axioms RationalStrictSDIRKTwentySevenStageTenUpper.order_ten
#print axioms RationalStrictSDIRKTwentySevenStageTenUpper.eleventh_tall_weight
#print axioms RationalStrictSDIRKTwentySevenStageTenUpper.not_order_eleven
#print axioms exists_twenty_seven_stage_rational_strictSDIRK_exact_ten
