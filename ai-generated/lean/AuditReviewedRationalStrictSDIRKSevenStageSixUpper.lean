module

import RKCert.ReviewedNative.RationalStrictSDIRKSevenStageSixUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 6 RationalStrictSDIRKSevenStageSixUpper.A RationalStrictSDIRKSevenStageSixUpper.b :=
  RationalStrictSDIRKSevenStageSixUpper.order_six

example : RationalStrictSDIRKSevenStageSixUpper.b ⬝ᵥ Φ (tallTree 7) RationalStrictSDIRKSevenStageSixUpper.A =
    (7 / 40960 : ℚ) := RationalStrictSDIRKSevenStageSixUpper.seventh_tall_weight

example :
    ∃ (A : Matrix (Fin 7) (Fin 7) ℚ) (b : Fin 7 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/4) ∧ (1/4 : ℚ) ≠ 0 ∧
        HasOrder 6 A b ∧ ¬ HasOrder 7 A b :=
  exists_seven_stage_rational_strictSDIRK_exact_six

#print axioms RationalStrictSDIRKSevenStageSixUpper.order_six
#print axioms RationalStrictSDIRKSevenStageSixUpper.seventh_tall_weight
#print axioms RationalStrictSDIRKSevenStageSixUpper.not_order_seven
#print axioms exists_seven_stage_rational_strictSDIRK_exact_six
