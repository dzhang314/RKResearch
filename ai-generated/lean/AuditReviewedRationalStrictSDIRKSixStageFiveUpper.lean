module

import RKCert.ReviewedNative.RationalStrictSDIRKSixStageFiveUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 5 RationalStrictSDIRKSixStageFiveUpper.A RationalStrictSDIRKSixStageFiveUpper.b :=
  RationalStrictSDIRKSixStageFiveUpper.order_five

example : RationalStrictSDIRKSixStageFiveUpper.b ⬝ᵥ Φ (tallTree 6) RationalStrictSDIRKSixStageFiveUpper.A =
    (-5 / 24 : ℚ) := RationalStrictSDIRKSixStageFiveUpper.sixth_tall_weight

example :
    ∃ (A : Matrix (Fin 6) (Fin 6) ℚ) (b : Fin 6 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b :=
  exists_six_stage_rational_strictSDIRK_exact_five

#print axioms RationalStrictSDIRKSixStageFiveUpper.order_five
#print axioms RationalStrictSDIRKSixStageFiveUpper.sixth_tall_weight
#print axioms RationalStrictSDIRKSixStageFiveUpper.not_order_six
#print axioms exists_six_stage_rational_strictSDIRK_exact_five
