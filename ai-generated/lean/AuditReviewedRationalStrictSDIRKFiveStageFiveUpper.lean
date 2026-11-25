module

import RKCert.ReviewedNative.RationalStrictSDIRKFiveStageFiveUpper

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : HasOrder 5 RationalStrictSDIRKFiveStageFiveUpper.A RationalStrictSDIRKFiveStageFiveUpper.b :=
  RationalStrictSDIRKFiveStageFiveUpper.order_five

example : RationalStrictSDIRKFiveStageFiveUpper.b ⬝ᵥ Φ (tallTree 6) RationalStrictSDIRKFiveStageFiveUpper.A =
    (-5 / 24 : ℚ) := RationalStrictSDIRKFiveStageFiveUpper.sixth_tall_weight

example :
    ∃ (A : Matrix (Fin 5) (Fin 5) ℚ) (b : Fin 5 → ℚ),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b :=
  exists_five_stage_rational_strictSDIRK_exact_five

#print axioms RationalStrictSDIRKFiveStageFiveUpper.order_five
#print axioms RationalStrictSDIRKFiveStageFiveUpper.sixth_tall_weight
#print axioms RationalStrictSDIRKFiveStageFiveUpper.not_order_six
#print axioms exists_five_stage_rational_strictSDIRK_exact_five
