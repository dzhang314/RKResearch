module

import RKCert.ReviewedNative.RationalStrictSDIRKSmallUpper

open RKResearch RKResearch.Certified

example : HasOrder 3 RationalStrictSDIRK3.A RationalStrictSDIRK3.b ∧
    ¬ HasOrder 4 RationalStrictSDIRK3.A RationalStrictSDIRK3.b :=
  ⟨RationalStrictSDIRK3.order_three, RationalStrictSDIRK3.not_order_four⟩

example : HasOrder 4 RationalStrictSDIRK4.A RationalStrictSDIRK4.b ∧
    ¬ HasOrder 5 RationalStrictSDIRK4.A RationalStrictSDIRK4.b :=
  ⟨RationalStrictSDIRK4.order_four, RationalStrictSDIRK4.not_order_five⟩

#print axioms RKResearch.Certified.RationalStrictSDIRK3.order_three
#print axioms RKResearch.Certified.RationalStrictSDIRK3.not_order_four
#print axioms RKResearch.Certified.RationalStrictSDIRK4.order_four
#print axioms RKResearch.Certified.RationalStrictSDIRK4.not_order_five
#print axioms RKResearch.Certified.exists_rational_strictSDIRK_exact_three
#print axioms RKResearch.Certified.exists_rational_strictSDIRK_exact_four
#print axioms RKResearch.Certified.exists_strictSDIRK_exact_three_via_rational
#print axioms RKResearch.Certified.exists_strictSDIRK_exact_four_via_rational
