module

import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenTall

open RKResearch RKResearch.Certified RKResearch.FiniteRootedTree
open scoped Matrix

example : RationalStrictSDIRKTwentySevenStageTenUpper.b ⬝ᵥ
    Φ (tallTree 11) RationalStrictSDIRKTwentySevenStageTenUpper.A =
    (5946972394780345710421384301593 / 224017752875470299449731184306688000000 : ℚ) :=
  RationalStrictSDIRKTwentySevenStageTenUpper.eleventh_tall_weight

example : ¬ HasOrder 11 RationalStrictSDIRKTwentySevenStageTenUpper.A
    RationalStrictSDIRKTwentySevenStageTenUpper.b :=
  RationalStrictSDIRKTwentySevenStageTenUpper.not_order_eleven

#print axioms RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper.eleventh_tall_weight
#print axioms RKResearch.Certified.RationalStrictSDIRKTwentySevenStageTenUpper.not_order_eleven
