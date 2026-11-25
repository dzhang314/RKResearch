module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G02B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G02B01

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade2 : (treesOfOrderSucc 2).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 1
  intro i
  fin_cases i
  · exact paidBandG02B00
  · exact paidBandG02B01

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
