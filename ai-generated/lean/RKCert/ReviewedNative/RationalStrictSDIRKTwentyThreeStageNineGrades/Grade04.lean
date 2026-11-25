module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G04B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G04B01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G04B02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G04B03

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade4 : (treesOfOrderSucc 4).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 3
  intro i
  fin_cases i
  · exact paidBandG04B00
  · exact paidBandG04B01
  · exact paidBandG04B02
  · exact paidBandG04B03

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
