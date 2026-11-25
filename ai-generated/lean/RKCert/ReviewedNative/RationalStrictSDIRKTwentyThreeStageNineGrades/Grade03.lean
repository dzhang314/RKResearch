module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G03B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G03B01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G03B02

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade3 : (treesOfOrderSucc 3).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 2
  intro i
  fin_cases i
  · exact paidBandG03B00
  · exact paidBandG03B01
  · exact paidBandG03B02

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
