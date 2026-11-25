module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G05B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G05B01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G05B02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G05B03
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G05B04

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade5 : (treesOfOrderSucc 5).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 4
  intro i
  fin_cases i
  · exact paidBandG05B00
  · exact paidBandG05B01
  · exact paidBandG05B02
  · exact paidBandG05B03
  · exact paidBandG05B04

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
