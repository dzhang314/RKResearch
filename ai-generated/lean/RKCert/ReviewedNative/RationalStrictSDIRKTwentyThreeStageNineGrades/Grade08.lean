module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B03
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B04
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B05
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B06
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G08B07

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade8 : (treesOfOrderSucc 8).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 7
  intro i
  fin_cases i
  · exact paidBandG08B00
  · exact paidBandG08B01
  · exact paidBandG08B02
  · exact paidBandG08B03
  · exact paidBandG08B04
  · exact paidBandG08B05
  · exact paidBandG08B06
  · exact paidBandG08B07

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
