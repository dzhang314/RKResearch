module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G06B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G06B01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G06B02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G06B03
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G06B04
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G06B05

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade6 : (treesOfOrderSucc 6).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 5
  intro i
  fin_cases i
  · exact paidBandG06B00
  · exact paidBandG06B01
  · exact paidBandG06B02
  · exact paidBandG06B03
  · exact paidBandG06B04
  · exact paidBandG06B05

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
