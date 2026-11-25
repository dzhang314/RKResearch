module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B00
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B01
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B02
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B03
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B04
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B05
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G07B06

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade7 : (treesOfOrderSucc 7).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 6
  intro i
  fin_cases i
  · exact paidBandG07B00
  · exact paidBandG07B01
  · exact paidBandG07B02
  · exact paidBandG07B03
  · exact paidBandG07B04
  · exact paidBandG07B05
  · exact paidBandG07B06

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
