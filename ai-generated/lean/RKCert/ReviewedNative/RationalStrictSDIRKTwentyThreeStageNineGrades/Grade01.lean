module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineBands.G01B00

import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open RationalStrictSDIRKTreePages
open scoped Matrix

theorem paidGrade1 : (treesOfOrderSucc 1).all paidTree = true := by
  apply all_trees_succ_of_bands paidTree 0
  intro i
  fin_cases i
  · exact paidBandG01B00

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
