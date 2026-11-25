module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B07RLLRRRRR : (rootPage (((((((((treesOfOrderSucc 7).drop 214).take 106).take 52).drop 26).drop 12).drop 6).drop 4).drop 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B07RLRLLLL : (rootPage ((((((((treesOfOrderSucc 7).drop 214).take 106).drop 52).take 26).take 12).take 6).take 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
