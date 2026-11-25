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
theorem pageG08B00RLLLRLRL : (rootPage (treesOfOrderSucc 0) (((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).drop 6).take 2)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B00RLLLRLRRL : (rootPage (treesOfOrderSucc 0) ((((((((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52).drop 26).take 12).drop 6).drop 2).take 2)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
