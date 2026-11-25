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
theorem pageG07B00LRLLRL : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4).take 2)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG07B00LRLLRR : (rootPage (treesOfOrderSucc 0) (((((((treesOfOrderSucc 6).take 66).drop 32).take 16).take 8).drop 4).drop 2)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
