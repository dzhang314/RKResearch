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
theorem pageG07B06LLLLRL : (rootPage (((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4).take 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG07B06LLLLRR : (rootPage (((((((treesOfOrderSucc 6).take 66).take 32).take 16).take 8).drop 4).drop 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
