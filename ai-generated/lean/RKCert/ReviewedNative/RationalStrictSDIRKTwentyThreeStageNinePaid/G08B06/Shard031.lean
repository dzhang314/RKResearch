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
theorem pageG08B06RRRLRR : (rootPage (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4).drop 2) (treesOfOrderSucc 1)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B06RRRRLL : (rootPage (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4).take 2) (treesOfOrderSucc 1)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
