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
theorem pageG08B04LLRRRL : (rootPage (((((treesOfOrderSucc 4).take 7).take 3).drop 1).take 1) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B04LLRRRR : (rootPage (((((treesOfOrderSucc 4).take 7).take 3).drop 1).drop 1) (((treesOfOrderSucc 3).drop 2).drop 1)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
