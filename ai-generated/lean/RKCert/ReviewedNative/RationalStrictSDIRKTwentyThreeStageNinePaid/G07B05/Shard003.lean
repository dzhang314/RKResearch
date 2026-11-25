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
theorem pageG07B05LLRRR : (rootPage ((((((treesOfOrderSucc 5).take 20).take 10).drop 4).drop 2).drop 2) (treesOfOrderSucc 1)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG07B05LRLL : (rootPage (((((treesOfOrderSucc 5).take 20).drop 10).take 4).take 2) (treesOfOrderSucc 1)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
