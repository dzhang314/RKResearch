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
theorem pageG08B07LLRRRLRR : (rootPage (((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).take 6).drop 2).drop 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B07LLRRRRLL : (rootPage (((((((((treesOfOrderSucc 7).take 214).take 106).drop 52).drop 26).drop 14).drop 6).take 4).take 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
