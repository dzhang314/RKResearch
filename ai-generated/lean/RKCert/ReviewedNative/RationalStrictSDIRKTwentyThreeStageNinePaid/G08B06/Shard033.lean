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
theorem pageG08B06RRRRRRL : (rootPage ((((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2).take 2) (treesOfOrderSucc 1)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B06RRRRRRR : (rootPage ((((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2).drop 2) (treesOfOrderSucc 1)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
