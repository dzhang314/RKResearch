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
theorem pageG08B00RRRRLRRRL : (rootPage (treesOfOrderSucc 0) ((((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).take 26).drop 12).drop 6).drop 4).take 2)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B00RRRRLRRRR : (rootPage (treesOfOrderSucc 0) ((((((((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).drop 54).take 26).drop 12).drop 6).drop 4).drop 2)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
