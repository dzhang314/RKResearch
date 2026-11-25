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
theorem pageG08B03RRRLL : (rootPage (((treesOfOrderSucc 3).drop 2).take 1) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B03RRRLRL : (rootPage ((((treesOfOrderSucc 3).drop 2).drop 1).take 1) ((((treesOfOrderSucc 4).drop 7).drop 3).take 2)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
