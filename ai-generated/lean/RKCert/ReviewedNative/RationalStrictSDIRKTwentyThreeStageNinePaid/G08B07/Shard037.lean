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
theorem pageG08B07LRLRLRRR : (rootPage (((((((((treesOfOrderSucc 7).take 214).drop 106).take 54).drop 26).take 14).drop 6).drop 4).drop 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem pageG08B07LRLRRLL : (rootPage ((((((((treesOfOrderSucc 7).take 214).drop 106).take 54).drop 26).drop 14).take 6).take 2) (treesOfOrderSucc 0)).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
