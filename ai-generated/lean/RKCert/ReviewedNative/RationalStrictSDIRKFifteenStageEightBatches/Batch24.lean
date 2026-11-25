module

public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightCore

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper

open FiniteRootedTree
open scoped Matrix

/-! These are actual leaves of the frozen take/drop proof. No tree is relabelled. -/

set_option maxHeartbeats 8000000 in
theorem paidGroup7LRLRLR : (((((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).take 16).drop 8).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem paidGroup7LRLRRL : (((((((treesOfOrderSucc 7).take 216).drop 104).take 56).drop 24).drop 16).take 8).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper
