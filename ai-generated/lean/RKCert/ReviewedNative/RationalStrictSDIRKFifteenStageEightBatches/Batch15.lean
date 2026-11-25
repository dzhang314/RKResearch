module

public import RKCert.ReviewedNative.RationalStrictSDIRKFifteenStageEightCore

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper

open FiniteRootedTree
open scoped Matrix

/-! These are actual leaves of the frozen take/drop proof. No tree is relabelled. -/

set_option maxHeartbeats 8000000 in
theorem paidGroup6RRRRR : ((((((treesOfOrderSucc 6).drop 64).drop 32).drop 16).drop 8).drop 8).all paidTree = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
theorem paidGroup7LLLLL : ((((((treesOfOrderSucc 7).take 216).take 104).take 48).take 24).take 8).all paidTree = true := by
  decide +kernel

end RKResearch.Certified.RationalStrictSDIRKFifteenStageEightUpper
