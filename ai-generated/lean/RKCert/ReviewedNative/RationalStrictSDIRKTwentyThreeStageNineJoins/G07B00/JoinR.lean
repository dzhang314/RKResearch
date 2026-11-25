module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B00.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B00.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B00R : (rootPage (treesOfOrderSucc 0) ((treesOfOrderSucc 6).drop 66)).all paidTree = true :=
  split_right (p := paidTree) 32 (treesOfOrderSucc 0) ((treesOfOrderSucc 6).drop 66) pageG07B00RL pageG07B00RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
