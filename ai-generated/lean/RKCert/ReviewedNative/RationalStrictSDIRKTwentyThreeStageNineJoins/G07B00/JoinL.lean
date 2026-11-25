module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B00.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B00.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B00L : (rootPage (treesOfOrderSucc 0) ((treesOfOrderSucc 6).take 66)).all paidTree = true :=
  split_right (p := paidTree) 32 (treesOfOrderSucc 0) ((treesOfOrderSucc 6).take 66) pageG07B00LL pageG07B00LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
