module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B06.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B06.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B06L : (rootPage ((treesOfOrderSucc 6).take 66) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 32 ((treesOfOrderSucc 6).take 66) (treesOfOrderSucc 0) pageG07B06LL pageG07B06LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
