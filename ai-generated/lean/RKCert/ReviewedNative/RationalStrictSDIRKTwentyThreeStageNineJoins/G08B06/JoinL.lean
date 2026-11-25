module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B06.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B06.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B06L : (rootPage ((treesOfOrderSucc 6).take 66) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 32 ((treesOfOrderSucc 6).take 66) (treesOfOrderSucc 1) pageG08B06LL pageG08B06LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
