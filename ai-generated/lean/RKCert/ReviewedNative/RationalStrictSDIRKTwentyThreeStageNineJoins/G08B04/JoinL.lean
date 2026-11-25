module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B04.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B04.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B04L : (rootPage ((treesOfOrderSucc 4).take 7) (treesOfOrderSucc 3)).all paidTree = true :=
  split_left (p := paidTree) 3 ((treesOfOrderSucc 4).take 7) (treesOfOrderSucc 3) pageG08B04LL pageG08B04LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
