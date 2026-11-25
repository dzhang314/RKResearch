module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B01.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B01.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B01L : (rootPage (treesOfOrderSucc 1) ((treesOfOrderSucc 6).take 66)).all paidTree = true :=
  split_right (p := paidTree) 32 (treesOfOrderSucc 1) ((treesOfOrderSucc 6).take 66) pageG08B01LL pageG08B01LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
