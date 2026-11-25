module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B03.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B03.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B03L : (rootPage (treesOfOrderSucc 3) ((treesOfOrderSucc 4).take 7)).all paidTree = true :=
  split_right (p := paidTree) 3 (treesOfOrderSucc 3) ((treesOfOrderSucc 4).take 7) pageG08B03LL pageG08B03LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
