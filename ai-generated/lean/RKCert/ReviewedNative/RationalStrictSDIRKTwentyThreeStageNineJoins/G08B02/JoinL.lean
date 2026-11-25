module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B02.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B02.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B02L : (rootPage (treesOfOrderSucc 2) ((treesOfOrderSucc 5).take 21)).all paidTree = true :=
  split_right (p := paidTree) 10 (treesOfOrderSucc 2) ((treesOfOrderSucc 5).take 21) pageG08B02LL pageG08B02LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
