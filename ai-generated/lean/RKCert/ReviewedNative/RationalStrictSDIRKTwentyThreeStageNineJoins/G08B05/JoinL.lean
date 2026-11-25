module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B05.JoinLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B05.JoinLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B05L : (rootPage ((treesOfOrderSucc 5).take 21) (treesOfOrderSucc 2)).all paidTree = true :=
  split_left (p := paidTree) 10 ((treesOfOrderSucc 5).take 21) (treesOfOrderSucc 2) pageG08B05LL pageG08B05LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
