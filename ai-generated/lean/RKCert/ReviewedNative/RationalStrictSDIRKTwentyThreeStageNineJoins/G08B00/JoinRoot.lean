module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B00.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 7)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 0) (treesOfOrderSucc 7) pageG08B00L pageG08B00R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
