module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B03.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B03.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B03R : (rootPage (treesOfOrderSucc 3) ((treesOfOrderSucc 4).drop 7)).all paidTree = true :=
  split_right (p := paidTree) 3 (treesOfOrderSucc 3) ((treesOfOrderSucc 4).drop 7) pageG08B03RL pageG08B03RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
