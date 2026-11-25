module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00R : (rootPage (treesOfOrderSucc 0) ((treesOfOrderSucc 7).drop 1)).all paidTree = true :=
  split_right (p := paidTree) 214 (treesOfOrderSucc 0) ((treesOfOrderSucc 7).drop 1) pageG08B00RL pageG08B00RR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
