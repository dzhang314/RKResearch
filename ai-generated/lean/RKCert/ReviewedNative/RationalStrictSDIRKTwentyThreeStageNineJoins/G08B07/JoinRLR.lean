module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRLRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinRLRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07RLR : (rootPage ((((treesOfOrderSucc 7).drop 214).take 106).drop 52) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 26 ((((treesOfOrderSucc 7).drop 214).take 106).drop 52) (treesOfOrderSucc 0) pageG08B07RLRL pageG08B07RLRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
