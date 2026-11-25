module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLLRL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLLRR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07LLR : (rootPage ((((treesOfOrderSucc 7).take 214).take 106).drop 52) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 26 ((((treesOfOrderSucc 7).take 214).take 106).drop 52) (treesOfOrderSucc 0) pageG08B07LLRL pageG08B07LLRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
