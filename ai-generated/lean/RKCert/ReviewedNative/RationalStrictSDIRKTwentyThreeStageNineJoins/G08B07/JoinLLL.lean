module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLLLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B07.JoinLLLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B07LLL : (rootPage ((((treesOfOrderSucc 7).take 214).take 106).take 52) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 26 ((((treesOfOrderSucc 7).take 214).take 106).take 52) (treesOfOrderSucc 0) pageG08B07LLLL pageG08B07LLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
