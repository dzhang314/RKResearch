module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLLLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLLLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RLLL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52)).all paidTree = true :=
  split_right (p := paidTree) 26 (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).take 214).take 106).take 52) pageG08B00RLLLL pageG08B00RLLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
