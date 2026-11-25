module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRLLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RLL : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).take 214).take 106)).all paidTree = true :=
  split_right (p := paidTree) 52 (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).take 214).take 106) pageG08B00RLLL pageG08B00RLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
