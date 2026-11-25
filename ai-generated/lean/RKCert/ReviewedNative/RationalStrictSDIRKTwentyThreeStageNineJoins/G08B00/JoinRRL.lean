module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RRL : (rootPage (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).drop 214).take 106)).all paidTree = true :=
  split_right (p := paidTree) 52 (treesOfOrderSucc 0) ((((treesOfOrderSucc 7).drop 1).drop 214).take 106) pageG08B00RRLL pageG08B00RRLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
