module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRRLL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G08B00.JoinRRRLR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG08B00RRRL : (rootPage (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).take 54)).all paidTree = true :=
  split_right (p := paidTree) 26 (treesOfOrderSucc 0) (((((treesOfOrderSucc 7).drop 1).drop 214).drop 106).take 54) pageG08B00RRRLL pageG08B00RRRLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
