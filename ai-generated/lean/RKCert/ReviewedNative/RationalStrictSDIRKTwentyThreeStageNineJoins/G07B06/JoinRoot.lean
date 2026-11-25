module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B06.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B06.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B06 : (rootPage (treesOfOrderSucc 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 66 (treesOfOrderSucc 6) (treesOfOrderSucc 0) pageG07B06L pageG07B06R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
