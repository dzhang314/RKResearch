module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B00.JoinL
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineJoins.G07B00.JoinR

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

theorem pageG07B00 : (rootPage (treesOfOrderSucc 0) (treesOfOrderSucc 6)).all paidTree = true :=
  split_right (p := paidTree) 66 (treesOfOrderSucc 0) (treesOfOrderSucc 6) pageG07B00L pageG07B00R

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
