module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B01.Shard005

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B01LLL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).take 10).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).take 10).take 4) pageG07B01LLLL pageG07B01LLLR

private theorem pageG07B01LLRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).take 20).take 10).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).take 20).take 10).drop 4).drop 2) pageG07B01LLRRL pageG07B01LLRRR

private theorem pageG07B01LLR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).take 10).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).take 10).drop 4) pageG07B01LLRL pageG07B01LLRR

private theorem pageG07B01LL : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 5).take 20).take 10)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((treesOfOrderSucc 5).take 20).take 10) pageG07B01LLL pageG07B01LLR

private theorem pageG07B01LRL : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).drop 10).take 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).drop 10).take 4) pageG07B01LRLL pageG07B01LRLR

private theorem pageG07B01LRRR : (rootPage (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).take 20).drop 10).drop 4).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) (((((treesOfOrderSucc 5).take 20).drop 10).drop 4).drop 2) pageG07B01LRRRL pageG07B01LRRRR

private theorem pageG07B01LRR : (rootPage (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).drop 10).drop 4)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 1) ((((treesOfOrderSucc 5).take 20).drop 10).drop 4) pageG07B01LRRL pageG07B01LRRR

private theorem pageG07B01LR : (rootPage (treesOfOrderSucc 1) (((treesOfOrderSucc 5).take 20).drop 10)).all paidTree = true :=
  split_right (p := paidTree) 4 (treesOfOrderSucc 1) (((treesOfOrderSucc 5).take 20).drop 10) pageG07B01LRL pageG07B01LRR

theorem pageG07B01L : (rootPage (treesOfOrderSucc 1) ((treesOfOrderSucc 5).take 20)).all paidTree = true :=
  split_right (p := paidTree) 10 (treesOfOrderSucc 1) ((treesOfOrderSucc 5).take 20) pageG07B01LL pageG07B01LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
