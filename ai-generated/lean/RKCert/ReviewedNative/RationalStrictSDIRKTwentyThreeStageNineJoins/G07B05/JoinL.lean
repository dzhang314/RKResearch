module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G07B05.Shard005

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG07B05LLL : (rootPage ((((treesOfOrderSucc 5).take 20).take 10).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 20).take 10).take 4) (treesOfOrderSucc 1) pageG07B05LLLL pageG07B05LLLR

private theorem pageG07B05LLRR : (rootPage (((((treesOfOrderSucc 5).take 20).take 10).drop 4).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((treesOfOrderSucc 5).take 20).take 10).drop 4).drop 2) (treesOfOrderSucc 1) pageG07B05LLRRL pageG07B05LLRRR

private theorem pageG07B05LLR : (rootPage ((((treesOfOrderSucc 5).take 20).take 10).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 20).take 10).drop 4) (treesOfOrderSucc 1) pageG07B05LLRL pageG07B05LLRR

private theorem pageG07B05LL : (rootPage (((treesOfOrderSucc 5).take 20).take 10) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).take 20).take 10) (treesOfOrderSucc 1) pageG07B05LLL pageG07B05LLR

private theorem pageG07B05LRL : (rootPage ((((treesOfOrderSucc 5).take 20).drop 10).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 20).drop 10).take 4) (treesOfOrderSucc 1) pageG07B05LRLL pageG07B05LRLR

private theorem pageG07B05LRRR : (rootPage (((((treesOfOrderSucc 5).take 20).drop 10).drop 4).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((treesOfOrderSucc 5).take 20).drop 10).drop 4).drop 2) (treesOfOrderSucc 1) pageG07B05LRRRL pageG07B05LRRRR

private theorem pageG07B05LRR : (rootPage ((((treesOfOrderSucc 5).take 20).drop 10).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((treesOfOrderSucc 5).take 20).drop 10).drop 4) (treesOfOrderSucc 1) pageG07B05LRRL pageG07B05LRRR

private theorem pageG07B05LR : (rootPage (((treesOfOrderSucc 5).take 20).drop 10) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((treesOfOrderSucc 5).take 20).drop 10) (treesOfOrderSucc 1) pageG07B05LRL pageG07B05LRR

theorem pageG07B05L : (rootPage ((treesOfOrderSucc 5).take 20) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 10 ((treesOfOrderSucc 5).take 20) (treesOfOrderSucc 1) pageG07B05LL pageG07B05LR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
