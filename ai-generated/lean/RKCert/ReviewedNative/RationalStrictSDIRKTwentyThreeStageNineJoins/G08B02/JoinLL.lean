module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B02.Shard005

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B02LLLL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).take 5).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).take 5).take 2) pageG08B02LLLLL pageG08B02LLLLR

private theorem pageG08B02LLLRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2).drop 1) pageG08B02LLLRRL pageG08B02LLLRRR

private theorem pageG08B02LLLR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).take 5).drop 2) pageG08B02LLLRL pageG08B02LLLRR

private theorem pageG08B02LLL : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).take 10).take 5)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).take 10).take 5) pageG08B02LLLL pageG08B02LLLR

private theorem pageG08B02LLRL : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).drop 5).take 2)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).drop 5).take 2) pageG08B02LLRLL pageG08B02LLRLR

private theorem pageG08B02LLRRR : (rootPage (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2).drop 1)).all paidTree = true :=
  split_left (p := paidTree) 1 (treesOfOrderSucc 2) ((((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2).drop 1) pageG08B02LLRRRL pageG08B02LLRRRR

private theorem pageG08B02LLRR : (rootPage (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2)).all paidTree = true :=
  split_right (p := paidTree) 1 (treesOfOrderSucc 2) (((((treesOfOrderSucc 5).take 21).take 10).drop 5).drop 2) pageG08B02LLRRL pageG08B02LLRRR

private theorem pageG08B02LLR : (rootPage (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).take 10).drop 5)).all paidTree = true :=
  split_right (p := paidTree) 2 (treesOfOrderSucc 2) ((((treesOfOrderSucc 5).take 21).take 10).drop 5) pageG08B02LLRL pageG08B02LLRR

theorem pageG08B02LL : (rootPage (treesOfOrderSucc 2) (((treesOfOrderSucc 5).take 21).take 10)).all paidTree = true :=
  split_right (p := paidTree) 5 (treesOfOrderSucc 2) (((treesOfOrderSucc 5).take 21).take 10) pageG08B02LLL pageG08B02LLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
