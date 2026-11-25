module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard001
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard002
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard003
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard004
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard005
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard006
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard007

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B07LLLLLLR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLLLLLRL pageG08B07LLLLLLRR

private theorem pageG08B07LLLLLL : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).take 6) (treesOfOrderSucc 0) pageG08B07LLLLLLL pageG08B07LLLLLLR

private theorem pageG08B07LLLLLRR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).drop 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).drop 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLLLLRRL pageG08B07LLLLLRRR

private theorem pageG08B07LLLLLR : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12).drop 6) (treesOfOrderSucc 0) pageG08B07LLLLLRL pageG08B07LLLLLRR

private theorem pageG08B07LLLLL : (rootPage ((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).take 12) (treesOfOrderSucc 0) pageG08B07LLLLLL pageG08B07LLLLLR

private theorem pageG08B07LLLLRLR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07LLLLRLRL pageG08B07LLLLRLRR

private theorem pageG08B07LLLLRL : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).take 6) (treesOfOrderSucc 0) pageG08B07LLLLRLL pageG08B07LLLLRLR

private theorem pageG08B07LLLLRRL : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).drop 6).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).drop 6).take 4) (treesOfOrderSucc 0) pageG08B07LLLLRRLL pageG08B07LLLLRRLR

private theorem pageG08B07LLLLRRR : (rootPage ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).drop 6).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).drop 6).drop 4) (treesOfOrderSucc 0) pageG08B07LLLLRRRL pageG08B07LLLLRRRR

private theorem pageG08B07LLLLRR : (rootPage (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12).drop 6) (treesOfOrderSucc 0) pageG08B07LLLLRRL pageG08B07LLLLRRR

private theorem pageG08B07LLLLR : (rootPage ((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26).drop 12) (treesOfOrderSucc 0) pageG08B07LLLLRL pageG08B07LLLLRR

theorem pageG08B07LLLL : (rootPage (((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 12 (((((treesOfOrderSucc 7).take 214).take 106).take 52).take 26) (treesOfOrderSucc 0) pageG08B07LLLLL pageG08B07LLLLR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
