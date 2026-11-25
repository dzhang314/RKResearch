module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard101
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard102
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard103
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard104
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard105
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard106
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard107
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B07.Shard108

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B07RRRRLLR : (rootPage ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07RRRRLLRL pageG08B07RRRRLLRR

private theorem pageG08B07RRRRLL : (rootPage (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).take 6) (treesOfOrderSucc 0) pageG08B07RRRRLLL pageG08B07RRRRLLR

private theorem pageG08B07RRRRLRL : (rootPage ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).take 4) (treesOfOrderSucc 0) pageG08B07RRRRLRLL pageG08B07RRRRLRLR

private theorem pageG08B07RRRRLRR : (rootPage ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).drop 6).drop 4) (treesOfOrderSucc 0) pageG08B07RRRRLRRL pageG08B07RRRRLRRR

private theorem pageG08B07RRRRLR : (rootPage (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14).drop 6) (treesOfOrderSucc 0) pageG08B07RRRRLRL pageG08B07RRRRLRR

private theorem pageG08B07RRRRL : (rootPage ((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).take 14) (treesOfOrderSucc 0) pageG08B07RRRRLL pageG08B07RRRRLR

private theorem pageG08B07RRRRRLR : (rootPage ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).take 6).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).take 6).drop 2) (treesOfOrderSucc 0) pageG08B07RRRRRLRL pageG08B07RRRRRLRR

private theorem pageG08B07RRRRRL : (rootPage (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).take 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).take 6) (treesOfOrderSucc 0) pageG08B07RRRRRLL pageG08B07RRRRRLR

private theorem pageG08B07RRRRRRL : (rootPage ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).take 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).take 4) (treesOfOrderSucc 0) pageG08B07RRRRRRLL pageG08B07RRRRRRLR

private theorem pageG08B07RRRRRRRR : (rootPage (((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).drop 4).drop 2) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).drop 4).drop 2) (treesOfOrderSucc 0) pageG08B07RRRRRRRRL pageG08B07RRRRRRRRR

private theorem pageG08B07RRRRRRR : (rootPage ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).drop 4) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6).drop 4) (treesOfOrderSucc 0) pageG08B07RRRRRRRL pageG08B07RRRRRRRR

private theorem pageG08B07RRRRRR : (rootPage (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14).drop 6) (treesOfOrderSucc 0) pageG08B07RRRRRRL pageG08B07RRRRRRR

private theorem pageG08B07RRRRR : (rootPage ((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 6 ((((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26).drop 14) (treesOfOrderSucc 0) pageG08B07RRRRRL pageG08B07RRRRRR

theorem pageG08B07RRRR : (rootPage (((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26) (treesOfOrderSucc 0)).all paidTree = true :=
  split_left (p := paidTree) 14 (((((treesOfOrderSucc 7).drop 214).drop 106).drop 54).drop 26) (treesOfOrderSucc 0) pageG08B07RRRRL pageG08B07RRRRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
