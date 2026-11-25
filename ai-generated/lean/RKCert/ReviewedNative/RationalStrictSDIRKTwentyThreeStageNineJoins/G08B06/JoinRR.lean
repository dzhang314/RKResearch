module

public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNineData
public import RKCert.ReviewedNative.RationalStrictSDIRKTreePages
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard025
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard026
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard027
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard028
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard029
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard030
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard031
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard032
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentyThreeStageNinePaid.G08B06.Shard033

@[expose] public section

namespace RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper

open FiniteRootedTree
open RationalStrictSDIRKTreePages
open scoped Matrix

private theorem pageG08B06RRLLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06RRLLLL pageG08B06RRLLLR

private theorem pageG08B06RRLLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06RRLLRL pageG08B06RRLLRR

private theorem pageG08B06RRLL : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).take 8) (treesOfOrderSucc 1) pageG08B06RRLLL pageG08B06RRLLR

private theorem pageG08B06RRLRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06RRLRLL pageG08B06RRLRLR

private theorem pageG08B06RRLRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06RRLRRL pageG08B06RRLRRR

private theorem pageG08B06RRLR : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).take 16).drop 8) (treesOfOrderSucc 1) pageG08B06RRLRL pageG08B06RRLRR

private theorem pageG08B06RRL : (rootPage ((((treesOfOrderSucc 6).drop 66).drop 32).take 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).drop 32).take 16) (treesOfOrderSucc 1) pageG08B06RRLL pageG08B06RRLR

private theorem pageG08B06RRRLL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).take 4) (treesOfOrderSucc 1) pageG08B06RRRLLL pageG08B06RRRLLR

private theorem pageG08B06RRRLR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8).drop 4) (treesOfOrderSucc 1) pageG08B06RRRLRL pageG08B06RRRLRR

private theorem pageG08B06RRRL : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).take 8) (treesOfOrderSucc 1) pageG08B06RRRLL pageG08B06RRRLR

private theorem pageG08B06RRRRL : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).take 4) (treesOfOrderSucc 1) pageG08B06RRRRLL pageG08B06RRRRLR

private theorem pageG08B06RRRRRR : (rootPage (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 (((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4).drop 2) (treesOfOrderSucc 1) pageG08B06RRRRRRL pageG08B06RRRRRRR

private theorem pageG08B06RRRRR : (rootPage ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 2 ((((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8).drop 4) (treesOfOrderSucc 1) pageG08B06RRRRRL pageG08B06RRRRRR

private theorem pageG08B06RRRR : (rootPage (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 4 (((((treesOfOrderSucc 6).drop 66).drop 32).drop 16).drop 8) (treesOfOrderSucc 1) pageG08B06RRRRL pageG08B06RRRRR

private theorem pageG08B06RRR : (rootPage ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 8 ((((treesOfOrderSucc 6).drop 66).drop 32).drop 16) (treesOfOrderSucc 1) pageG08B06RRRL pageG08B06RRRR

theorem pageG08B06RR : (rootPage (((treesOfOrderSucc 6).drop 66).drop 32) (treesOfOrderSucc 1)).all paidTree = true :=
  split_left (p := paidTree) 16 (((treesOfOrderSucc 6).drop 66).drop 32) (treesOfOrderSucc 1) pageG08B06RRL pageG08B06RRR

end RKResearch.Certified.RationalStrictSDIRKTwentyThreeStageNineUpper
