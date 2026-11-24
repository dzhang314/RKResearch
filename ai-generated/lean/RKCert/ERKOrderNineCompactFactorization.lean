module

public import RKCert.ERKOrderNineGoodPrimeNatRow0
public import RKCert.ERKOrderNineGoodPrimeNatRow1
public import RKCert.ERKOrderNineGoodPrimeNatRow2
public import RKCert.ERKOrderNineGoodPrimeNatRow3
public import RKCert.ERKOrderNineGoodPrimeNatRow4
public import RKCert.ERKOrderNineGoodPrimeNatRow5
public import RKCert.ERKOrderNineCompactRow6
public import RKCert.ERKOrderNineCompactRow7
public import RKCert.ERKOrderNineCompactAssembly

@[expose] public section

namespace RKCert.CompactResidue
open Polynomial RKCert.GoodPrimeDense

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def primeRows : List (NatSelectorDatum 1319) :=
  [NatRow0.selector,NatRow1.selector,NatRow2.selector,NatRow3.selector,
    NatRow4.selector,NatRow5.selector,Row6.selector,Row7.selector]

private def a8 : List Nat := [829,439,1133,467,1210,845,939,917,12,377,1]
private def a7 : List Nat := [840,240,1136,912,520,1074,773,925,320,1]
private def a6 : List Nat := [669,354,1271,244,1101,663,717,1]
private def a5 : List Nat := [778,310,269,887,1040,584,595,1]
private def a4 : List Nat := [30,887,1214,676,1279,709,1]
private def a3 : List Nat := [195,431,402,162,1]
private def a2 : List Nat := [621,477,993,1]
private def a1 : List Nat := [301,1265,1]
private def a0 : List Nat := [455]
private theorem w9 : Product 1319 [] [1] := .nil
private theorem w8 : Product 1319 [a8] [829,439,1133,467,1210,845,939,917,12,377,1] :=
  .cons w9 (of_decide_eq_true rfl)
private theorem w7 : Product 1319 [a7,a8] [1247,550,539,1126,957,1305,973,718,983,80,893,267,966,1226,1229,467,763,229,697,1] :=
  .cons w8 (of_decide_eq_true rfl)
private theorem w6 : Product 1319 [a6,a7,a8] [635,841,810,574,822,505,604,797,678,148,888,728,346,650,194,1010,585,45,60,184,1194,484,278,324,740,95,1] :=
  .cons w7 (of_decide_eq_true rfl)
private theorem w5 : Product 1319 [a5,a6,a7,a8] [724,393,1229,633,244,123,93,1193,410,50,1152,663,165,286,620,43,1240,335,1144,1244,613,306,1139,636,1075,404,1269,46,1040,774,1200,1132,690,1] :=
  .cons w6 (of_decide_eq_true rfl)
private theorem w4 : Product 1319 [a4,a5,a6,a7,a8] [616,1073,795,852,1126,816,464,870,21,599,121,1093,573,1149,450,1156,782,459,901,837,142,1160,1012,909,352,516,437,526,994,1014,93,200,323,690,461,1113,1292,953,80,1] :=
  .cons w5 (of_decide_eq_true rfl)
private theorem w3 : Product 1319 [a3,a4,a5,a6,a7,a8] [91,1210,1175,551,553,919,870,1157,1160,238,297,1222,431,710,1252,446,69,1119,1113,1278,85,1,554,904,105,687,1197,983,869,115,1278,636,979,923,920,397,248,564,68,354,971,1125,242,1] :=
  .cons w4 (of_decide_eq_true rfl)
private theorem w2 : Product 1319 [a2,a3,a4,a5,a6,a7,a8] [1113,779,387,462,170,486,911,838,298,332,100,1047,812,450,818,788,1153,670,1279,901,1259,247,200,1026,569,540,976,1280,394,473,331,1114,193,500,598,310,853,1055,1299,66,1053,489,76,886,531,1235,1] :=
  .cons w3 (of_decide_eq_true rfl)
private theorem w1 : Product 1319 [a1,a2,a3,a4,a5,a6,a7,a8] [1306,269,351,233,229,392,165,404,511,262,599,114,676,319,1138,892,630,382,417,998,515,667,637,179,1312,940,66,728,328,1029,619,34,906,59,187,844,553,89,1175,897,766,701,161,590,1267,1007,92,1181,1] :=
  .cons w2 (of_decide_eq_true rfl)
private theorem w0 : Product 1319 [a0,a1,a2,a3,a4,a5,a6,a7,a8] [680,1047,106,495,1313,295,1211,479,361,500,831,429,253,55,742,927,427,1021,1118,354,862,115,974,986,772,344,1012,171,193,1269,698,961,702,465,669,191,1005,925,430,564,314,1076,710,693,82,492,971,522,455] :=
  .cons w1 (of_decide_eq_true rfl)

/-- The parameter polynomial has the eight verified factor charts at 1319. -/
theorem prime_factorization :
    h48.map (Int.castRingHom Fp) =
      C (455:Fp) * (primeRows.map (fun S=>S.split.factor Fp)).prod :=
  factorization_of_product primeRows w0

end RKCert.CompactResidue
