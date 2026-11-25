module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripRowCheck
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def packet1200 : StripRowPacket :=
  ⟨⟨⟨5,29,4,14⟩,
    ![460,1475,2885,4473,5998,7229,7981],![469,1498,2926,4535,6077,7322,8093]⟩,
    ⟨6998523411950185577470555,413466101293807413566420992⟩,
    ⟨59096507693073470885987,2930837293594881777649664⟩⟩

def packet1201 : StripRowPacket :=
  ⟨⟨⟨5,29,4,15⟩,
    ![464,1489,2913,4517,6057,7300,8064],![473,1511,2951,4572,6128,7384,8192]⟩,
    ⟨16357505992229499910195011,826932202587614827132841984⟩,
    ⟨1029839912807,44739236603776⟩⟩

def packet1202 : StripRowPacket :=
  ⟨⟨⟨6,60,4,12⟩,
    ![448,1439,2815,4369,5866,7087,7875],![458,1464,2861,4435,5947,7170,7931]⟩,
    ⟨88178086685874626047224259,7695456809951325073636257280⟩,
    ⟨8153488513747410440874637,560832547581152464489963520⟩⟩

def packet1203 : StripRowPacket :=
  ⟨⟨⟨6,61,4,12⟩,
    ![448,1437,2814,4367,5864,7086,7875],![458,1463,2859,4433,5946,7170,7931]⟩,
    ⟨86782519361810287637377799,7510398554544538506369218560⟩,
    ⟨64043315785778657496674981047,4369335530431460794005497016320⟩⟩

def packet1204 : StripRowPacket :=
  ⟨⟨⟨5,30,4,13⟩,
    ![453,1456,2849,4420,5930,7154,7919],![464,1481,2895,4487,6016,7249,8001]⟩,
    ⟨423567339777984377998039,29591599048243256673499136⟩,
    ⟨8967904487922819690169489,509698111557378440107620352⟩⟩

def packet1205 : StripRowPacket :=
  ⟨⟨⟨6,62,4,12⟩,
    ![447,1436,2812,4365,5863,7085,7875],![457,1462,2857,4431,5944,7169,7931]⟩,
    ⟨13916325369980511648542135433,1194419139595023883048357870592⟩,
    ⟨8358758596319924611923900811,565688439489759032661842321408⟩⟩

def packet1206 : StripRowPacket :=
  ⟨⟨⟨6,63,4,12⟩,
    ![447,1435,2810,4363,5861,7084,7875],![457,1460,2855,4429,5943,7168,7930]⟩,
    ⟨200932667822976953,17105171570547906560⟩,
    ⟨512770163656386287,34426525347563514880⟩⟩

def packet1207 : StripRowPacket :=
  ⟨⟨⟨5,31,4,13⟩,
    ![453,1453,2845,4416,5928,7153,7919],![463,1479,2891,4483,6013,7248,8001]⟩,
    ⟨7393834897875863,508041928958586880⟩,
    ⟨135279055511173,7566689081219840⟩⟩

def packet1208 : StripRowPacket :=
  ⟨⟨⟨5,30,4,14⟩,
    ![459,1472,2881,4469,5996,7228,7981],![468,1496,2922,4530,6074,7320,8092]⟩,
    ⟨254715896820533239152005,14795799524121628336749568⟩,
    ⟨20894296944260247888501321,1019396223114756880215240704⟩⟩

def packet1209 : StripRowPacket :=
  ⟨⟨⟨5,30,4,15⟩,
    ![463,1487,2909,4513,6054,7299,8065],![472,1508,2947,4568,6125,7382,8192]⟩,
    ⟨595296247504148578609981,29591599048243256673499136⟩,
    ⟨148595494363351,6350524111982336⟩⟩

def packet1210 : StripRowPacket :=
  ⟨⟨⟨5,31,4,14⟩,
    ![458,1470,2877,4465,5993,7227,7981],![467,1493,2918,4526,6071,7318,8092]⟩,
    ⟨404171353709391,23092814952663040⟩,
    ⟨63037269670273,3026675632487936⟩⟩

def packet1211 : StripRowPacket :=
  ⟨⟨⟨5,31,4,15⟩,
    ![462,1484,2905,4509,6051,7298,8065],![471,1505,2943,4564,6122,7381,8192]⟩,
    ⟨10389704665337341,508041928958586880⟩,
    ⟨17,715⟩⟩

def packets050 : List StripRowPacket :=
  [packet1200, packet1201, packet1202, packet1203, packet1204, packet1205,
   packet1206, packet1207, packet1208, packet1209, packet1210, packet1211]

theorem packet1200_membership : packet1200 ∈ packets050 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1200_shape : checkStripShape packet1200.row = true := by
  decide +kernel

private theorem packet1200_cache : checkStripCache packet1200 = true := by
  decide +kernel

private theorem packet1200_pair (i : Fin 7) : checkEdgePair packet1200 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1200_ok : checkStripPacket packet1200 = true :=
  checkStripPacket_intro packet1200_shape packet1200_cache packet1200_pair

theorem packet1201_membership : packet1201 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1201_shape : checkStripShape packet1201.row = true := by
  decide +kernel

private theorem packet1201_cache : checkStripCache packet1201 = true := by
  decide +kernel

private theorem packet1201_pair (i : Fin 7) : checkEdgePair packet1201 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1201_ok : checkStripPacket packet1201 = true :=
  checkStripPacket_intro packet1201_shape packet1201_cache packet1201_pair

theorem packet1202_membership : packet1202 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1202_shape : checkStripShape packet1202.row = true := by
  decide +kernel

private theorem packet1202_cache : checkStripCache packet1202 = true := by
  decide +kernel

private theorem packet1202_pair (i : Fin 7) : checkEdgePair packet1202 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1202_ok : checkStripPacket packet1202 = true :=
  checkStripPacket_intro packet1202_shape packet1202_cache packet1202_pair

theorem packet1203_membership : packet1203 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1203_shape : checkStripShape packet1203.row = true := by
  decide +kernel

private theorem packet1203_cache : checkStripCache packet1203 = true := by
  decide +kernel

private theorem packet1203_pair (i : Fin 7) : checkEdgePair packet1203 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1203_ok : checkStripPacket packet1203 = true :=
  checkStripPacket_intro packet1203_shape packet1203_cache packet1203_pair

theorem packet1204_membership : packet1204 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1204_shape : checkStripShape packet1204.row = true := by
  decide +kernel

private theorem packet1204_cache : checkStripCache packet1204 = true := by
  decide +kernel

private theorem packet1204_pair (i : Fin 7) : checkEdgePair packet1204 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1204_ok : checkStripPacket packet1204 = true :=
  checkStripPacket_intro packet1204_shape packet1204_cache packet1204_pair

theorem packet1205_membership : packet1205 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1205_shape : checkStripShape packet1205.row = true := by
  decide +kernel

private theorem packet1205_cache : checkStripCache packet1205 = true := by
  decide +kernel

private theorem packet1205_pair (i : Fin 7) : checkEdgePair packet1205 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1205_ok : checkStripPacket packet1205 = true :=
  checkStripPacket_intro packet1205_shape packet1205_cache packet1205_pair

theorem packet1206_membership : packet1206 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1206_shape : checkStripShape packet1206.row = true := by
  decide +kernel

private theorem packet1206_cache : checkStripCache packet1206 = true := by
  decide +kernel

private theorem packet1206_pair (i : Fin 7) : checkEdgePair packet1206 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1206_ok : checkStripPacket packet1206 = true :=
  checkStripPacket_intro packet1206_shape packet1206_cache packet1206_pair

theorem packet1207_membership : packet1207 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1207_shape : checkStripShape packet1207.row = true := by
  decide +kernel

private theorem packet1207_cache : checkStripCache packet1207 = true := by
  decide +kernel

private theorem packet1207_pair (i : Fin 7) : checkEdgePair packet1207 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1207_ok : checkStripPacket packet1207 = true :=
  checkStripPacket_intro packet1207_shape packet1207_cache packet1207_pair

theorem packet1208_membership : packet1208 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1208_shape : checkStripShape packet1208.row = true := by
  decide +kernel

private theorem packet1208_cache : checkStripCache packet1208 = true := by
  decide +kernel

private theorem packet1208_pair (i : Fin 7) : checkEdgePair packet1208 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1208_ok : checkStripPacket packet1208 = true :=
  checkStripPacket_intro packet1208_shape packet1208_cache packet1208_pair

theorem packet1209_membership : packet1209 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1209_shape : checkStripShape packet1209.row = true := by
  decide +kernel

private theorem packet1209_cache : checkStripCache packet1209 = true := by
  decide +kernel

private theorem packet1209_pair (i : Fin 7) : checkEdgePair packet1209 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1209_ok : checkStripPacket packet1209 = true :=
  checkStripPacket_intro packet1209_shape packet1209_cache packet1209_pair

theorem packet1210_membership : packet1210 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1210_shape : checkStripShape packet1210.row = true := by
  decide +kernel

private theorem packet1210_cache : checkStripCache packet1210 = true := by
  decide +kernel

private theorem packet1210_pair (i : Fin 7) : checkEdgePair packet1210 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1210_ok : checkStripPacket packet1210 = true :=
  checkStripPacket_intro packet1210_shape packet1210_cache packet1210_pair

theorem packet1211_membership : packet1211 ∈ packets050 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1211_shape : checkStripShape packet1211.row = true := by
  decide +kernel

private theorem packet1211_cache : checkStripCache packet1211 = true := by
  decide +kernel

private theorem packet1211_pair (i : Fin 7) : checkEdgePair packet1211 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1211_ok : checkStripPacket packet1211 = true :=
  checkStripPacket_intro packet1211_shape packet1211_cache packet1211_pair

theorem packets050_checked : packets050.all checkStripPacket = true := by
  simp only [packets050, List.all_cons, List.all_nil, Bool.true_and, packet1200_ok,
    packet1201_ok, packet1202_ok, packet1203_ok, packet1204_ok, packet1205_ok,
    packet1206_ok, packet1207_ok, packet1208_ok, packet1209_ok, packet1210_ok,
    packet1211_ok]

theorem packets050_valid : packets050.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
