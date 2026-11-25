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

def packet1032 : StripRowPacket :=
  ⟨⟨⟨5,26,4,7⟩,
    ![396,1285,2554,4037,5535,6841,7771],![418,1340,2636,4127,5610,6887,7788]⟩,
    ⟨-93394901210316934777567,31884217861213170263050240⟩,
    ⟨33411309273510165507,196003341541853709360640⟩⟩

def packet1033 : StripRowPacket :=
  ⟨⟨⟨5,27,4,6⟩,
    ![375,1232,2480,3963,5478,6808,7760],![401,1294,2565,4049,5545,6848,7775]⟩,
    ⟨-17069117880490790723,2978728190488516843520⟩,
    ⟨-102687083265800083523,39702544872511311365120⟩⟩

def packet1034 : StripRowPacket :=
  ⟨⟨⟨5,27,4,7⟩,
    ![395,1283,2550,4033,5532,6838,7770],![417,1338,2632,4123,5606,6884,7788]⟩,
    ⟨-321855139180197745,108317388745036976128⟩,
    ⟨1889596608818597641,10918199839940610625408⟩⟩

def packet1035 : StripRowPacket :=
  ⟨⟨⟨4,14,3,0⟩,
    ![0,811,2080,3644,5263,6695,7724],![220,977,2213,3740,5328,6731,7737]⟩,
    ⟨-528786627687,22954587264752⟩,
    ⟨-45516745428056836009,2738494041225521413120⟩⟩

def packet1036 : StripRowPacket :=
  ⟨⟨⟨5,28,4,2⟩,
    ![192,952,2195,3730,5319,6724,7733],![275,1045,2274,3788,5359,6747,7742]⟩,
    ⟨-22528139158433146524399,1321465047388920860208640⟩,
    ⟨-8741804950105328612521,630651859159033974845440⟩⟩

def packet1037 : StripRowPacket :=
  ⟨⟨⟨5,28,4,3⟩,
    ![260,1027,2260,3778,5351,6740,7738],![321,1116,2344,3844,5396,6766,7748]⟩,
    ⟨-37637809057223087009917,2642930094777841720417280⟩,
    ⟨-1742818923437178337891,157662964789758493711360⟩⟩

def packet1038 : StripRowPacket :=
  ⟨⟨⟨5,29,4,2⟩,
    ![192,951,2192,3725,5315,6722,7732],![274,1043,2271,3784,5355,6744,7741]⟩,
    ⟨-7164231598024586954052851,413466101293807413566420992⟩,
    ⟨-537092905719881109469285,38100884816733463109445632⟩⟩

def packet1039 : StripRowPacket :=
  ⟨⟨⟨5,29,4,3⟩,
    ![260,1026,2257,3774,5347,6738,7737],![320,1114,2341,3840,5392,6763,7747]⟩,
    ⟨-11968004027720045152851801,826932202587614827132841984⟩,
    ⟨-107078486727265355888423,9525221204183365777361408⟩⟩

def packet1040 : StripRowPacket :=
  ⟨⟨⟨4,15,3,0⟩,
    ![0,809,2074,3636,5256,6691,7722],![219,973,2206,3732,5320,6726,7735]⟩,
    ⟨-17,715⟩,
    ⟨-15778664951557,918183490590080⟩⟩

def packet1041 : StripRowPacket :=
  ⟨⟨⟨5,30,4,2⟩,
    ![192,949,2189,3721,5311,6719,7731],![274,1041,2268,3780,5351,6742,7741]⟩,
    ⟨-260470826357959362683821,14795799524121628336749568⟩,
    ⟨-14607558676715054209446795,1019396223114756880215240704⟩⟩

def packet1042 : StripRowPacket :=
  ⟨⟨⟨5,30,4,3⟩,
    ![260,1024,2254,3770,5343,6736,7736],![319,1113,2337,3836,5389,6761,7747]⟩,
    ⟨-435077198852836625061671,29591599048243256673499136⟩,
    ⟨-2912267677075111425321113,254849055778689220053810176⟩⟩

def packet1043 : StripRowPacket :=
  ⟨⟨⟨5,31,4,2⟩,
    ![192,948,2186,3717,5308,6717,7731],![273,1039,2264,3776,5348,6739,7740]⟩,
    ⟨-4541724411581133,254020964479293440⟩,
    ⟨-220352499596863,15133378162439680⟩⟩

def packet1044 : StripRowPacket :=
  ⟨⟨⟨5,31,4,3⟩,
    ![259,1023,2251,3766,5340,6733,7736],![319,1111,2334,3832,5385,6759,7746]⟩,
    ⟨-689592176311957,46185629905326080⟩,
    ⟨-43931065566961,3783344540609920⟩⟩

def packet1045 : StripRowPacket :=
  ⟨⟨⟨5,28,4,4⟩,
    ![310,1101,2330,3833,5387,6759,7744],![355,1182,2417,3906,5438,6788,7755]⟩,
    ⟨-581141149953459249443,50825578745727725392640⟩,
    ⟨-5200746437392098090607,630651859159033974845440⟩⟩

def packet1046 : StripRowPacket :=
  ⟨⟨⟨5,28,4,5⟩,
    ![347,1169,2404,3894,5428,6781,7751],![380,1241,2490,3973,5487,6814,7764]⟩,
    ⟨-414561282507939544221,48053274450506213098496⟩,
    ⟨-343021718103548282965,63065185915903397484544⟩⟩

def packet1047 : StripRowPacket :=
  ⟨⟨⟨5,29,4,4⟩,
    ![310,1099,2327,3829,5383,6757,7743],![354,1180,2413,3902,5435,6786,7755]⟩,
    ⟨-2401886214847729099399475,206733050646903706783210496⟩,
    ⟨-319534988098241737638099,38100884816733463109445632⟩⟩

def packet1048 : StripRowPacket :=
  ⟨⟨⟨5,29,4,5⟩,
    ![346,1168,2400,3890,5424,6778,7750],![379,1238,2487,3969,5483,6812,7763]⟩,
    ⟨-7247085691061787642343999,826932202587614827132841984⟩,
    ⟨-105378014643711025861253,19050442408366731554722816⟩⟩

def packet1049 : StripRowPacket :=
  ⟨⟨⟨5,28,4,6⟩,
    ![374,1230,2476,3959,5475,6806,7759],![400,1292,2562,4045,5541,6845,7774]⟩,
    ⟨-7691200639146734446637,1321465047388920860208640⟩,
    ⟨-127668301898374428361,48511681473771844218880⟩⟩

def packet1050 : StripRowPacket :=
  ⟨⟨⟨5,28,4,7⟩,
    ![394,1281,2547,4029,5528,6836,7769],![416,1335,2628,4118,5603,6882,7787]⟩,
    ⟨-7963932018650262854393,2642930094777841720417280⟩,
    ⟨13855166459718461533,78831482394879246855680⟩⟩

def packet1051 : StripRowPacket :=
  ⟨⟨⟨5,29,4,6⟩,
    ![373,1228,2473,3955,5471,6804,7758],![400,1289,2558,4041,5538,6843,7773]⟩,
    ⟨-2443313261366329443545049,413466101293807413566420992⟩,
    ⟨-101977070476602365806913,38100884816733463109445632⟩⟩

def packet1052 : StripRowPacket :=
  ⟨⟨⟨5,29,4,7⟩,
    ![394,1279,2543,4025,5525,6834,7768],![415,1333,2625,4114,5599,6880,7786]⟩,
    ⟨-2526167354403530131836197,826932202587614827132841984⟩,
    ⟨850236041777165013585,4762610602091682888680704⟩⟩

def packet1053 : StripRowPacket :=
  ⟨⟨⟨5,30,4,4⟩,
    ![309,1098,2324,3825,5379,6754,7742],![353,1178,2410,3898,5431,6783,7754]⟩,
    ⟨-87303186247438631188925,7397899762060814168374784⟩,
    ⟨-668506364606602861009393,78415094085750529247326208⟩⟩

def packet1054 : StripRowPacket :=
  ⟨⟨⟨5,30,4,5⟩,
    ![346,1166,2397,3886,5421,6776,7749],![379,1236,2483,3965,5479,6810,7762]⟩,
    ⟨-263348291126672424449729,29591599048243256673499136⟩,
    ⟨-2866047385735614342479883,509698111557378440107620352⟩⟩

def packet1055 : StripRowPacket :=
  ⟨⟨⟨5,31,4,4⟩,
    ![309,1096,2321,3821,5376,6752,7742],![353,1176,2407,3894,5427,6781,7753]⟩,
    ⟨-1521894763925197,127010482239646720⟩,
    ⟨-26219204987765,3026675632487936⟩⟩

def packets043 : List StripRowPacket :=
  [packet1032, packet1033, packet1034, packet1035, packet1036, packet1037,
   packet1038, packet1039, packet1040, packet1041, packet1042, packet1043,
   packet1044, packet1045, packet1046, packet1047, packet1048, packet1049,
   packet1050, packet1051, packet1052, packet1053, packet1054, packet1055]

theorem packet1032_membership : packet1032 ∈ packets043 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1032_shape : checkStripShape packet1032.row = true := by
  decide +kernel

private theorem packet1032_cache : checkStripCache packet1032 = true := by
  decide +kernel

private theorem packet1032_pair (i : Fin 7) : checkEdgePair packet1032 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1032_ok : checkStripPacket packet1032 = true :=
  checkStripPacket_intro packet1032_shape packet1032_cache packet1032_pair

theorem packet1033_membership : packet1033 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1033_shape : checkStripShape packet1033.row = true := by
  decide +kernel

private theorem packet1033_cache : checkStripCache packet1033 = true := by
  decide +kernel

private theorem packet1033_pair (i : Fin 7) : checkEdgePair packet1033 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1033_ok : checkStripPacket packet1033 = true :=
  checkStripPacket_intro packet1033_shape packet1033_cache packet1033_pair

theorem packet1034_membership : packet1034 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1034_shape : checkStripShape packet1034.row = true := by
  decide +kernel

private theorem packet1034_cache : checkStripCache packet1034 = true := by
  decide +kernel

private theorem packet1034_pair (i : Fin 7) : checkEdgePair packet1034 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1034_ok : checkStripPacket packet1034 = true :=
  checkStripPacket_intro packet1034_shape packet1034_cache packet1034_pair

theorem packet1035_membership : packet1035 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1035_shape : checkStripShape packet1035.row = true := by
  decide +kernel

private theorem packet1035_cache : checkStripCache packet1035 = true := by
  decide +kernel

private theorem packet1035_pair (i : Fin 7) : checkEdgePair packet1035 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1035_ok : checkStripPacket packet1035 = true :=
  checkStripPacket_intro packet1035_shape packet1035_cache packet1035_pair

theorem packet1036_membership : packet1036 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1036_shape : checkStripShape packet1036.row = true := by
  decide +kernel

private theorem packet1036_cache : checkStripCache packet1036 = true := by
  decide +kernel

private theorem packet1036_pair (i : Fin 7) : checkEdgePair packet1036 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1036_ok : checkStripPacket packet1036 = true :=
  checkStripPacket_intro packet1036_shape packet1036_cache packet1036_pair

theorem packet1037_membership : packet1037 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1037_shape : checkStripShape packet1037.row = true := by
  decide +kernel

private theorem packet1037_cache : checkStripCache packet1037 = true := by
  decide +kernel

private theorem packet1037_pair (i : Fin 7) : checkEdgePair packet1037 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1037_ok : checkStripPacket packet1037 = true :=
  checkStripPacket_intro packet1037_shape packet1037_cache packet1037_pair

theorem packet1038_membership : packet1038 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1038_shape : checkStripShape packet1038.row = true := by
  decide +kernel

private theorem packet1038_cache : checkStripCache packet1038 = true := by
  decide +kernel

private theorem packet1038_pair (i : Fin 7) : checkEdgePair packet1038 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1038_ok : checkStripPacket packet1038 = true :=
  checkStripPacket_intro packet1038_shape packet1038_cache packet1038_pair

theorem packet1039_membership : packet1039 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1039_shape : checkStripShape packet1039.row = true := by
  decide +kernel

private theorem packet1039_cache : checkStripCache packet1039 = true := by
  decide +kernel

private theorem packet1039_pair (i : Fin 7) : checkEdgePair packet1039 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1039_ok : checkStripPacket packet1039 = true :=
  checkStripPacket_intro packet1039_shape packet1039_cache packet1039_pair

theorem packet1040_membership : packet1040 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1040_shape : checkStripShape packet1040.row = true := by
  decide +kernel

private theorem packet1040_cache : checkStripCache packet1040 = true := by
  decide +kernel

private theorem packet1040_pair (i : Fin 7) : checkEdgePair packet1040 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1040_ok : checkStripPacket packet1040 = true :=
  checkStripPacket_intro packet1040_shape packet1040_cache packet1040_pair

theorem packet1041_membership : packet1041 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1041_shape : checkStripShape packet1041.row = true := by
  decide +kernel

private theorem packet1041_cache : checkStripCache packet1041 = true := by
  decide +kernel

private theorem packet1041_pair (i : Fin 7) : checkEdgePair packet1041 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1041_ok : checkStripPacket packet1041 = true :=
  checkStripPacket_intro packet1041_shape packet1041_cache packet1041_pair

theorem packet1042_membership : packet1042 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1042_shape : checkStripShape packet1042.row = true := by
  decide +kernel

private theorem packet1042_cache : checkStripCache packet1042 = true := by
  decide +kernel

private theorem packet1042_pair (i : Fin 7) : checkEdgePair packet1042 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1042_ok : checkStripPacket packet1042 = true :=
  checkStripPacket_intro packet1042_shape packet1042_cache packet1042_pair

theorem packet1043_membership : packet1043 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1043_shape : checkStripShape packet1043.row = true := by
  decide +kernel

private theorem packet1043_cache : checkStripCache packet1043 = true := by
  decide +kernel

private theorem packet1043_pair (i : Fin 7) : checkEdgePair packet1043 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1043_ok : checkStripPacket packet1043 = true :=
  checkStripPacket_intro packet1043_shape packet1043_cache packet1043_pair

theorem packet1044_membership : packet1044 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1044_shape : checkStripShape packet1044.row = true := by
  decide +kernel

private theorem packet1044_cache : checkStripCache packet1044 = true := by
  decide +kernel

private theorem packet1044_pair (i : Fin 7) : checkEdgePair packet1044 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1044_ok : checkStripPacket packet1044 = true :=
  checkStripPacket_intro packet1044_shape packet1044_cache packet1044_pair

theorem packet1045_membership : packet1045 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1045_shape : checkStripShape packet1045.row = true := by
  decide +kernel

private theorem packet1045_cache : checkStripCache packet1045 = true := by
  decide +kernel

private theorem packet1045_pair (i : Fin 7) : checkEdgePair packet1045 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1045_ok : checkStripPacket packet1045 = true :=
  checkStripPacket_intro packet1045_shape packet1045_cache packet1045_pair

theorem packet1046_membership : packet1046 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1046_shape : checkStripShape packet1046.row = true := by
  decide +kernel

private theorem packet1046_cache : checkStripCache packet1046 = true := by
  decide +kernel

private theorem packet1046_pair (i : Fin 7) : checkEdgePair packet1046 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1046_ok : checkStripPacket packet1046 = true :=
  checkStripPacket_intro packet1046_shape packet1046_cache packet1046_pair

theorem packet1047_membership : packet1047 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1047_shape : checkStripShape packet1047.row = true := by
  decide +kernel

private theorem packet1047_cache : checkStripCache packet1047 = true := by
  decide +kernel

private theorem packet1047_pair (i : Fin 7) : checkEdgePair packet1047 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1047_ok : checkStripPacket packet1047 = true :=
  checkStripPacket_intro packet1047_shape packet1047_cache packet1047_pair

theorem packet1048_membership : packet1048 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1048_shape : checkStripShape packet1048.row = true := by
  decide +kernel

private theorem packet1048_cache : checkStripCache packet1048 = true := by
  decide +kernel

private theorem packet1048_pair (i : Fin 7) : checkEdgePair packet1048 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1048_ok : checkStripPacket packet1048 = true :=
  checkStripPacket_intro packet1048_shape packet1048_cache packet1048_pair

theorem packet1049_membership : packet1049 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1049_shape : checkStripShape packet1049.row = true := by
  decide +kernel

private theorem packet1049_cache : checkStripCache packet1049 = true := by
  decide +kernel

private theorem packet1049_pair (i : Fin 7) : checkEdgePair packet1049 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1049_ok : checkStripPacket packet1049 = true :=
  checkStripPacket_intro packet1049_shape packet1049_cache packet1049_pair

theorem packet1050_membership : packet1050 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1050_shape : checkStripShape packet1050.row = true := by
  decide +kernel

private theorem packet1050_cache : checkStripCache packet1050 = true := by
  decide +kernel

private theorem packet1050_pair (i : Fin 7) : checkEdgePair packet1050 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1050_ok : checkStripPacket packet1050 = true :=
  checkStripPacket_intro packet1050_shape packet1050_cache packet1050_pair

theorem packet1051_membership : packet1051 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1051_shape : checkStripShape packet1051.row = true := by
  decide +kernel

private theorem packet1051_cache : checkStripCache packet1051 = true := by
  decide +kernel

private theorem packet1051_pair (i : Fin 7) : checkEdgePair packet1051 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1051_ok : checkStripPacket packet1051 = true :=
  checkStripPacket_intro packet1051_shape packet1051_cache packet1051_pair

theorem packet1052_membership : packet1052 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1052_shape : checkStripShape packet1052.row = true := by
  decide +kernel

private theorem packet1052_cache : checkStripCache packet1052 = true := by
  decide +kernel

private theorem packet1052_pair (i : Fin 7) : checkEdgePair packet1052 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1052_ok : checkStripPacket packet1052 = true :=
  checkStripPacket_intro packet1052_shape packet1052_cache packet1052_pair

theorem packet1053_membership : packet1053 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1053_shape : checkStripShape packet1053.row = true := by
  decide +kernel

private theorem packet1053_cache : checkStripCache packet1053 = true := by
  decide +kernel

private theorem packet1053_pair (i : Fin 7) : checkEdgePair packet1053 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1053_ok : checkStripPacket packet1053 = true :=
  checkStripPacket_intro packet1053_shape packet1053_cache packet1053_pair

theorem packet1054_membership : packet1054 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1054_shape : checkStripShape packet1054.row = true := by
  decide +kernel

private theorem packet1054_cache : checkStripCache packet1054 = true := by
  decide +kernel

private theorem packet1054_pair (i : Fin 7) : checkEdgePair packet1054 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1054_ok : checkStripPacket packet1054 = true :=
  checkStripPacket_intro packet1054_shape packet1054_cache packet1054_pair

theorem packet1055_membership : packet1055 ∈ packets043 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1055_shape : checkStripShape packet1055.row = true := by
  decide +kernel

private theorem packet1055_cache : checkStripCache packet1055 = true := by
  decide +kernel

private theorem packet1055_pair (i : Fin 7) : checkEdgePair packet1055 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1055_ok : checkStripPacket packet1055 = true :=
  checkStripPacket_intro packet1055_shape packet1055_cache packet1055_pair

theorem packets043_checked : packets043.all checkStripPacket = true := by
  simp only [packets043, List.all_cons, List.all_nil, Bool.true_and, packet1032_ok,
    packet1033_ok, packet1034_ok, packet1035_ok, packet1036_ok, packet1037_ok,
    packet1038_ok, packet1039_ok, packet1040_ok, packet1041_ok, packet1042_ok,
    packet1043_ok, packet1044_ok, packet1045_ok, packet1046_ok, packet1047_ok,
    packet1048_ok, packet1049_ok, packet1050_ok, packet1051_ok, packet1052_ok,
    packet1053_ok, packet1054_ok, packet1055_ok]

theorem packets043_valid : packets043.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
