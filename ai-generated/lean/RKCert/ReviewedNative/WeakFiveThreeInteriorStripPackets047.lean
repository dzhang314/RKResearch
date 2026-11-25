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

def packet1128 : StripRowPacket :=
  ⟨⟨⟨6,54,4,12⟩,
    ![451,1446,2827,4381,5875,7092,7877],![461,1472,2873,4448,5957,7176,7932]⟩,
    ⟨343857432704204285264752261,31631361921833479469256186880⟩,
    ⟨59856410874068951703107247419,4333525189799553687397342044160⟩⟩

def packet1129 : StripRowPacket :=
  ⟨⟨⟨6,55,4,12⟩,
    ![450,1445,2825,4379,5873,7091,7877],![461,1471,2871,4446,5956,7175,7932]⟩,
    ⟨187974373621448671039357,17135627978406811335587840⟩,
    ⟨1022145658313265462678623,73352806887677580338183680⟩⟩

def packet1130 : StripRowPacket :=
  ⟨⟨⟨5,27,4,13⟩,
    ![456,1463,2860,4432,5939,7158,7920],![467,1490,2907,4500,6026,7255,8003]⟩,
    ⟨80915185981513356851,5957456380977033687040⟩,
    ⟨3653217273006006425999,218363996798812212508160⟩⟩

def packet1131 : StripRowPacket :=
  ⟨⟨⟨5,26,4,14⟩,
    ![463,1483,2897,4486,6008,7233,7981],![472,1507,2940,4548,6088,7327,8094]⟩,
    ⟨255781355729014862255297,15942108930606585131525120⟩,
    ⟨6004882895251787159785,313605346466965934977024⟩⟩

def packet1132 : StripRowPacket :=
  ⟨⟨⟨5,26,4,15⟩,
    ![467,1497,2925,4530,6067,7304,8064],![476,1520,2964,4586,6139,7389,8192]⟩,
    ⟨597985227553507818694617,31884217861213170263050240⟩,
    ⟨5318719980443,243319911028480⟩⟩

def packet1133 : StripRowPacket :=
  ⟨⟨⟨5,27,4,14⟩,
    ![461,1480,2892,4481,6005,7232,7981],![471,1504,2935,4544,6084,7326,8094]⟩,
    ⟨48675694543792031161,2978728190488516843520⟩,
    ⟨8511576326288557676391,436727993597624425016320⟩⟩

def packet1134 : StripRowPacket :=
  ⟨⟨⟨5,27,4,15⟩,
    ![466,1495,2921,4525,6063,7303,8064],![475,1517,2960,4582,6135,7387,8192]⟩,
    ⟨113787592193654767793,5957456380977033687040⟩,
    ⟨6277042543,282128200640⟩⟩

def packet1135 : StripRowPacket :=
  ⟨⟨⟨6,56,4,8⟩,
    ![411,1327,2617,4106,5591,6874,7782],![428,1371,2687,4189,5667,6924,7802]⟩,
    ⟨-66547914755643699509,593367760427187408794560⟩,
    ⟨219889878557444509644313,76490390554350298673438720⟩⟩

def packet1136 : StripRowPacket :=
  ⟨⟨⟨6,57,4,8⟩,
    ![411,1326,2615,4104,5590,6873,7782],![428,1369,2685,4187,5665,6923,7802]⟩,
    ⟨-80149255093474403283217191,731649098886080006031321439232⟩,
    ⟨502796068906096941632641161,173354006520491469747720515584⟩⟩

def packet1137 : StripRowPacket :=
  ⟨⟨⟨6,56,5,18⟩,
    ![424,1364,2678,4178,5657,6916,7797],![434,1387,2715,4225,5702,6949,7811]⟩,
    ⟨3183986361138841401471,1186735520854374817589120⟩,
    ⟨653601454423488911589827,152980781108700597346877440⟩⟩

def packet1138 : StripRowPacket :=
  ⟨⟨⟨6,56,5,19⟩,
    ![429,1380,2706,4214,5691,6940,7806],![439,1402,2742,4260,5738,6975,7822]⟩,
    ⟨9685054912927811603431,2373471041708749635178240⟩,
    ⟨19714162539365654633887,3476835934288649939701760⟩⟩

def packet1139 : StripRowPacket :=
  ⟨⟨⟨6,57,5,18⟩,
    ![424,1362,2676,4176,5655,6915,7797],![433,1385,2713,4222,5700,6947,7811]⟩,
    ⟨15859049130785963539032788545,5853192791088640048250571513856⟩,
    ⟨1494327314637761763329884115,346708013040982939495441031168⟩⟩

def packet1140 : StripRowPacket :=
  ⟨⟨⟨6,57,5,19⟩,
    ![429,1379,2704,4212,5690,6939,7806],![438,1400,2740,4258,5736,6974,7822]⟩,
    ⟨48218341433105685843364103163,11706385582177280096501143027712⟩,
    ⟨495765622865832410848621477,86677003260245734873860257792⟩⟩

def packet1141 : StripRowPacket :=
  ⟨⟨⟨6,58,4,8⟩,
    ![410,1325,2613,4102,5588,6872,7781],![427,1368,2683,4185,5663,6922,7801]⟩,
    ⟨-43251483495746187353742727,404401508967715120202790592000⟩,
    ⟨19062119765652870479363443099,6514805710558910077783995965440⟩⟩

def packet1142 : StripRowPacket :=
  ⟨⟨⟨6,59,4,8⟩,
    ![410,1324,2612,4100,5586,6871,7781],![427,1367,2681,4183,5662,6921,7801]⟩,
    ⟨-1456395541567005549516373,13954226083371980650201717760⟩,
    ⟨82925818035289586329039181,28096671251805235027776256000⟩⟩

def packet1143 : StripRowPacket :=
  ⟨⟨⟨6,58,5,18⟩,
    ![423,1361,2674,4174,5653,6914,7797],![433,1384,2711,4220,5698,6946,7811]⟩,
    ⟨8851041259786121526359963161,3235212071741720961622324736000⟩,
    ⟨2981384037487708771026396291,685769022164095797661473259520⟩⟩

def packet1144 : StripRowPacket :=
  ⟨⟨⟨6,58,5,19⟩,
    ![429,1377,2702,4210,5688,6938,7806],![438,1399,2738,4255,5734,6973,7821]⟩,
    ⟨26899135647324334077909831299,6470424143483441923244649472000⟩,
    ⟨289109053435489201308754511,50113890081222385213723045888⟩⟩

def packet1145 : StripRowPacket :=
  ⟨⟨⟨6,59,5,18⟩,
    ![423,1360,2672,4172,5652,6913,7796],![432,1383,2709,4218,5697,6945,7810]⟩,
    ⟨308344883051708099874283203,111633808666975845201613742080⟩,
    ⟨246397859007103476173864479,56193342503610470055552512000⟩⟩

def packet1146 : StripRowPacket :=
  ⟨⟨⟨6,59,5,19⟩,
    ![428,1376,2700,4208,5686,6938,7805],![437,1398,2736,4253,5733,6972,7821]⟩,
    ⟨49299253341455807579946347,11750927228102720547538288640⟩,
    ⟨81736020485906944922412649,14048335625902617513888128000⟩⟩

def packet1147 : StripRowPacket :=
  ⟨⟨⟨6,56,5,20⟩,
    ![434,1395,2732,4249,5727,6966,7817],![443,1415,2766,4294,5774,7004,7834]⟩,
    ⟨162526713794724255049,29668388021359370439728⟩,
    ⟨1081244849040688696192229,152980781108700597346877440⟩⟩

def packet1148 : StripRowPacket :=
  ⟨⟨⟨6,56,5,21⟩,
    ![439,1408,2757,4283,5763,6994,7829],![447,1428,2790,4327,5811,7034,7848]⟩,
    ⟨16319219294228069204409,2373471041708749635178240⟩,
    ⟨129506654634928858849343,15298078110870059734687744⟩⟩

def packet1149 : StripRowPacket :=
  ⟨⟨⟨6,57,5,20⟩,
    ![434,1394,2730,4247,5725,6965,7817],![443,1414,2764,4292,5772,7003,7834]⟩,
    ⟨16179646151159861152165657309,2926596395544320024125285756928⟩,
    ⟨2471797668288897523459087701,346708013040982939495441031168⟩⟩

def packet1150 : StripRowPacket :=
  ⟨⟨⟨6,57,5,21⟩,
    ![438,1407,2755,4280,5761,6993,7828],![447,1426,2788,4324,5809,7033,7848]⟩,
    ⟨51633075509328164891265833,7442076021727450792435564544⟩,
    ⟨113866647889017900135526519,13334923578499343826747731968⟩⟩

def packet1151 : StripRowPacket :=
  ⟨⟨⟨6,56,5,22⟩,
    ![443,1421,2780,4315,5799,7024,7842],![451,1439,2812,4358,5848,7067,7865]⟩,
    ⟨755242364803007615573,91287347758028832122240⟩,
    ⟨1508888243657888480794631,152980781108700597346877440⟩⟩

def packets047 : List StripRowPacket :=
  [packet1128, packet1129, packet1130, packet1131, packet1132, packet1133,
   packet1134, packet1135, packet1136, packet1137, packet1138, packet1139,
   packet1140, packet1141, packet1142, packet1143, packet1144, packet1145,
   packet1146, packet1147, packet1148, packet1149, packet1150, packet1151]

theorem packet1128_membership : packet1128 ∈ packets047 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1128_shape : checkStripShape packet1128.row = true := by
  decide +kernel

private theorem packet1128_cache : checkStripCache packet1128 = true := by
  decide +kernel

private theorem packet1128_pair (i : Fin 7) : checkEdgePair packet1128 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1128_ok : checkStripPacket packet1128 = true :=
  checkStripPacket_intro packet1128_shape packet1128_cache packet1128_pair

theorem packet1129_membership : packet1129 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1129_shape : checkStripShape packet1129.row = true := by
  decide +kernel

private theorem packet1129_cache : checkStripCache packet1129 = true := by
  decide +kernel

private theorem packet1129_pair (i : Fin 7) : checkEdgePair packet1129 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1129_ok : checkStripPacket packet1129 = true :=
  checkStripPacket_intro packet1129_shape packet1129_cache packet1129_pair

theorem packet1130_membership : packet1130 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1130_shape : checkStripShape packet1130.row = true := by
  decide +kernel

private theorem packet1130_cache : checkStripCache packet1130 = true := by
  decide +kernel

private theorem packet1130_pair (i : Fin 7) : checkEdgePair packet1130 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1130_ok : checkStripPacket packet1130 = true :=
  checkStripPacket_intro packet1130_shape packet1130_cache packet1130_pair

theorem packet1131_membership : packet1131 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1131_shape : checkStripShape packet1131.row = true := by
  decide +kernel

private theorem packet1131_cache : checkStripCache packet1131 = true := by
  decide +kernel

private theorem packet1131_pair (i : Fin 7) : checkEdgePair packet1131 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1131_ok : checkStripPacket packet1131 = true :=
  checkStripPacket_intro packet1131_shape packet1131_cache packet1131_pair

theorem packet1132_membership : packet1132 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1132_shape : checkStripShape packet1132.row = true := by
  decide +kernel

private theorem packet1132_cache : checkStripCache packet1132 = true := by
  decide +kernel

private theorem packet1132_pair (i : Fin 7) : checkEdgePair packet1132 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1132_ok : checkStripPacket packet1132 = true :=
  checkStripPacket_intro packet1132_shape packet1132_cache packet1132_pair

theorem packet1133_membership : packet1133 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1133_shape : checkStripShape packet1133.row = true := by
  decide +kernel

private theorem packet1133_cache : checkStripCache packet1133 = true := by
  decide +kernel

private theorem packet1133_pair (i : Fin 7) : checkEdgePair packet1133 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1133_ok : checkStripPacket packet1133 = true :=
  checkStripPacket_intro packet1133_shape packet1133_cache packet1133_pair

theorem packet1134_membership : packet1134 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1134_shape : checkStripShape packet1134.row = true := by
  decide +kernel

private theorem packet1134_cache : checkStripCache packet1134 = true := by
  decide +kernel

private theorem packet1134_pair (i : Fin 7) : checkEdgePair packet1134 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1134_ok : checkStripPacket packet1134 = true :=
  checkStripPacket_intro packet1134_shape packet1134_cache packet1134_pair

theorem packet1135_membership : packet1135 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1135_shape : checkStripShape packet1135.row = true := by
  decide +kernel

private theorem packet1135_cache : checkStripCache packet1135 = true := by
  decide +kernel

private theorem packet1135_pair (i : Fin 7) : checkEdgePair packet1135 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1135_ok : checkStripPacket packet1135 = true :=
  checkStripPacket_intro packet1135_shape packet1135_cache packet1135_pair

theorem packet1136_membership : packet1136 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1136_shape : checkStripShape packet1136.row = true := by
  decide +kernel

private theorem packet1136_cache : checkStripCache packet1136 = true := by
  decide +kernel

private theorem packet1136_pair (i : Fin 7) : checkEdgePair packet1136 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1136_ok : checkStripPacket packet1136 = true :=
  checkStripPacket_intro packet1136_shape packet1136_cache packet1136_pair

theorem packet1137_membership : packet1137 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1137_shape : checkStripShape packet1137.row = true := by
  decide +kernel

private theorem packet1137_cache : checkStripCache packet1137 = true := by
  decide +kernel

private theorem packet1137_pair (i : Fin 7) : checkEdgePair packet1137 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1137_ok : checkStripPacket packet1137 = true :=
  checkStripPacket_intro packet1137_shape packet1137_cache packet1137_pair

theorem packet1138_membership : packet1138 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1138_shape : checkStripShape packet1138.row = true := by
  decide +kernel

private theorem packet1138_cache : checkStripCache packet1138 = true := by
  decide +kernel

private theorem packet1138_pair (i : Fin 7) : checkEdgePair packet1138 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1138_ok : checkStripPacket packet1138 = true :=
  checkStripPacket_intro packet1138_shape packet1138_cache packet1138_pair

theorem packet1139_membership : packet1139 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1139_shape : checkStripShape packet1139.row = true := by
  decide +kernel

private theorem packet1139_cache : checkStripCache packet1139 = true := by
  decide +kernel

private theorem packet1139_pair (i : Fin 7) : checkEdgePair packet1139 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1139_ok : checkStripPacket packet1139 = true :=
  checkStripPacket_intro packet1139_shape packet1139_cache packet1139_pair

theorem packet1140_membership : packet1140 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1140_shape : checkStripShape packet1140.row = true := by
  decide +kernel

private theorem packet1140_cache : checkStripCache packet1140 = true := by
  decide +kernel

private theorem packet1140_pair (i : Fin 7) : checkEdgePair packet1140 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1140_ok : checkStripPacket packet1140 = true :=
  checkStripPacket_intro packet1140_shape packet1140_cache packet1140_pair

theorem packet1141_membership : packet1141 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1141_shape : checkStripShape packet1141.row = true := by
  decide +kernel

private theorem packet1141_cache : checkStripCache packet1141 = true := by
  decide +kernel

private theorem packet1141_pair (i : Fin 7) : checkEdgePair packet1141 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1141_ok : checkStripPacket packet1141 = true :=
  checkStripPacket_intro packet1141_shape packet1141_cache packet1141_pair

theorem packet1142_membership : packet1142 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1142_shape : checkStripShape packet1142.row = true := by
  decide +kernel

private theorem packet1142_cache : checkStripCache packet1142 = true := by
  decide +kernel

private theorem packet1142_pair (i : Fin 7) : checkEdgePair packet1142 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1142_ok : checkStripPacket packet1142 = true :=
  checkStripPacket_intro packet1142_shape packet1142_cache packet1142_pair

theorem packet1143_membership : packet1143 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1143_shape : checkStripShape packet1143.row = true := by
  decide +kernel

private theorem packet1143_cache : checkStripCache packet1143 = true := by
  decide +kernel

private theorem packet1143_pair (i : Fin 7) : checkEdgePair packet1143 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1143_ok : checkStripPacket packet1143 = true :=
  checkStripPacket_intro packet1143_shape packet1143_cache packet1143_pair

theorem packet1144_membership : packet1144 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1144_shape : checkStripShape packet1144.row = true := by
  decide +kernel

private theorem packet1144_cache : checkStripCache packet1144 = true := by
  decide +kernel

private theorem packet1144_pair (i : Fin 7) : checkEdgePair packet1144 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1144_ok : checkStripPacket packet1144 = true :=
  checkStripPacket_intro packet1144_shape packet1144_cache packet1144_pair

theorem packet1145_membership : packet1145 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1145_shape : checkStripShape packet1145.row = true := by
  decide +kernel

private theorem packet1145_cache : checkStripCache packet1145 = true := by
  decide +kernel

private theorem packet1145_pair (i : Fin 7) : checkEdgePair packet1145 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1145_ok : checkStripPacket packet1145 = true :=
  checkStripPacket_intro packet1145_shape packet1145_cache packet1145_pair

theorem packet1146_membership : packet1146 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1146_shape : checkStripShape packet1146.row = true := by
  decide +kernel

private theorem packet1146_cache : checkStripCache packet1146 = true := by
  decide +kernel

private theorem packet1146_pair (i : Fin 7) : checkEdgePair packet1146 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1146_ok : checkStripPacket packet1146 = true :=
  checkStripPacket_intro packet1146_shape packet1146_cache packet1146_pair

theorem packet1147_membership : packet1147 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1147_shape : checkStripShape packet1147.row = true := by
  decide +kernel

private theorem packet1147_cache : checkStripCache packet1147 = true := by
  decide +kernel

private theorem packet1147_pair (i : Fin 7) : checkEdgePair packet1147 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1147_ok : checkStripPacket packet1147 = true :=
  checkStripPacket_intro packet1147_shape packet1147_cache packet1147_pair

theorem packet1148_membership : packet1148 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1148_shape : checkStripShape packet1148.row = true := by
  decide +kernel

private theorem packet1148_cache : checkStripCache packet1148 = true := by
  decide +kernel

private theorem packet1148_pair (i : Fin 7) : checkEdgePair packet1148 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1148_ok : checkStripPacket packet1148 = true :=
  checkStripPacket_intro packet1148_shape packet1148_cache packet1148_pair

theorem packet1149_membership : packet1149 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1149_shape : checkStripShape packet1149.row = true := by
  decide +kernel

private theorem packet1149_cache : checkStripCache packet1149 = true := by
  decide +kernel

private theorem packet1149_pair (i : Fin 7) : checkEdgePair packet1149 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1149_ok : checkStripPacket packet1149 = true :=
  checkStripPacket_intro packet1149_shape packet1149_cache packet1149_pair

theorem packet1150_membership : packet1150 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1150_shape : checkStripShape packet1150.row = true := by
  decide +kernel

private theorem packet1150_cache : checkStripCache packet1150 = true := by
  decide +kernel

private theorem packet1150_pair (i : Fin 7) : checkEdgePair packet1150 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1150_ok : checkStripPacket packet1150 = true :=
  checkStripPacket_intro packet1150_shape packet1150_cache packet1150_pair

theorem packet1151_membership : packet1151 ∈ packets047 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1151_shape : checkStripShape packet1151.row = true := by
  decide +kernel

private theorem packet1151_cache : checkStripCache packet1151 = true := by
  decide +kernel

private theorem packet1151_pair (i : Fin 7) : checkEdgePair packet1151 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1151_ok : checkStripPacket packet1151 = true :=
  checkStripPacket_intro packet1151_shape packet1151_cache packet1151_pair

theorem packets047_checked : packets047.all checkStripPacket = true := by
  simp only [packets047, List.all_cons, List.all_nil, Bool.true_and, packet1128_ok,
    packet1129_ok, packet1130_ok, packet1131_ok, packet1132_ok, packet1133_ok,
    packet1134_ok, packet1135_ok, packet1136_ok, packet1137_ok, packet1138_ok,
    packet1139_ok, packet1140_ok, packet1141_ok, packet1142_ok, packet1143_ok,
    packet1144_ok, packet1145_ok, packet1146_ok, packet1147_ok, packet1148_ok,
    packet1149_ok, packet1150_ok, packet1151_ok]

theorem packets047_valid : packets047.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
