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

def packet1080 : StripRowPacket :=
  ⟨⟨⟨6,50,5,21⟩,
    ![442,1417,2769,4295,5773,7000,7830],![450,1436,2803,4340,5822,7040,7850]⟩,
    ⟨82366279986495604405879437,12680156469123755736659025920⟩,
    ⟨56198347285863661212436907,7008817629307622759777935360⟩⟩

def packet1081 : StripRowPacket :=
  ⟨⟨⟨6,51,5,20⟩,
    ![437,1401,2742,4259,5735,6971,7818],![446,1422,2777,4305,5783,7009,7836]⟩,
    ⟨115415729410774333771447,22098668005430270272139264⟩,
    ⟨1827147028486674362673093,270429679421498528521441280⟩⟩

def packet1082 : StripRowPacket :=
  ⟨⟨⟨6,51,5,21⟩,
    ![441,1415,2767,4293,5771,6999,7830],![450,1435,2800,4338,5820,7039,7850]⟩,
    ⟨2899250188845274366466563,441973360108605405442785280⟩,
    ⟨1532131597577119890764537,189300775595048969965008896⟩⟩

def packet1083 : StripRowPacket :=
  ⟨⟨⟨6,50,5,22⟩,
    ![446,1429,2793,4328,5809,7030,7844],![454,1448,2825,4372,5858,7073,7867]⟩,
    ⟨762803346800616293650067,97539665147105813358915584⟩,
    ⟨11906239022553473036541701,1274330478055931410868715520⟩⟩

def packet1084 : StripRowPacket :=
  ⟨⟨⟨6,50,5,23⟩,
    ![450,1441,2815,4360,5846,7061,7860],![457,1459,2845,4402,5894,7107,7885]⟩,
    ⟨115962590181664631943137983,12680156469123755736659025920⟩,
    ⟨18692570490556135547380451,1752204407326905689944483840⟩⟩

def packet1085 : StripRowPacket :=
  ⟨⟨⟨6,51,5,22⟩,
    ![445,1428,2791,4326,5807,7029,7844],![453,1447,2822,4369,5856,7072,7866]⟩,
    ⟨1745092894737531028752093,220986680054302702721392640⟩,
    ⟨17852602752135677276579089,1893007755950489699650088960⟩⟩

def packet1086 : StripRowPacket :=
  ⟨⟨⟨6,51,5,23⟩,
    ![449,1440,2813,4357,5844,7061,7859],![457,1457,2843,4399,5893,7106,7885]⟩,
    ⟨4081121390104849748541809,441973360108605405442785280⟩,
    ⟨2547986191062519455689101,236625969493811212456261120⟩⟩

def packet1087 : StripRowPacket :=
  ⟨⟨⟨6,52,4,8⟩,
    ![413,1332,2624,4114,5598,6878,7783],![430,1376,2695,4198,5674,6928,7803]⟩,
    ⟨-18965714531056016998111,154537859227278008698408192⟩,
    ⟨62481140415701847726331,22547417238419100401803264⟩⟩

def packet1088 : StripRowPacket :=
  ⟨⟨⟨6,53,4,8⟩,
    ![413,1330,2622,4112,5596,6877,7783],![430,1374,2693,4195,5672,6927,7803]⟩,
    ⟨-406404495764063200998893,3385053498427870276610606080⟩,
    ⟨29179722488789721888673981,10431896163129009450006794240⟩⟩

def packet1089 : StripRowPacket :=
  ⟨⟨⟨6,52,5,18⟩,
    ![426,1369,2685,4186,5664,6920,7799],![436,1392,2723,4233,5709,6953,7813]⟩,
    ⟨3184458190758652176382885,1236302873818224069587265536⟩,
    ⟨2415570068887648323328005,586232848198896610446884864⟩⟩

def packet1090 : StripRowPacket :=
  ⟨⟨⟨6,52,5,19⟩,
    ![431,1385,2713,4222,5698,6944,7808],![441,1407,2750,4268,5745,6979,7823]⟩,
    ⟨9705100288524404665133543,2472605747636448139174531072⟩,
    ⟨801657621741762151442851,146558212049724152611721216⟩⟩

def packet1091 : StripRowPacket :=
  ⟨⟨⟨6,53,5,18⟩,
    ![425,1367,2683,4184,5662,6919,7798],![435,1391,2721,4231,5707,6952,7812]⟩,
    ⟨130899579583422102587991801,50292223405214072681071861760⟩,
    ⟨7887880309004205946363981,1896708393296183536364871680⟩⟩

def packet1092 : StripRowPacket :=
  ⟨⟨⟨6,53,5,19⟩,
    ![431,1384,2711,4220,5696,6943,7807],![440,1406,2748,4266,5743,6978,7823]⟩,
    ⟨253741567164666066113792063,64008284333908819775909642240⟩,
    ⟨5758696091025654352132981,1043189616312900945000679424⟩⟩

def packet1093 : StripRowPacket :=
  ⟨⟨⟨6,54,4,8⟩,
    ![412,1329,2621,4110,5595,6876,7783],![429,1373,2691,4193,5670,6926,7803]⟩,
    ⟨-168808215250262356041363,1437789178265158157693463040⟩,
    ⟨1747724964529741253368327593,619075027114221955342477434880⟩⟩

def packet1094 : StripRowPacket :=
  ⟨⟨⟨6,55,4,8⟩,
    ![412,1328,2619,4108,5593,6875,7782],![429,1372,2689,4191,5669,6925,7802]⟩,
    ⟨-983356352889520184833,8567813989203405667793920⟩,
    ⟨208980703657017824964499,73352806887677580338183680⟩⟩

def packet1095 : StripRowPacket :=
  ⟨⟨⟨6,54,5,18⟩,
    ![425,1366,2681,4182,5660,6918,7798],![435,1389,2719,4229,5705,6951,7812]⟩,
    ⟨332716090497686969766022303,126525447687333917877024747520⟩,
    ⟨36373733534006568279538824869,8667050379599107374794684088320⟩⟩

def packet1096 : StripRowPacket :=
  ⟨⟨⟨6,54,5,19⟩,
    ![430,1382,2709,4218,5695,6942,7807],![440,1404,2746,4264,5741,6977,7823]⟩,
    ⟨77923338033467999740746681,19465453490359064288773038080⟩,
    ⟨928448414703783827152328143,166674045761521295669128540160⟩⟩

def packet1097 : StripRowPacket :=
  ⟨⟨⟨6,55,5,18⟩,
    ![424,1365,2679,4180,5658,6917,7798],![434,1388,2717,4227,5704,6950,7812]⟩,
    ⟨182074235504111549930359,68542511913627245342351360⟩,
    ⟨47788665075238273796733,11285047213488858513566720⟩⟩

def packet1098 : StripRowPacket :=
  ⟨⟨⟨6,55,5,19⟩,
    ![430,1381,2708,4216,5693,6941,7807],![439,1403,2744,4262,5739,6976,7822]⟩,
    ⟨554089557335450811269741,137085023827254490684702720⟩,
    ⟨41227194232107973439303,7335280688767758033818368⟩⟩

def packet1099 : StripRowPacket :=
  ⟨⟨⟨6,52,5,20⟩,
    ![436,1400,2740,4257,5733,6970,7818],![445,1421,2775,4303,5781,7008,7836]⟩,
    ⟨296392822625716022215939,56195585173555639526693888⟩,
    ⟨3997690905046448888214803,586232848198896610446884864⟩⟩

def packet1100 : StripRowPacket :=
  ⟨⟨⟨6,52,5,21⟩,
    ![441,1414,2765,4291,5769,6998,7830],![449,1433,2798,4335,5818,7038,7850]⟩,
    ⟨2339638300362657898552727,353229392519492591310647296⟩,
    ⟨2394375661562924585329101,293116424099448305223442432⟩⟩

def packet1101 : StripRowPacket :=
  ⟨⟨⟨6,53,5,20⟩,
    ![436,1399,2738,4255,5732,6969,7818],![444,1419,2773,4300,5779,7007,7835]⟩,
    ⟨937430090863686004567885043,176022781918249254383751516160⟩,
    ⟨143581160241979908675315449,20863792326258018900013588480⟩⟩

def packet1102 : StripRowPacket :=
  ⟨⟨⟨6,53,5,21⟩,
    ![440,1412,2763,4289,5768,6997,7830],![449,1432,2796,4333,5816,7037,7849]⟩,
    ⟨4708283488098161309291367651,704091127672997017535006064640⟩,
    ⟨85994199331723365153985639,10431896163129009450006794240⟩⟩

def packet1103 : StripRowPacket :=
  ⟨⟨⟨6,52,5,22⟩,
    ![445,1426,2788,4324,5806,7028,7843],![453,1445,2820,4367,5855,7071,7866]⟩,
    ⟨9856826004772852801118431,1236302873818224069587265536⟩,
    ⟨5579811741205249453101601,586232848198896610446884864⟩⟩

def packets045 : List StripRowPacket :=
  [packet1080, packet1081, packet1082, packet1083, packet1084, packet1085,
   packet1086, packet1087, packet1088, packet1089, packet1090, packet1091,
   packet1092, packet1093, packet1094, packet1095, packet1096, packet1097,
   packet1098, packet1099, packet1100, packet1101, packet1102, packet1103]

theorem packet1080_membership : packet1080 ∈ packets045 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1080_shape : checkStripShape packet1080.row = true := by
  decide +kernel

private theorem packet1080_cache : checkStripCache packet1080 = true := by
  decide +kernel

private theorem packet1080_pair (i : Fin 7) : checkEdgePair packet1080 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1080_ok : checkStripPacket packet1080 = true :=
  checkStripPacket_intro packet1080_shape packet1080_cache packet1080_pair

theorem packet1081_membership : packet1081 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1081_shape : checkStripShape packet1081.row = true := by
  decide +kernel

private theorem packet1081_cache : checkStripCache packet1081 = true := by
  decide +kernel

private theorem packet1081_pair (i : Fin 7) : checkEdgePair packet1081 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1081_ok : checkStripPacket packet1081 = true :=
  checkStripPacket_intro packet1081_shape packet1081_cache packet1081_pair

theorem packet1082_membership : packet1082 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1082_shape : checkStripShape packet1082.row = true := by
  decide +kernel

private theorem packet1082_cache : checkStripCache packet1082 = true := by
  decide +kernel

private theorem packet1082_pair (i : Fin 7) : checkEdgePair packet1082 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1082_ok : checkStripPacket packet1082 = true :=
  checkStripPacket_intro packet1082_shape packet1082_cache packet1082_pair

theorem packet1083_membership : packet1083 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1083_shape : checkStripShape packet1083.row = true := by
  decide +kernel

private theorem packet1083_cache : checkStripCache packet1083 = true := by
  decide +kernel

private theorem packet1083_pair (i : Fin 7) : checkEdgePair packet1083 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1083_ok : checkStripPacket packet1083 = true :=
  checkStripPacket_intro packet1083_shape packet1083_cache packet1083_pair

theorem packet1084_membership : packet1084 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1084_shape : checkStripShape packet1084.row = true := by
  decide +kernel

private theorem packet1084_cache : checkStripCache packet1084 = true := by
  decide +kernel

private theorem packet1084_pair (i : Fin 7) : checkEdgePair packet1084 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1084_ok : checkStripPacket packet1084 = true :=
  checkStripPacket_intro packet1084_shape packet1084_cache packet1084_pair

theorem packet1085_membership : packet1085 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1085_shape : checkStripShape packet1085.row = true := by
  decide +kernel

private theorem packet1085_cache : checkStripCache packet1085 = true := by
  decide +kernel

private theorem packet1085_pair (i : Fin 7) : checkEdgePair packet1085 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1085_ok : checkStripPacket packet1085 = true :=
  checkStripPacket_intro packet1085_shape packet1085_cache packet1085_pair

theorem packet1086_membership : packet1086 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1086_shape : checkStripShape packet1086.row = true := by
  decide +kernel

private theorem packet1086_cache : checkStripCache packet1086 = true := by
  decide +kernel

private theorem packet1086_pair (i : Fin 7) : checkEdgePair packet1086 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1086_ok : checkStripPacket packet1086 = true :=
  checkStripPacket_intro packet1086_shape packet1086_cache packet1086_pair

theorem packet1087_membership : packet1087 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1087_shape : checkStripShape packet1087.row = true := by
  decide +kernel

private theorem packet1087_cache : checkStripCache packet1087 = true := by
  decide +kernel

private theorem packet1087_pair (i : Fin 7) : checkEdgePair packet1087 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1087_ok : checkStripPacket packet1087 = true :=
  checkStripPacket_intro packet1087_shape packet1087_cache packet1087_pair

theorem packet1088_membership : packet1088 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1088_shape : checkStripShape packet1088.row = true := by
  decide +kernel

private theorem packet1088_cache : checkStripCache packet1088 = true := by
  decide +kernel

private theorem packet1088_pair (i : Fin 7) : checkEdgePair packet1088 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1088_ok : checkStripPacket packet1088 = true :=
  checkStripPacket_intro packet1088_shape packet1088_cache packet1088_pair

theorem packet1089_membership : packet1089 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1089_shape : checkStripShape packet1089.row = true := by
  decide +kernel

private theorem packet1089_cache : checkStripCache packet1089 = true := by
  decide +kernel

private theorem packet1089_pair (i : Fin 7) : checkEdgePair packet1089 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1089_ok : checkStripPacket packet1089 = true :=
  checkStripPacket_intro packet1089_shape packet1089_cache packet1089_pair

theorem packet1090_membership : packet1090 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1090_shape : checkStripShape packet1090.row = true := by
  decide +kernel

private theorem packet1090_cache : checkStripCache packet1090 = true := by
  decide +kernel

private theorem packet1090_pair (i : Fin 7) : checkEdgePair packet1090 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1090_ok : checkStripPacket packet1090 = true :=
  checkStripPacket_intro packet1090_shape packet1090_cache packet1090_pair

theorem packet1091_membership : packet1091 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1091_shape : checkStripShape packet1091.row = true := by
  decide +kernel

private theorem packet1091_cache : checkStripCache packet1091 = true := by
  decide +kernel

private theorem packet1091_pair (i : Fin 7) : checkEdgePair packet1091 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1091_ok : checkStripPacket packet1091 = true :=
  checkStripPacket_intro packet1091_shape packet1091_cache packet1091_pair

theorem packet1092_membership : packet1092 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1092_shape : checkStripShape packet1092.row = true := by
  decide +kernel

private theorem packet1092_cache : checkStripCache packet1092 = true := by
  decide +kernel

private theorem packet1092_pair (i : Fin 7) : checkEdgePair packet1092 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1092_ok : checkStripPacket packet1092 = true :=
  checkStripPacket_intro packet1092_shape packet1092_cache packet1092_pair

theorem packet1093_membership : packet1093 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1093_shape : checkStripShape packet1093.row = true := by
  decide +kernel

private theorem packet1093_cache : checkStripCache packet1093 = true := by
  decide +kernel

private theorem packet1093_pair (i : Fin 7) : checkEdgePair packet1093 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1093_ok : checkStripPacket packet1093 = true :=
  checkStripPacket_intro packet1093_shape packet1093_cache packet1093_pair

theorem packet1094_membership : packet1094 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1094_shape : checkStripShape packet1094.row = true := by
  decide +kernel

private theorem packet1094_cache : checkStripCache packet1094 = true := by
  decide +kernel

private theorem packet1094_pair (i : Fin 7) : checkEdgePair packet1094 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1094_ok : checkStripPacket packet1094 = true :=
  checkStripPacket_intro packet1094_shape packet1094_cache packet1094_pair

theorem packet1095_membership : packet1095 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1095_shape : checkStripShape packet1095.row = true := by
  decide +kernel

private theorem packet1095_cache : checkStripCache packet1095 = true := by
  decide +kernel

private theorem packet1095_pair (i : Fin 7) : checkEdgePair packet1095 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1095_ok : checkStripPacket packet1095 = true :=
  checkStripPacket_intro packet1095_shape packet1095_cache packet1095_pair

theorem packet1096_membership : packet1096 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1096_shape : checkStripShape packet1096.row = true := by
  decide +kernel

private theorem packet1096_cache : checkStripCache packet1096 = true := by
  decide +kernel

private theorem packet1096_pair (i : Fin 7) : checkEdgePair packet1096 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1096_ok : checkStripPacket packet1096 = true :=
  checkStripPacket_intro packet1096_shape packet1096_cache packet1096_pair

theorem packet1097_membership : packet1097 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1097_shape : checkStripShape packet1097.row = true := by
  decide +kernel

private theorem packet1097_cache : checkStripCache packet1097 = true := by
  decide +kernel

private theorem packet1097_pair (i : Fin 7) : checkEdgePair packet1097 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1097_ok : checkStripPacket packet1097 = true :=
  checkStripPacket_intro packet1097_shape packet1097_cache packet1097_pair

theorem packet1098_membership : packet1098 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1098_shape : checkStripShape packet1098.row = true := by
  decide +kernel

private theorem packet1098_cache : checkStripCache packet1098 = true := by
  decide +kernel

private theorem packet1098_pair (i : Fin 7) : checkEdgePair packet1098 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1098_ok : checkStripPacket packet1098 = true :=
  checkStripPacket_intro packet1098_shape packet1098_cache packet1098_pair

theorem packet1099_membership : packet1099 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1099_shape : checkStripShape packet1099.row = true := by
  decide +kernel

private theorem packet1099_cache : checkStripCache packet1099 = true := by
  decide +kernel

private theorem packet1099_pair (i : Fin 7) : checkEdgePair packet1099 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1099_ok : checkStripPacket packet1099 = true :=
  checkStripPacket_intro packet1099_shape packet1099_cache packet1099_pair

theorem packet1100_membership : packet1100 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1100_shape : checkStripShape packet1100.row = true := by
  decide +kernel

private theorem packet1100_cache : checkStripCache packet1100 = true := by
  decide +kernel

private theorem packet1100_pair (i : Fin 7) : checkEdgePair packet1100 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1100_ok : checkStripPacket packet1100 = true :=
  checkStripPacket_intro packet1100_shape packet1100_cache packet1100_pair

theorem packet1101_membership : packet1101 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1101_shape : checkStripShape packet1101.row = true := by
  decide +kernel

private theorem packet1101_cache : checkStripCache packet1101 = true := by
  decide +kernel

private theorem packet1101_pair (i : Fin 7) : checkEdgePair packet1101 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1101_ok : checkStripPacket packet1101 = true :=
  checkStripPacket_intro packet1101_shape packet1101_cache packet1101_pair

theorem packet1102_membership : packet1102 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1102_shape : checkStripShape packet1102.row = true := by
  decide +kernel

private theorem packet1102_cache : checkStripCache packet1102 = true := by
  decide +kernel

private theorem packet1102_pair (i : Fin 7) : checkEdgePair packet1102 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1102_ok : checkStripPacket packet1102 = true :=
  checkStripPacket_intro packet1102_shape packet1102_cache packet1102_pair

theorem packet1103_membership : packet1103 ∈ packets045 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1103_shape : checkStripShape packet1103.row = true := by
  decide +kernel

private theorem packet1103_cache : checkStripCache packet1103 = true := by
  decide +kernel

private theorem packet1103_pair (i : Fin 7) : checkEdgePair packet1103 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1103_ok : checkStripPacket packet1103 = true :=
  checkStripPacket_intro packet1103_shape packet1103_cache packet1103_pair

theorem packets045_checked : packets045.all checkStripPacket = true := by
  simp only [packets045, List.all_cons, List.all_nil, Bool.true_and, packet1080_ok,
    packet1081_ok, packet1082_ok, packet1083_ok, packet1084_ok, packet1085_ok,
    packet1086_ok, packet1087_ok, packet1088_ok, packet1089_ok, packet1090_ok,
    packet1091_ok, packet1092_ok, packet1093_ok, packet1094_ok, packet1095_ok,
    packet1096_ok, packet1097_ok, packet1098_ok, packet1099_ok, packet1100_ok,
    packet1101_ok, packet1102_ok, packet1103_ok]

theorem packets045_valid : packets045.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
