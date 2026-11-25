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

def packet1104 : StripRowPacket :=
  ⟨⟨⟨6,52,5,23⟩,
    ![449,1438,2810,4355,5842,7060,7859],![456,1456,2841,4397,5891,7105,7885]⟩,
    ⟨1773064301273292762661895,190200442125880626090348544⟩,
    ⟨796359019910581216943125,73279106024862076305860608⟩⟩

def packet1105 : StripRowPacket :=
  ⟨⟨⟨6,53,5,22⟩,
    ![444,1425,2786,4322,5804,7027,7843],![452,1444,2818,4365,5853,7070,7866]⟩,
    ⟨566684661274157860031119513,70409112767299701753500606464⟩,
    ⟨200395637084913551940627107,20863792326258018900013588480⟩⟩

def packet1106 : StripRowPacket :=
  ⟨⟨⟨6,53,5,23⟩,
    ![448,1437,2808,4353,5840,7059,7859],![456,1454,2838,4395,5889,7104,7885]⟩,
    ⟨6625409737384995891331022609,704091127672997017535006064640⟩,
    ⟨28600359438297546696660367,2607974040782252362501698560⟩⟩

def packet1107 : StripRowPacket :=
  ⟨⟨⟨6,54,5,20⟩,
    ![435,1397,2736,4253,5730,6968,7817],![444,1418,2770,4298,5778,7006,7835]⟩,
    ⟨68028730393739702686368455,12652544768733391787702474752⟩,
    ⟨60184901595186949744303302003,8667050379599107374794684088320⟩⟩

def packet1108 : StripRowPacket :=
  ⟨⟨⟨6,54,5,21⟩,
    ![440,1411,2761,4287,5766,6996,7829],![448,1430,2794,4331,5814,7036,7849]⟩,
    ⟨1708145821314504110825031347,253050895374667835754049495040⟩,
    ⟨7209048562577714047668554057,866705037959910737479468408832⟩⟩

def packet1109 : StripRowPacket :=
  ⟨⟨⟨6,55,5,20⟩,
    ![435,1396,2734,4251,5728,6967,7817],![443,1417,2768,4296,5776,7005,7835]⟩,
    ⟨186007660915669630669691,34271255956813622671175680⟩,
    ⟨1027835123306221378214591,146705613775355160676367360⟩⟩

def packet1110 : StripRowPacket :=
  ⟨⟨⟨6,55,5,21⟩,
    ![439,1410,2759,4285,5764,6995,7829],![448,1429,2792,4329,5813,7035,7849]⟩,
    ⟨933971729989906234087787,137085023827254490684702720⟩,
    ⟨615563180985141643821561,73352806887677580338183680⟩⟩

def packet1111 : StripRowPacket :=
  ⟨⟨⟨6,54,5,22⟩,
    ![444,1424,2784,4319,5802,7026,7843],![452,1442,2816,4362,5851,7069,7865]⟩,
    ⟨1027858517377107083961346797,126525447687333917877024747520⟩,
    ⟨83996069656367331209067779137,8667050379599107374794684088320⟩⟩

def packet1112 : StripRowPacket :=
  ⟨⟨⟨6,54,5,23⟩,
    ![448,1435,2806,4351,5839,7058,7859],![455,1453,2836,4392,5887,7103,7884]⟩,
    ⟨2403288248193924225020355841,253050895374667835754049495040⟩,
    ⟨11987706710869690242681252213,1083381297449888421849335511040⟩⟩

def packet1113 : StripRowPacket :=
  ⟨⟨⟨6,55,5,22⟩,
    ![443,1422,2782,4317,5801,7025,7843],![451,1441,2814,4360,5849,7068,7865]⟩,
    ⟨8645483202439491888437,1054500183286573005266944⟩,
    ⟨1434417600634345197071653,146705613775355160676367360⟩⟩

def packet1114 : StripRowPacket :=
  ⟨⟨⟨6,55,5,23⟩,
    ![447,1434,2804,4349,5837,7057,7858],![455,1451,2834,4390,5886,7102,7884]⟩,
    ⟨119441263876760150627803,12462274893386771880427520⟩,
    ⟨204713604912300888312523,18338201721919395084545920⟩⟩

def packet1115 : StripRowPacket :=
  ⟨⟨⟨6,48,4,12⟩,
    ![454,1455,2840,4395,5885,7097,7878],![465,1482,2887,4462,5968,7181,7934]⟩,
    ⟨161465099264191951369,15727355656297875715840⟩,
    ⟨112719781539357633155357,8626335389619516012421120⟩⟩

def packet1116 : StripRowPacket :=
  ⟨⟨⟨6,49,4,12⟩,
    ![454,1454,2838,4392,5883,7096,7878],![464,1480,2885,4460,5966,7180,7933]⟩,
    ⟨209782673081384860848274229,20232685512879870157264783360⟩,
    ⟨981365686030476932038147841,74387042085222389413707182080⟩⟩

def packet1117 : StripRowPacket :=
  ⟨⟨⟨5,24,4,13⟩,
    ![459,1472,2873,4445,5949,7163,7920],![470,1499,2922,4515,6037,7261,8004]⟩,
    ⟨127683204060013897,9952054169949237632⟩,
    ⟨33332658457954369199,2104014791004308289536⟩⟩

def packet1118 : StripRowPacket :=
  ⟨⟨⟨6,50,4,12⟩,
    ![453,1452,2835,4390,5882,7095,7878],![464,1478,2882,4458,5965,7179,7933]⟩,
    ⟨16595093159906143213970907,1585019558640469467082378240⟩,
    ⟨93342216638585423166606701,7008817629307622759777935360⟩⟩

def packet1119 : StripRowPacket :=
  ⟨⟨⟨6,51,4,12⟩,
    ![453,1451,2833,4388,5880,7094,7877],![463,1477,2880,4455,5963,7178,7933]⟩,
    ⟨584007123841829679947429,55246670013575675680348160⟩,
    ⟨12723231540614556191690123,946503877975244849825044480⟩⟩

def packet1120 : StripRowPacket :=
  ⟨⟨⟨5,25,4,13⟩,
    ![458,1469,2868,4440,5946,7161,7920],![469,1496,2917,4510,6034,7259,8004]⟩,
    ⟨16285441826215644284869,1244764818108185285390336⟩,
    ⟨16203753541881573463237,1003885205109552056800256⟩⟩

def packet1121 : StripRowPacket :=
  ⟨⟨⟨5,24,4,14⟩,
    ![465,1489,2905,4495,6014,7236,7981],![475,1514,2950,4559,6096,7331,8095]⟩,
    ⟨998923479367515305,64688352104670044608⟩,
    ⟨77660116671595416951,4208029582008616579072⟩⟩

def packet1122 : StripRowPacket :=
  ⟨⟨⟨5,24,4,15⟩,
    ![469,1504,2934,4539,6073,7307,8063],![479,1527,2974,4597,6146,7393,8192]⟩,
    ⟨212346569517261869,11761518564485462656⟩,
    ⟨4069448268833,193157462527744⟩⟩

def packet1123 : StripRowPacket :=
  ⟨⟨⟨5,25,4,14⟩,
    ![464,1486,2901,4490,6011,7235,7981],![474,1510,2945,4553,6092,7329,8095]⟩,
    ⟨890842923830772064365,56580219004917512972288⟩,
    ⟨3435482869673792000746223,182707107329938474337646592⟩⟩

def packet1124 : StripRowPacket :=
  ⟨⟨⟨5,25,4,15⟩,
    ![468,1500,2929,4534,6070,7306,8064],![478,1523,2969,4591,6143,7391,8192]⟩,
    ⟨22911646822338326547191,1244764818108185285390336⟩,
    ⟨618982568717,28836282547072⟩⟩

def packet1125 : StripRowPacket :=
  ⟨⟨⟨6,52,4,12⟩,
    ![452,1449,2831,4385,5878,7093,7877],![462,1475,2878,4453,5961,7178,7933]⟩,
    ⟨3298252477944988278371551,309075718454556017396816384⟩,
    ⟨3976496497721725150215899,293116424099448305223442432⟩⟩

def packet1126 : StripRowPacket :=
  ⟨⟨⟨6,53,4,12⟩,
    ![451,1448,2829,4383,5877,7093,7877],![462,1474,2875,4450,5959,7177,7932]⟩,
    ⟨947996607753551647793856261,88011390959124627191875758080⟩,
    ⟨142808676174657008419297297,10431896163129009450006794240⟩⟩

def packet1127 : StripRowPacket :=
  ⟨⟨⟨5,26,4,13⟩,
    ![457,1466,2864,4436,5943,7160,7920],![468,1493,2912,4505,6030,7257,8003]⟩,
    ⟨425140195362551630326571,31884217861213170263050240⟩,
    ⟨1171518034621699325439,71273942378855894312960⟩⟩

def packets046 : List StripRowPacket :=
  [packet1104, packet1105, packet1106, packet1107, packet1108, packet1109,
   packet1110, packet1111, packet1112, packet1113, packet1114, packet1115,
   packet1116, packet1117, packet1118, packet1119, packet1120, packet1121,
   packet1122, packet1123, packet1124, packet1125, packet1126, packet1127]

theorem packet1104_membership : packet1104 ∈ packets046 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1104_shape : checkStripShape packet1104.row = true := by
  decide +kernel

private theorem packet1104_cache : checkStripCache packet1104 = true := by
  decide +kernel

private theorem packet1104_pair (i : Fin 7) : checkEdgePair packet1104 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1104_ok : checkStripPacket packet1104 = true :=
  checkStripPacket_intro packet1104_shape packet1104_cache packet1104_pair

theorem packet1105_membership : packet1105 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1105_shape : checkStripShape packet1105.row = true := by
  decide +kernel

private theorem packet1105_cache : checkStripCache packet1105 = true := by
  decide +kernel

private theorem packet1105_pair (i : Fin 7) : checkEdgePair packet1105 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1105_ok : checkStripPacket packet1105 = true :=
  checkStripPacket_intro packet1105_shape packet1105_cache packet1105_pair

theorem packet1106_membership : packet1106 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1106_shape : checkStripShape packet1106.row = true := by
  decide +kernel

private theorem packet1106_cache : checkStripCache packet1106 = true := by
  decide +kernel

private theorem packet1106_pair (i : Fin 7) : checkEdgePair packet1106 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1106_ok : checkStripPacket packet1106 = true :=
  checkStripPacket_intro packet1106_shape packet1106_cache packet1106_pair

theorem packet1107_membership : packet1107 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1107_shape : checkStripShape packet1107.row = true := by
  decide +kernel

private theorem packet1107_cache : checkStripCache packet1107 = true := by
  decide +kernel

private theorem packet1107_pair (i : Fin 7) : checkEdgePair packet1107 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1107_ok : checkStripPacket packet1107 = true :=
  checkStripPacket_intro packet1107_shape packet1107_cache packet1107_pair

theorem packet1108_membership : packet1108 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1108_shape : checkStripShape packet1108.row = true := by
  decide +kernel

private theorem packet1108_cache : checkStripCache packet1108 = true := by
  decide +kernel

private theorem packet1108_pair (i : Fin 7) : checkEdgePair packet1108 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1108_ok : checkStripPacket packet1108 = true :=
  checkStripPacket_intro packet1108_shape packet1108_cache packet1108_pair

theorem packet1109_membership : packet1109 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1109_shape : checkStripShape packet1109.row = true := by
  decide +kernel

private theorem packet1109_cache : checkStripCache packet1109 = true := by
  decide +kernel

private theorem packet1109_pair (i : Fin 7) : checkEdgePair packet1109 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1109_ok : checkStripPacket packet1109 = true :=
  checkStripPacket_intro packet1109_shape packet1109_cache packet1109_pair

theorem packet1110_membership : packet1110 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1110_shape : checkStripShape packet1110.row = true := by
  decide +kernel

private theorem packet1110_cache : checkStripCache packet1110 = true := by
  decide +kernel

private theorem packet1110_pair (i : Fin 7) : checkEdgePair packet1110 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1110_ok : checkStripPacket packet1110 = true :=
  checkStripPacket_intro packet1110_shape packet1110_cache packet1110_pair

theorem packet1111_membership : packet1111 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1111_shape : checkStripShape packet1111.row = true := by
  decide +kernel

private theorem packet1111_cache : checkStripCache packet1111 = true := by
  decide +kernel

private theorem packet1111_pair (i : Fin 7) : checkEdgePair packet1111 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1111_ok : checkStripPacket packet1111 = true :=
  checkStripPacket_intro packet1111_shape packet1111_cache packet1111_pair

theorem packet1112_membership : packet1112 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1112_shape : checkStripShape packet1112.row = true := by
  decide +kernel

private theorem packet1112_cache : checkStripCache packet1112 = true := by
  decide +kernel

private theorem packet1112_pair (i : Fin 7) : checkEdgePair packet1112 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1112_ok : checkStripPacket packet1112 = true :=
  checkStripPacket_intro packet1112_shape packet1112_cache packet1112_pair

theorem packet1113_membership : packet1113 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1113_shape : checkStripShape packet1113.row = true := by
  decide +kernel

private theorem packet1113_cache : checkStripCache packet1113 = true := by
  decide +kernel

private theorem packet1113_pair (i : Fin 7) : checkEdgePair packet1113 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1113_ok : checkStripPacket packet1113 = true :=
  checkStripPacket_intro packet1113_shape packet1113_cache packet1113_pair

theorem packet1114_membership : packet1114 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1114_shape : checkStripShape packet1114.row = true := by
  decide +kernel

private theorem packet1114_cache : checkStripCache packet1114 = true := by
  decide +kernel

private theorem packet1114_pair (i : Fin 7) : checkEdgePair packet1114 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1114_ok : checkStripPacket packet1114 = true :=
  checkStripPacket_intro packet1114_shape packet1114_cache packet1114_pair

theorem packet1115_membership : packet1115 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1115_shape : checkStripShape packet1115.row = true := by
  decide +kernel

private theorem packet1115_cache : checkStripCache packet1115 = true := by
  decide +kernel

private theorem packet1115_pair (i : Fin 7) : checkEdgePair packet1115 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1115_ok : checkStripPacket packet1115 = true :=
  checkStripPacket_intro packet1115_shape packet1115_cache packet1115_pair

theorem packet1116_membership : packet1116 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1116_shape : checkStripShape packet1116.row = true := by
  decide +kernel

private theorem packet1116_cache : checkStripCache packet1116 = true := by
  decide +kernel

private theorem packet1116_pair (i : Fin 7) : checkEdgePair packet1116 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1116_ok : checkStripPacket packet1116 = true :=
  checkStripPacket_intro packet1116_shape packet1116_cache packet1116_pair

theorem packet1117_membership : packet1117 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1117_shape : checkStripShape packet1117.row = true := by
  decide +kernel

private theorem packet1117_cache : checkStripCache packet1117 = true := by
  decide +kernel

private theorem packet1117_pair (i : Fin 7) : checkEdgePair packet1117 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1117_ok : checkStripPacket packet1117 = true :=
  checkStripPacket_intro packet1117_shape packet1117_cache packet1117_pair

theorem packet1118_membership : packet1118 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1118_shape : checkStripShape packet1118.row = true := by
  decide +kernel

private theorem packet1118_cache : checkStripCache packet1118 = true := by
  decide +kernel

private theorem packet1118_pair (i : Fin 7) : checkEdgePair packet1118 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1118_ok : checkStripPacket packet1118 = true :=
  checkStripPacket_intro packet1118_shape packet1118_cache packet1118_pair

theorem packet1119_membership : packet1119 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1119_shape : checkStripShape packet1119.row = true := by
  decide +kernel

private theorem packet1119_cache : checkStripCache packet1119 = true := by
  decide +kernel

private theorem packet1119_pair (i : Fin 7) : checkEdgePair packet1119 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1119_ok : checkStripPacket packet1119 = true :=
  checkStripPacket_intro packet1119_shape packet1119_cache packet1119_pair

theorem packet1120_membership : packet1120 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1120_shape : checkStripShape packet1120.row = true := by
  decide +kernel

private theorem packet1120_cache : checkStripCache packet1120 = true := by
  decide +kernel

private theorem packet1120_pair (i : Fin 7) : checkEdgePair packet1120 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1120_ok : checkStripPacket packet1120 = true :=
  checkStripPacket_intro packet1120_shape packet1120_cache packet1120_pair

theorem packet1121_membership : packet1121 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1121_shape : checkStripShape packet1121.row = true := by
  decide +kernel

private theorem packet1121_cache : checkStripCache packet1121 = true := by
  decide +kernel

private theorem packet1121_pair (i : Fin 7) : checkEdgePair packet1121 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1121_ok : checkStripPacket packet1121 = true :=
  checkStripPacket_intro packet1121_shape packet1121_cache packet1121_pair

theorem packet1122_membership : packet1122 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1122_shape : checkStripShape packet1122.row = true := by
  decide +kernel

private theorem packet1122_cache : checkStripCache packet1122 = true := by
  decide +kernel

private theorem packet1122_pair (i : Fin 7) : checkEdgePair packet1122 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1122_ok : checkStripPacket packet1122 = true :=
  checkStripPacket_intro packet1122_shape packet1122_cache packet1122_pair

theorem packet1123_membership : packet1123 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1123_shape : checkStripShape packet1123.row = true := by
  decide +kernel

private theorem packet1123_cache : checkStripCache packet1123 = true := by
  decide +kernel

private theorem packet1123_pair (i : Fin 7) : checkEdgePair packet1123 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1123_ok : checkStripPacket packet1123 = true :=
  checkStripPacket_intro packet1123_shape packet1123_cache packet1123_pair

theorem packet1124_membership : packet1124 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1124_shape : checkStripShape packet1124.row = true := by
  decide +kernel

private theorem packet1124_cache : checkStripCache packet1124 = true := by
  decide +kernel

private theorem packet1124_pair (i : Fin 7) : checkEdgePair packet1124 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1124_ok : checkStripPacket packet1124 = true :=
  checkStripPacket_intro packet1124_shape packet1124_cache packet1124_pair

theorem packet1125_membership : packet1125 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1125_shape : checkStripShape packet1125.row = true := by
  decide +kernel

private theorem packet1125_cache : checkStripCache packet1125 = true := by
  decide +kernel

private theorem packet1125_pair (i : Fin 7) : checkEdgePair packet1125 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1125_ok : checkStripPacket packet1125 = true :=
  checkStripPacket_intro packet1125_shape packet1125_cache packet1125_pair

theorem packet1126_membership : packet1126 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1126_shape : checkStripShape packet1126.row = true := by
  decide +kernel

private theorem packet1126_cache : checkStripCache packet1126 = true := by
  decide +kernel

private theorem packet1126_pair (i : Fin 7) : checkEdgePair packet1126 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1126_ok : checkStripPacket packet1126 = true :=
  checkStripPacket_intro packet1126_shape packet1126_cache packet1126_pair

theorem packet1127_membership : packet1127 ∈ packets046 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1127_shape : checkStripShape packet1127.row = true := by
  decide +kernel

private theorem packet1127_cache : checkStripCache packet1127 = true := by
  decide +kernel

private theorem packet1127_pair (i : Fin 7) : checkEdgePair packet1127 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1127_ok : checkStripPacket packet1127 = true :=
  checkStripPacket_intro packet1127_shape packet1127_cache packet1127_pair

theorem packets046_checked : packets046.all checkStripPacket = true := by
  simp only [packets046, List.all_cons, List.all_nil, Bool.true_and, packet1104_ok,
    packet1105_ok, packet1106_ok, packet1107_ok, packet1108_ok, packet1109_ok,
    packet1110_ok, packet1111_ok, packet1112_ok, packet1113_ok, packet1114_ok,
    packet1115_ok, packet1116_ok, packet1117_ok, packet1118_ok, packet1119_ok,
    packet1120_ok, packet1121_ok, packet1122_ok, packet1123_ok, packet1124_ok,
    packet1125_ok, packet1126_ok, packet1127_ok]

theorem packets046_valid : packets046.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
