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

def packet1056 : StripRowPacket :=
  ⟨⟨⟨5,31,4,5⟩,
    ![345,1164,2394,3882,5417,6774,7749],![378,1234,2480,3961,5476,6808,7761]⟩,
    ⟨-4589644171970049,508041928958586880⟩,
    ⟨-43233893804903,7566689081219840⟩⟩

def packet1057 : StripRowPacket :=
  ⟨⟨⟨5,30,4,6⟩,
    ![373,1226,2470,3952,5468,6802,7758],![399,1287,2554,4036,5534,6841,7773]⟩,
    ⟨-88741918631795162071879,14795799524121628336749568⟩,
    ⟨-2773606803056620176797423,1019396223114756880215240704⟩⟩

def packet1058 : StripRowPacket :=
  ⟨⟨⟨5,30,4,7⟩,
    ![393,1277,2540,4021,5521,6832,7768],![414,1331,2621,4110,5596,6878,7785]⟩,
    ⟨-91619383400508223837787,29591599048243256673499136⟩,
    ⟨23110145669748541420615,127424527889344610026905088⟩⟩

def packet1059 : StripRowPacket :=
  ⟨⟨⟨5,31,4,6⟩,
    ![372,1224,2467,3948,5465,6800,7757],![398,1285,2551,4033,5531,6839,7772]⟩,
    ⟨-309170928823931,50804192895858688⟩,
    ⟨-41839550280787,15133378162439680⟩⟩

def packet1060 : StripRowPacket :=
  ⟨⟨⟨5,31,4,7⟩,
    ![392,1275,2537,4018,5518,6830,7767],![414,1328,2617,4106,5592,6876,7785]⟩,
    ⟨-1593774404508571,508041928958586880⟩,
    ⟨348585881029,1891672270304960⟩⟩

def packet1061 : StripRowPacket :=
  ⟨⟨⟨6,48,4,8⟩,
    ![415,1337,2633,4123,5606,6883,7785],![432,1382,2704,4207,5682,6933,7805]⟩,
    ⟨-1050444227006273091,7863677828148937857920⟩,
    ⟨22995462318112197995481,8626335389619516012421120⟩⟩

def packet1062 : StripRowPacket :=
  ⟨⟨⟨6,49,4,8⟩,
    ![414,1336,2630,4121,5604,6882,7785],![432,1380,2702,4205,5680,6932,7805]⟩,
    ⟨-1323589120907980967279417,10116342756439935078632391680⟩,
    ⟨200268147396734470809805549,74387042085222389413707182080⟩⟩

def packet1063 : StripRowPacket :=
  ⟨⟨⟨6,48,5,18⟩,
    ![428,1374,2694,4195,5671,6925,7800],![438,1398,2732,4243,5716,6957,7814]⟩,
    ⟨155162433902154312823,62909422625191502863360⟩,
    ⟨68422004441535754780931,17252670779239032024842240⟩⟩

def packet1064 : StripRowPacket :=
  ⟨⟨⟨6,48,5,19⟩,
    ![433,1391,2722,4231,5705,6948,7809],![443,1413,2759,4278,5752,6983,7825]⟩,
    ⟨473890855522513123197,125818845250383005726720⟩,
    ⟨4542654212342355678545,862633538961951601242112⟩⟩

def packet1065 : StripRowPacket :=
  ⟨⟨⟨6,49,5,18⟩,
    ![427,1373,2691,4193,5669,6924,7800],![437,1396,2730,4240,5715,6956,7814]⟩,
    ⟨201841138355936975044597727,80930742051519480629059133440⟩,
    ⟨595810679451904556926696671,148774084170444778827414364160⟩⟩

def packet1066 : StripRowPacket :=
  ⟨⟨⟨6,49,5,19⟩,
    ![433,1389,2720,4229,5703,6947,7809],![442,1411,2756,4276,5750,6982,7824]⟩,
    ⟨616112128035074772872028517,161861484103038961258118266880⟩,
    ⟨197771266027585043058445561,37193521042611194706853591040⟩⟩

def packet1067 : StripRowPacket :=
  ⟨⟨⟨6,50,4,8⟩,
    ![414,1334,2628,4118,5602,6881,7784],![431,1379,2699,4202,5678,6931,7804]⟩,
    ⟨-101530968839185277329183,792509779320234733541189120⟩,
    ⟨19054477933141899258267113,7008817629307622759777935360⟩⟩

def packet1068 : StripRowPacket :=
  ⟨⟨⟨6,51,4,8⟩,
    ![413,1333,2626,4116,5600,6879,7784],![431,1377,2697,4200,5676,6929,7804]⟩,
    ⟨-266479876459923503469,2124871923599064449244160⟩,
    ⟨2598084435156642715955247,946503877975244849825044480⟩⟩

def packet1069 : StripRowPacket :=
  ⟨⟨⟨6,50,5,18⟩,
    ![427,1371,2689,4191,5667,6923,7799],![437,1395,2728,4238,5713,6955,7813]⟩,
    ⟨15985907346871031549995809,6340078234561877868329512960⟩,
    ⟨1828415823956279983665133,452181782535975661921157120⟩⟩

def packet1070 : StripRowPacket :=
  ⟨⟨⟨6,50,5,19⟩,
    ![432,1388,2718,4226,5702,6946,7808],![442,1410,2754,4273,5748,6981,7824]⟩,
    ⟨48769969791326576868620891,12680156469123755736659025920⟩,
    ⟨3762641260950278023535201,700881762930762275977793536⟩⟩

def packet1071 : StripRowPacket :=
  ⟨⟨⟨6,51,5,18⟩,
    ![426,1370,2687,4189,5665,6922,7799],![436,1393,2725,4236,5711,6954,7813]⟩,
    ⟨563221693477955646676847,220986680054302702721392640⟩,
    ⟨7727455646677763800844213,1893007755950489699650088960⟩⟩

def packet1072 : StripRowPacket :=
  ⟨⟨⟨6,51,5,19⟩,
    ![432,1386,2715,4224,5700,6945,7808],![441,1408,2752,4271,5747,6980,7824]⟩,
    ⟨156125362507790816762847,40179396373509582312980480⟩,
    ⟨197283508135427734034191,36403995306740186531732480⟩⟩

def packet1073 : StripRowPacket :=
  ⟨⟨⟨6,48,5,20⟩,
    ![438,1406,2749,4266,5740,6974,7819],![447,1427,2784,4312,5789,7012,7837]⟩,
    ⟨159364210810179405187,31454711312595751431680⟩,
    ⟨113284164052158472360869,17252670779239032024842240⟩⟩

def packet1074 : StripRowPacket :=
  ⟨⟨⟨6,48,5,21⟩,
    ![443,1420,2774,4300,5776,7002,7831],![451,1440,2807,4345,5825,7042,7851]⟩,
    ⟨801022830958922118299,125818845250383005726720⟩,
    ⟨6168874720794083234129,784212308147228728401920⟩⟩

def packet1075 : StripRowPacket :=
  ⟨⟨⟨6,49,5,20⟩,
    ![438,1404,2746,4264,5739,6973,7819],![447,1425,2781,4310,5787,7011,7837]⟩,
    ⟨41427098967913779782743079,8093074205151948062905913344⟩,
    ⟨986359448768775787540867817,148774084170444778827414364160⟩⟩

def packet1076 : StripRowPacket :=
  ⟨⟨⟨6,49,5,21⟩,
    ![442,1418,2771,4298,5775,7001,7831],![451,1438,2805,4343,5823,7041,7851]⟩,
    ⟨1040971830681476418437694643,161861484103038961258118266880⟩,
    ⟨118163383342721140284795339,14877408417044477882741436416⟩⟩

def packet1077 : StripRowPacket :=
  ⟨⟨⟨6,48,4,11⟩,
    ![447,1432,2797,4333,5813,7032,7844],![459,1462,2850,4407,5898,7109,7886]⟩,
    ⟨96458881867712661585,12581884525038300572672⟩,
    ⟨22572175433511568591347,2156583847404879003105280⟩⟩

def packet1078 : StripRowPacket :=
  ⟨⟨⟨6,49,4,11⟩,
    ![446,1431,2795,4330,5811,7031,7844],![458,1461,2847,4404,5896,7108,7886]⟩,
    ⟨56972803727485329146387623,7357340186501770966278103040⟩,
    ⟨196522825343010329182765567,18596760521305597353426795520⟩⟩

def packet1079 : StripRowPacket :=
  ⟨⟨⟨6,50,5,20⟩,
    ![437,1403,2744,4261,5737,6972,7819],![446,1424,2779,4307,5785,7010,7836]⟩,
    ⟨16392031222227772659312541,3170039117280938934164756480⟩,
    ⟨93824759895366441447788917,14017635258615245519555870720⟩⟩

def packets044 : List StripRowPacket :=
  [packet1056, packet1057, packet1058, packet1059, packet1060, packet1061,
   packet1062, packet1063, packet1064, packet1065, packet1066, packet1067,
   packet1068, packet1069, packet1070, packet1071, packet1072, packet1073,
   packet1074, packet1075, packet1076, packet1077, packet1078, packet1079]

theorem packet1056_membership : packet1056 ∈ packets044 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1056_shape : checkStripShape packet1056.row = true := by
  decide +kernel

private theorem packet1056_cache : checkStripCache packet1056 = true := by
  decide +kernel

private theorem packet1056_pair (i : Fin 7) : checkEdgePair packet1056 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1056_ok : checkStripPacket packet1056 = true :=
  checkStripPacket_intro packet1056_shape packet1056_cache packet1056_pair

theorem packet1057_membership : packet1057 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1057_shape : checkStripShape packet1057.row = true := by
  decide +kernel

private theorem packet1057_cache : checkStripCache packet1057 = true := by
  decide +kernel

private theorem packet1057_pair (i : Fin 7) : checkEdgePair packet1057 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1057_ok : checkStripPacket packet1057 = true :=
  checkStripPacket_intro packet1057_shape packet1057_cache packet1057_pair

theorem packet1058_membership : packet1058 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1058_shape : checkStripShape packet1058.row = true := by
  decide +kernel

private theorem packet1058_cache : checkStripCache packet1058 = true := by
  decide +kernel

private theorem packet1058_pair (i : Fin 7) : checkEdgePair packet1058 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1058_ok : checkStripPacket packet1058 = true :=
  checkStripPacket_intro packet1058_shape packet1058_cache packet1058_pair

theorem packet1059_membership : packet1059 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1059_shape : checkStripShape packet1059.row = true := by
  decide +kernel

private theorem packet1059_cache : checkStripCache packet1059 = true := by
  decide +kernel

private theorem packet1059_pair (i : Fin 7) : checkEdgePair packet1059 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1059_ok : checkStripPacket packet1059 = true :=
  checkStripPacket_intro packet1059_shape packet1059_cache packet1059_pair

theorem packet1060_membership : packet1060 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1060_shape : checkStripShape packet1060.row = true := by
  decide +kernel

private theorem packet1060_cache : checkStripCache packet1060 = true := by
  decide +kernel

private theorem packet1060_pair (i : Fin 7) : checkEdgePair packet1060 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1060_ok : checkStripPacket packet1060 = true :=
  checkStripPacket_intro packet1060_shape packet1060_cache packet1060_pair

theorem packet1061_membership : packet1061 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1061_shape : checkStripShape packet1061.row = true := by
  decide +kernel

private theorem packet1061_cache : checkStripCache packet1061 = true := by
  decide +kernel

private theorem packet1061_pair (i : Fin 7) : checkEdgePair packet1061 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1061_ok : checkStripPacket packet1061 = true :=
  checkStripPacket_intro packet1061_shape packet1061_cache packet1061_pair

theorem packet1062_membership : packet1062 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1062_shape : checkStripShape packet1062.row = true := by
  decide +kernel

private theorem packet1062_cache : checkStripCache packet1062 = true := by
  decide +kernel

private theorem packet1062_pair (i : Fin 7) : checkEdgePair packet1062 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1062_ok : checkStripPacket packet1062 = true :=
  checkStripPacket_intro packet1062_shape packet1062_cache packet1062_pair

theorem packet1063_membership : packet1063 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1063_shape : checkStripShape packet1063.row = true := by
  decide +kernel

private theorem packet1063_cache : checkStripCache packet1063 = true := by
  decide +kernel

private theorem packet1063_pair (i : Fin 7) : checkEdgePair packet1063 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1063_ok : checkStripPacket packet1063 = true :=
  checkStripPacket_intro packet1063_shape packet1063_cache packet1063_pair

theorem packet1064_membership : packet1064 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1064_shape : checkStripShape packet1064.row = true := by
  decide +kernel

private theorem packet1064_cache : checkStripCache packet1064 = true := by
  decide +kernel

private theorem packet1064_pair (i : Fin 7) : checkEdgePair packet1064 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1064_ok : checkStripPacket packet1064 = true :=
  checkStripPacket_intro packet1064_shape packet1064_cache packet1064_pair

theorem packet1065_membership : packet1065 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1065_shape : checkStripShape packet1065.row = true := by
  decide +kernel

private theorem packet1065_cache : checkStripCache packet1065 = true := by
  decide +kernel

private theorem packet1065_pair (i : Fin 7) : checkEdgePair packet1065 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1065_ok : checkStripPacket packet1065 = true :=
  checkStripPacket_intro packet1065_shape packet1065_cache packet1065_pair

theorem packet1066_membership : packet1066 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1066_shape : checkStripShape packet1066.row = true := by
  decide +kernel

private theorem packet1066_cache : checkStripCache packet1066 = true := by
  decide +kernel

private theorem packet1066_pair (i : Fin 7) : checkEdgePair packet1066 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1066_ok : checkStripPacket packet1066 = true :=
  checkStripPacket_intro packet1066_shape packet1066_cache packet1066_pair

theorem packet1067_membership : packet1067 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1067_shape : checkStripShape packet1067.row = true := by
  decide +kernel

private theorem packet1067_cache : checkStripCache packet1067 = true := by
  decide +kernel

private theorem packet1067_pair (i : Fin 7) : checkEdgePair packet1067 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1067_ok : checkStripPacket packet1067 = true :=
  checkStripPacket_intro packet1067_shape packet1067_cache packet1067_pair

theorem packet1068_membership : packet1068 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1068_shape : checkStripShape packet1068.row = true := by
  decide +kernel

private theorem packet1068_cache : checkStripCache packet1068 = true := by
  decide +kernel

private theorem packet1068_pair (i : Fin 7) : checkEdgePair packet1068 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1068_ok : checkStripPacket packet1068 = true :=
  checkStripPacket_intro packet1068_shape packet1068_cache packet1068_pair

theorem packet1069_membership : packet1069 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1069_shape : checkStripShape packet1069.row = true := by
  decide +kernel

private theorem packet1069_cache : checkStripCache packet1069 = true := by
  decide +kernel

private theorem packet1069_pair (i : Fin 7) : checkEdgePair packet1069 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1069_ok : checkStripPacket packet1069 = true :=
  checkStripPacket_intro packet1069_shape packet1069_cache packet1069_pair

theorem packet1070_membership : packet1070 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1070_shape : checkStripShape packet1070.row = true := by
  decide +kernel

private theorem packet1070_cache : checkStripCache packet1070 = true := by
  decide +kernel

private theorem packet1070_pair (i : Fin 7) : checkEdgePair packet1070 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1070_ok : checkStripPacket packet1070 = true :=
  checkStripPacket_intro packet1070_shape packet1070_cache packet1070_pair

theorem packet1071_membership : packet1071 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1071_shape : checkStripShape packet1071.row = true := by
  decide +kernel

private theorem packet1071_cache : checkStripCache packet1071 = true := by
  decide +kernel

private theorem packet1071_pair (i : Fin 7) : checkEdgePair packet1071 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1071_ok : checkStripPacket packet1071 = true :=
  checkStripPacket_intro packet1071_shape packet1071_cache packet1071_pair

theorem packet1072_membership : packet1072 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1072_shape : checkStripShape packet1072.row = true := by
  decide +kernel

private theorem packet1072_cache : checkStripCache packet1072 = true := by
  decide +kernel

private theorem packet1072_pair (i : Fin 7) : checkEdgePair packet1072 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1072_ok : checkStripPacket packet1072 = true :=
  checkStripPacket_intro packet1072_shape packet1072_cache packet1072_pair

theorem packet1073_membership : packet1073 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1073_shape : checkStripShape packet1073.row = true := by
  decide +kernel

private theorem packet1073_cache : checkStripCache packet1073 = true := by
  decide +kernel

private theorem packet1073_pair (i : Fin 7) : checkEdgePair packet1073 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1073_ok : checkStripPacket packet1073 = true :=
  checkStripPacket_intro packet1073_shape packet1073_cache packet1073_pair

theorem packet1074_membership : packet1074 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1074_shape : checkStripShape packet1074.row = true := by
  decide +kernel

private theorem packet1074_cache : checkStripCache packet1074 = true := by
  decide +kernel

private theorem packet1074_pair (i : Fin 7) : checkEdgePair packet1074 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1074_ok : checkStripPacket packet1074 = true :=
  checkStripPacket_intro packet1074_shape packet1074_cache packet1074_pair

theorem packet1075_membership : packet1075 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1075_shape : checkStripShape packet1075.row = true := by
  decide +kernel

private theorem packet1075_cache : checkStripCache packet1075 = true := by
  decide +kernel

private theorem packet1075_pair (i : Fin 7) : checkEdgePair packet1075 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1075_ok : checkStripPacket packet1075 = true :=
  checkStripPacket_intro packet1075_shape packet1075_cache packet1075_pair

theorem packet1076_membership : packet1076 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1076_shape : checkStripShape packet1076.row = true := by
  decide +kernel

private theorem packet1076_cache : checkStripCache packet1076 = true := by
  decide +kernel

private theorem packet1076_pair (i : Fin 7) : checkEdgePair packet1076 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1076_ok : checkStripPacket packet1076 = true :=
  checkStripPacket_intro packet1076_shape packet1076_cache packet1076_pair

theorem packet1077_membership : packet1077 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1077_shape : checkStripShape packet1077.row = true := by
  decide +kernel

private theorem packet1077_cache : checkStripCache packet1077 = true := by
  decide +kernel

private theorem packet1077_pair (i : Fin 7) : checkEdgePair packet1077 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1077_ok : checkStripPacket packet1077 = true :=
  checkStripPacket_intro packet1077_shape packet1077_cache packet1077_pair

theorem packet1078_membership : packet1078 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1078_shape : checkStripShape packet1078.row = true := by
  decide +kernel

private theorem packet1078_cache : checkStripCache packet1078 = true := by
  decide +kernel

private theorem packet1078_pair (i : Fin 7) : checkEdgePair packet1078 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1078_ok : checkStripPacket packet1078 = true :=
  checkStripPacket_intro packet1078_shape packet1078_cache packet1078_pair

theorem packet1079_membership : packet1079 ∈ packets044 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1079_shape : checkStripShape packet1079.row = true := by
  decide +kernel

private theorem packet1079_cache : checkStripCache packet1079 = true := by
  decide +kernel

private theorem packet1079_pair (i : Fin 7) : checkEdgePair packet1079 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1079_ok : checkStripPacket packet1079 = true :=
  checkStripPacket_intro packet1079_shape packet1079_cache packet1079_pair

theorem packets044_checked : packets044.all checkStripPacket = true := by
  simp only [packets044, List.all_cons, List.all_nil, Bool.true_and, packet1056_ok,
    packet1057_ok, packet1058_ok, packet1059_ok, packet1060_ok, packet1061_ok,
    packet1062_ok, packet1063_ok, packet1064_ok, packet1065_ok, packet1066_ok,
    packet1067_ok, packet1068_ok, packet1069_ok, packet1070_ok, packet1071_ok,
    packet1072_ok, packet1073_ok, packet1074_ok, packet1075_ok, packet1076_ok,
    packet1077_ok, packet1078_ok, packet1079_ok]

theorem packets044_valid : packets044.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
