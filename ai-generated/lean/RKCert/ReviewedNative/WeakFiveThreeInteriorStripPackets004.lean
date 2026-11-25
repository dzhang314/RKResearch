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

def packet0096 : StripRowPacket :=
  ⟨⟨⟨8,4,6,11⟩,
    ![334,1251,2549,4052,5554,6854,7776],![371,1283,2576,4072,5569,6863,7780]⟩,
    ⟨-949308703089487990662975841831,165400291631312794749434335559680⟩,
    ⟨-3152627441840082509041418177,588875505488060348741115412480⟩⟩

def packet0097 : StripRowPacket :=
  ⟨⟨⟨8,5,6,10⟩,
    ![306,1226,2529,4037,5545,6850,7774],![346,1258,2555,4057,5559,6858,7779]⟩,
    ⟨-1225261254901717823931860540329,201786154456169414069731465953280⟩,
    ⟨-8250335420781508830716000181547,1450958070828439567023527350435840⟩⟩

def packet0098 : StripRowPacket :=
  ⟨⟨⟨8,5,6,11⟩,
    ![330,1245,2544,4048,5552,6853,7775],![366,1277,2571,4068,5566,6862,7780]⟩,
    ⟨-335181824780913793240536036193,57653186987476975448494704558080⟩,
    ⟨-1968716967409009648220712335971,362739517707109891755881837608960⟩⟩

def packet0099 : StripRowPacket :=
  ⟨⟨⟨8,6,6,8⟩,
    ![251,1184,2496,4013,5530,6842,7772],![297,1214,2520,4031,5543,6850,7776]⟩,
    ⟨-342083005009842336070354653,51252094357766744273864581120⟩,
    ⟨-70011100948882717160918501889933,11133076166518099094133789274013696⟩⟩

def packet0100 : StripRowPacket :=
  ⟨⟨⟨8,6,6,9⟩,
    ![278,1202,2510,4023,5536,6845,7773],![320,1233,2535,4042,5549,6853,7777]⟩,
    ⟨-2629010388665898687898401637,410016754862133954190916648960⟩,
    ⟨-12900671670194624551530494767889,2140976185868865210410344091156480⟩⟩

def packet0101 : StripRowPacket :=
  ⟨⟨⟨8,7,6,8⟩,
    ![249,1179,2491,4009,5527,6841,7771],![294,1208,2515,4027,5540,6849,7776]⟩,
    ⟨-12606657729845389414633817105,1865241740506761257683324485632⟩,
    ⟨-44757171970087318635541319,7024333952012097732992121856⟩⟩

def packet0102 : StripRowPacket :=
  ⟨⟨⟨8,7,6,9⟩,
    ![275,1197,2505,4019,5534,6844,7772],![317,1227,2530,4038,5547,6852,7777]⟩,
    ⟨-96874107539139933022687650457,14921933924054090061466595885056⟩,
    ⟨-21440736327907944670861421,3512166976006048866496060928⟩⟩

def packet0103 : StripRowPacket :=
  ⟨⟨⟨8,6,6,10⟩,
    ![303,1221,2524,4033,5543,6848,7774],![342,1252,2550,4053,5556,6857,7778]⟩,
    ⟨-252135673725305868723396605,41001675486213395419091664896⟩,
    ⟨-320779422105706890874993218480563,55665380832590495470668946370068480⟩⟩

def packet0104 : StripRowPacket :=
  ⟨⟨⟨8,6,6,11⟩,
    ![326,1239,2539,4044,5550,6852,7775],![362,1271,2566,4064,5564,6860,7780]⟩,
    ⟨-2413703085840218686569530463,410016754862133954190916648960⟩,
    ⟨-76535345196588385852548393249003,13916345208147623867667236592517120⟩⟩

def packet0105 : StripRowPacket :=
  ⟨⟨⟨8,7,6,10⟩,
    ![300,1215,2519,4029,5540,6847,7773],![338,1246,2545,4049,5554,6855,7778]⟩,
    ⟨-4222497874523488669468398367,678269723820640457339390722048⟩,
    ⟨-41005773341544460047904365,7024333952012097732992121856⟩⟩

def packet0106 : StripRowPacket :=
  ⟨⟨⟨8,7,6,11⟩,
    ![323,1234,2534,4040,5547,6851,7774],![358,1265,2561,4061,5561,6859,7779]⟩,
    ⟨-88915798939893568433921877691,14921933924054090061466595885056⟩,
    ⟨-38212962917258819095787,6859701125011814192375119⟩⟩

def packet0107 : StripRowPacket :=
  ⟨⟨⟨8,4,6,12⟩,
    ![356,1269,2564,4063,5562,6858,7777],![391,1302,2592,4084,5576,6867,7782]⟩,
    ⟨-226827410750210071781473514143,41350072907828198687358583889920⟩,
    ⟨-1091925817495441347699770669,214136547450203763178587422720⟩⟩

def packet0108 : StripRowPacket :=
  ⟨⟨⟨8,4,6,13⟩,
    ![378,1288,2580,4074,5569,6862,7778],![410,1322,2608,4096,5584,6871,7783]⟩,
    ⟨-865310582912192583588812271313,165400291631312794749434335559680⟩,
    ⟨-163026545964848280188989743,33650028885032019928063737856⟩⟩

def packet0109 : StripRowPacket :=
  ⟨⟨⟨8,5,6,12⟩,
    ![352,1264,2559,4059,5559,6857,7776],![386,1296,2587,4080,5574,6866,7781]⟩,
    ⟨-560505759282339364375945856511,100893077228084707034865732976640⟩,
    ⟨-681763665317324395913608955111,131905279166221778820320668221440⟩⟩

def packet0110 : StripRowPacket :=
  ⟨⟨⟨8,5,6,13⟩,
    ![373,1283,2575,4070,5566,6860,7777],![404,1315,2603,4092,5581,6870,7782]⟩,
    ⟨-194343027344756214756710418067,36688391719303529830860266536960⟩,
    ⟨-3561966383672549058608273834279,725479035414219783511763675217920⟩⟩

def packet0111 : StripRowPacket :=
  ⟨⟨⟨8,4,6,14⟩,
    ![397,1307,2596,4086,5576,6865,7779],![428,1341,2625,4109,5592,6875,7784]⟩,
    ⟨-411655761411772440025865243027,82700145815656397374717167779840⟩,
    ⟨-10812532442628904401761086661,2355502021952241394964461649920⟩⟩

def packet0112 : StripRowPacket :=
  ⟨⟨⟨8,4,6,15⟩,
    ![414,1326,2612,4098,5584,6869,7780],![445,1361,2642,4122,5600,6879,7785]⟩,
    ⟨-12020191734383033484840749243,2544619871250966073068220547072⟩,
    ⟨-638325416732401824393305707,147218876372015087185278853120⟩⟩

def packet0113 : StripRowPacket :=
  ⟨⟨⟨8,5,6,14⟩,
    ![392,1302,2591,4082,5574,6864,7779],![422,1335,2620,4105,5589,6874,7784]⟩,
    ⟨-203352356445527926714384577143,40357230891233882813946293190656⟩,
    ⟨-1349693043239925575876679366179,290191614165687913404705470087168⟩⟩

def packet0114 : StripRowPacket :=
  ⟨⟨⟨8,5,6,15⟩,
    ![409,1321,2607,4094,5582,6868,7780],![438,1354,2637,4118,5598,6878,7785]⟩,
    ⟨-1929273828118240171963876944123,403572308912338828139462931906560⟩,
    ⟨-398312354065884852596890374577,90684879426777472938970459402240⟩⟩

def packet0115 : StripRowPacket :=
  ⟨⟨⟨8,6,6,12⟩,
    ![348,1258,2554,4055,5557,6855,7776],![381,1290,2582,4076,5571,6864,7781]⟩,
    ⟨-576512358606844671476273719,102504188715533488547729162240⟩,
    ⟨-291503339467000195945393927511461,55665380832590495470668946370068480⟩⟩

def packet0116 : StripRowPacket :=
  ⟨⟨⟨8,6,6,13⟩,
    ![368,1277,2570,4067,5564,6859,7777],![399,1310,2598,4088,5579,6868,7782]⟩,
    ⟨-2198395783014538685240659289,410016754862133954190916648960⟩,
    ⟨-27686529814764684848059428202691,5566538083259049547066894637006848⟩⟩

def packet0117 : StripRowPacket :=
  ⟨⟨⟨8,7,6,12⟩,
    ![344,1253,2550,4052,5554,6854,7776],![377,1284,2577,4072,5569,6863,7780]⟩,
    ⟨-21234161160067596534884747827,3730483481013522515366648971264⟩,
    ⟨-37254374713001601460267411,7024333952012097732992121856⟩⟩

def packet0118 : StripRowPacket :=
  ⟨⟨⟨8,7,6,13⟩,
    ![364,1272,2565,4063,5562,6858,7777],![395,1304,2593,4085,5576,6867,7782]⟩,
    ⟨-80957490340647203845156104925,14921933924054090061466595885056⟩,
    ⟨-123701662233322280302269,24560608223818523541930496⟩⟩

def packet0119 : StripRowPacket :=
  ⟨⟨⟨8,6,6,14⟩,
    ![387,1296,2586,4079,5572,6863,7778],![417,1329,2615,4101,5587,6872,7783]⟩,
    ⟨-95033733254622667480737441,18637125221006088826859847680⟩,
    ⟨-37461036689756214430827805220337,7952197261798642210095563767152640⟩⟩

def packets004 : List StripRowPacket :=
  [packet0096, packet0097, packet0098, packet0099, packet0100, packet0101,
   packet0102, packet0103, packet0104, packet0105, packet0106, packet0107,
   packet0108, packet0109, packet0110, packet0111, packet0112, packet0113,
   packet0114, packet0115, packet0116, packet0117, packet0118, packet0119]

theorem packet0096_membership : packet0096 ∈ packets004 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0096_shape : checkStripShape packet0096.row = true := by
  decide +kernel

private theorem packet0096_cache : checkStripCache packet0096 = true := by
  decide +kernel

private theorem packet0096_pair (i : Fin 7) : checkEdgePair packet0096 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0096_ok : checkStripPacket packet0096 = true :=
  checkStripPacket_intro packet0096_shape packet0096_cache packet0096_pair

theorem packet0097_membership : packet0097 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0097_shape : checkStripShape packet0097.row = true := by
  decide +kernel

private theorem packet0097_cache : checkStripCache packet0097 = true := by
  decide +kernel

private theorem packet0097_pair (i : Fin 7) : checkEdgePair packet0097 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0097_ok : checkStripPacket packet0097 = true :=
  checkStripPacket_intro packet0097_shape packet0097_cache packet0097_pair

theorem packet0098_membership : packet0098 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0098_shape : checkStripShape packet0098.row = true := by
  decide +kernel

private theorem packet0098_cache : checkStripCache packet0098 = true := by
  decide +kernel

private theorem packet0098_pair (i : Fin 7) : checkEdgePair packet0098 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0098_ok : checkStripPacket packet0098 = true :=
  checkStripPacket_intro packet0098_shape packet0098_cache packet0098_pair

theorem packet0099_membership : packet0099 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0099_shape : checkStripShape packet0099.row = true := by
  decide +kernel

private theorem packet0099_cache : checkStripCache packet0099 = true := by
  decide +kernel

private theorem packet0099_pair (i : Fin 7) : checkEdgePair packet0099 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0099_ok : checkStripPacket packet0099 = true :=
  checkStripPacket_intro packet0099_shape packet0099_cache packet0099_pair

theorem packet0100_membership : packet0100 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0100_shape : checkStripShape packet0100.row = true := by
  decide +kernel

private theorem packet0100_cache : checkStripCache packet0100 = true := by
  decide +kernel

private theorem packet0100_pair (i : Fin 7) : checkEdgePair packet0100 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0100_ok : checkStripPacket packet0100 = true :=
  checkStripPacket_intro packet0100_shape packet0100_cache packet0100_pair

theorem packet0101_membership : packet0101 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0101_shape : checkStripShape packet0101.row = true := by
  decide +kernel

private theorem packet0101_cache : checkStripCache packet0101 = true := by
  decide +kernel

private theorem packet0101_pair (i : Fin 7) : checkEdgePair packet0101 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0101_ok : checkStripPacket packet0101 = true :=
  checkStripPacket_intro packet0101_shape packet0101_cache packet0101_pair

theorem packet0102_membership : packet0102 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0102_shape : checkStripShape packet0102.row = true := by
  decide +kernel

private theorem packet0102_cache : checkStripCache packet0102 = true := by
  decide +kernel

private theorem packet0102_pair (i : Fin 7) : checkEdgePair packet0102 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0102_ok : checkStripPacket packet0102 = true :=
  checkStripPacket_intro packet0102_shape packet0102_cache packet0102_pair

theorem packet0103_membership : packet0103 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0103_shape : checkStripShape packet0103.row = true := by
  decide +kernel

private theorem packet0103_cache : checkStripCache packet0103 = true := by
  decide +kernel

private theorem packet0103_pair (i : Fin 7) : checkEdgePair packet0103 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0103_ok : checkStripPacket packet0103 = true :=
  checkStripPacket_intro packet0103_shape packet0103_cache packet0103_pair

theorem packet0104_membership : packet0104 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0104_shape : checkStripShape packet0104.row = true := by
  decide +kernel

private theorem packet0104_cache : checkStripCache packet0104 = true := by
  decide +kernel

private theorem packet0104_pair (i : Fin 7) : checkEdgePair packet0104 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0104_ok : checkStripPacket packet0104 = true :=
  checkStripPacket_intro packet0104_shape packet0104_cache packet0104_pair

theorem packet0105_membership : packet0105 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0105_shape : checkStripShape packet0105.row = true := by
  decide +kernel

private theorem packet0105_cache : checkStripCache packet0105 = true := by
  decide +kernel

private theorem packet0105_pair (i : Fin 7) : checkEdgePair packet0105 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0105_ok : checkStripPacket packet0105 = true :=
  checkStripPacket_intro packet0105_shape packet0105_cache packet0105_pair

theorem packet0106_membership : packet0106 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0106_shape : checkStripShape packet0106.row = true := by
  decide +kernel

private theorem packet0106_cache : checkStripCache packet0106 = true := by
  decide +kernel

private theorem packet0106_pair (i : Fin 7) : checkEdgePair packet0106 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0106_ok : checkStripPacket packet0106 = true :=
  checkStripPacket_intro packet0106_shape packet0106_cache packet0106_pair

theorem packet0107_membership : packet0107 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0107_shape : checkStripShape packet0107.row = true := by
  decide +kernel

private theorem packet0107_cache : checkStripCache packet0107 = true := by
  decide +kernel

private theorem packet0107_pair (i : Fin 7) : checkEdgePair packet0107 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0107_ok : checkStripPacket packet0107 = true :=
  checkStripPacket_intro packet0107_shape packet0107_cache packet0107_pair

theorem packet0108_membership : packet0108 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0108_shape : checkStripShape packet0108.row = true := by
  decide +kernel

private theorem packet0108_cache : checkStripCache packet0108 = true := by
  decide +kernel

private theorem packet0108_pair (i : Fin 7) : checkEdgePair packet0108 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0108_ok : checkStripPacket packet0108 = true :=
  checkStripPacket_intro packet0108_shape packet0108_cache packet0108_pair

theorem packet0109_membership : packet0109 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0109_shape : checkStripShape packet0109.row = true := by
  decide +kernel

private theorem packet0109_cache : checkStripCache packet0109 = true := by
  decide +kernel

private theorem packet0109_pair (i : Fin 7) : checkEdgePair packet0109 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0109_ok : checkStripPacket packet0109 = true :=
  checkStripPacket_intro packet0109_shape packet0109_cache packet0109_pair

theorem packet0110_membership : packet0110 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0110_shape : checkStripShape packet0110.row = true := by
  decide +kernel

private theorem packet0110_cache : checkStripCache packet0110 = true := by
  decide +kernel

private theorem packet0110_pair (i : Fin 7) : checkEdgePair packet0110 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0110_ok : checkStripPacket packet0110 = true :=
  checkStripPacket_intro packet0110_shape packet0110_cache packet0110_pair

theorem packet0111_membership : packet0111 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0111_shape : checkStripShape packet0111.row = true := by
  decide +kernel

private theorem packet0111_cache : checkStripCache packet0111 = true := by
  decide +kernel

private theorem packet0111_pair (i : Fin 7) : checkEdgePair packet0111 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0111_ok : checkStripPacket packet0111 = true :=
  checkStripPacket_intro packet0111_shape packet0111_cache packet0111_pair

theorem packet0112_membership : packet0112 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0112_shape : checkStripShape packet0112.row = true := by
  decide +kernel

private theorem packet0112_cache : checkStripCache packet0112 = true := by
  decide +kernel

private theorem packet0112_pair (i : Fin 7) : checkEdgePair packet0112 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0112_ok : checkStripPacket packet0112 = true :=
  checkStripPacket_intro packet0112_shape packet0112_cache packet0112_pair

theorem packet0113_membership : packet0113 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0113_shape : checkStripShape packet0113.row = true := by
  decide +kernel

private theorem packet0113_cache : checkStripCache packet0113 = true := by
  decide +kernel

private theorem packet0113_pair (i : Fin 7) : checkEdgePair packet0113 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0113_ok : checkStripPacket packet0113 = true :=
  checkStripPacket_intro packet0113_shape packet0113_cache packet0113_pair

theorem packet0114_membership : packet0114 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0114_shape : checkStripShape packet0114.row = true := by
  decide +kernel

private theorem packet0114_cache : checkStripCache packet0114 = true := by
  decide +kernel

private theorem packet0114_pair (i : Fin 7) : checkEdgePair packet0114 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0114_ok : checkStripPacket packet0114 = true :=
  checkStripPacket_intro packet0114_shape packet0114_cache packet0114_pair

theorem packet0115_membership : packet0115 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0115_shape : checkStripShape packet0115.row = true := by
  decide +kernel

private theorem packet0115_cache : checkStripCache packet0115 = true := by
  decide +kernel

private theorem packet0115_pair (i : Fin 7) : checkEdgePair packet0115 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0115_ok : checkStripPacket packet0115 = true :=
  checkStripPacket_intro packet0115_shape packet0115_cache packet0115_pair

theorem packet0116_membership : packet0116 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0116_shape : checkStripShape packet0116.row = true := by
  decide +kernel

private theorem packet0116_cache : checkStripCache packet0116 = true := by
  decide +kernel

private theorem packet0116_pair (i : Fin 7) : checkEdgePair packet0116 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0116_ok : checkStripPacket packet0116 = true :=
  checkStripPacket_intro packet0116_shape packet0116_cache packet0116_pair

theorem packet0117_membership : packet0117 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0117_shape : checkStripShape packet0117.row = true := by
  decide +kernel

private theorem packet0117_cache : checkStripCache packet0117 = true := by
  decide +kernel

private theorem packet0117_pair (i : Fin 7) : checkEdgePair packet0117 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0117_ok : checkStripPacket packet0117 = true :=
  checkStripPacket_intro packet0117_shape packet0117_cache packet0117_pair

theorem packet0118_membership : packet0118 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0118_shape : checkStripShape packet0118.row = true := by
  decide +kernel

private theorem packet0118_cache : checkStripCache packet0118 = true := by
  decide +kernel

private theorem packet0118_pair (i : Fin 7) : checkEdgePair packet0118 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0118_ok : checkStripPacket packet0118 = true :=
  checkStripPacket_intro packet0118_shape packet0118_cache packet0118_pair

theorem packet0119_membership : packet0119 ∈ packets004 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0119_shape : checkStripShape packet0119.row = true := by
  decide +kernel

private theorem packet0119_cache : checkStripCache packet0119 = true := by
  decide +kernel

private theorem packet0119_pair (i : Fin 7) : checkEdgePair packet0119 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0119_ok : checkStripPacket packet0119 = true :=
  checkStripPacket_intro packet0119_shape packet0119_cache packet0119_pair

theorem packets004_checked : packets004.all checkStripPacket = true := by
  simp only [packets004, List.all_cons, List.all_nil, Bool.true_and, packet0096_ok,
    packet0097_ok, packet0098_ok, packet0099_ok, packet0100_ok, packet0101_ok,
    packet0102_ok, packet0103_ok, packet0104_ok, packet0105_ok, packet0106_ok,
    packet0107_ok, packet0108_ok, packet0109_ok, packet0110_ok, packet0111_ok,
    packet0112_ok, packet0113_ok, packet0114_ok, packet0115_ok, packet0116_ok,
    packet0117_ok, packet0118_ok, packet0119_ok]

theorem packets004_valid : packets004.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
