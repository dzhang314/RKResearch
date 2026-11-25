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

def packet0120 : StripRowPacket :=
  ⟨⟨⟨8,6,6,15⟩,
    ![404,1315,2602,4091,5580,6867,7780],![433,1348,2632,4114,5595,6877,7785]⟩,
    ⟨-30509053541367056675565971,6307950074802060833706409984⟩,
    ⟨-15474325969308759596937186941113,3479086302036905966916809148129280⟩⟩

def packet0121 : StripRowPacket :=
  ⟨⟨⟨8,7,6,14⟩,
    ![383,1291,2581,4075,5569,6862,7778],![412,1323,2610,4097,5585,6871,7783]⟩,
    ⟨-38489168020512010775386609271,7460966962027045030733297942528⟩,
    ⟨-33502976084458742872630457,7024333952012097732992121856⟩⟩

def packet0122 : StripRowPacket :=
  ⟨⟨⟨8,7,6,15⟩,
    ![400,1310,2598,4087,5577,6866,7779],![428,1342,2627,4110,5593,6875,7784]⟩,
    ⟨-72999181741400839256390332159,14921933924054090061466595885056⟩,
    ⟨-7906819192546828394702995,1756083488003024433248030464⟩⟩

def packet0123 : StripRowPacket :=
  ⟨⟨⟨8,8,5,0⟩,
    ![0,1048,2388,3935,5480,6817,7764],![89,1085,2419,3958,5496,6826,7769]⟩,
    ⟨-44551797288191901,4946575144311806720⟩,
    ⟨-423409976337794798734130663,50707219171520871440495083520⟩⟩

def packet0124 : StripRowPacket :=
  ⟨⟨⟨8,9,5,0⟩,
    ![0,1042,2383,3931,5478,6816,7764],![88,1079,2414,3954,5493,6825,7769]⟩,
    ⟨-281755399662877,30898274430438272⟩,
    ⟨-12765841201482708501004776278099,1509506747372340137293148841410560⟩⟩

def packet0125 : StripRowPacket :=
  ⟨⟨⟨8,8,5,1⟩,
    ![58,1075,2410,3951,5490,6822,7766],![155,1116,2443,3975,5507,6832,7771]⟩,
    ⟨-340896631600056625484539411,40269884395537454726287831040⟩,
    ⟨-2573539265372362930336960699,329596924614885664363218042880⟩⟩

def packet0126 : StripRowPacket :=
  ⟨⟨⟨8,9,5,1⟩,
    ![58,1070,2405,3947,5488,6821,7765],![153,1110,2438,3971,5504,6830,7770]⟩,
    ⟨-1489191855488432332139868083091,173772694784838669898059121623040⟩,
    ⟨-108510609003294106215590054405,13722788612475819429937716740096⟩⟩

def packet0127 : StripRowPacket :=
  ⟨⟨⟨8,10,5,0⟩,
    ![0,1037,2378,3927,5475,6814,7763],![87,1074,2409,3950,5491,6824,7768]⟩,
    ⟨-648238350078993731,70240576602582214400⟩,
    ⟨-22042321456294464751372865754669,2574529806748077066002418778439680⟩⟩

def packet0128 : StripRowPacket :=
  ⟨⟨⟨8,11,5,0⟩,
    ![0,1031,2374,3923,5473,6813,7763],![86,1069,2404,3946,5489,6822,7768]⟩,
    ⟨-41785590396267,4475365549493696⟩,
    ⟨-677820776062454609566556081,78230509236984290561160396800⟩⟩

def packet0129 : StripRowPacket :=
  ⟨⟨⟨8,10,5,1⟩,
    ![58,1065,2400,3943,5485,6819,7765],![152,1105,2433,3967,5502,6829,7770]⟩,
    ⟨-16898873329597030748085852470789,1948614054400972821842838897459200⟩,
    ⟨-10304001307100217549763837309229,1287264903374038533001209389219840⟩⟩

def packet0130 : StripRowPacket :=
  ⟨⟨⟨8,11,5,1⟩,
    ![58,1060,2396,3939,5483,6818,7764],![150,1100,2428,3964,5500,6828,7769]⟩,
    ⟨-6542802667748952821649374993149,745799706660290370534961516052480⟩,
    ⟨-9061416234865165064382798259,1118696282088875355024593674240⟩⟩

def packet0131 : StripRowPacket :=
  ⟨⟨⟨8,8,5,2⟩,
    ![128,1106,2434,3968,5501,6827,7767],![214,1149,2468,3993,5519,6838,7772]⟩,
    ⟨-31909873737814459244465519,4026988439553745472628783104⟩,
    ⟨-165166461003383425441522213,22730822387233494094015037440⟩⟩

def packet0132 : StripRowPacket :=
  ⟨⟨⟨8,9,5,2⟩,
    ![127,1100,2429,3964,5499,6826,7767],![212,1144,2463,3990,5516,6836,7772]⟩,
    ⟨-696892026903751146632973914771,86886347392419334949029560811520⟩,
    ⟨-11106492779241994866425035691001,1509506747372340137293148841410560⟩⟩

def packet0133 : StripRowPacket :=
  ⟨⟨⟨8,8,5,3⟩,
    ![191,1139,2459,3986,5512,6833,7769],![267,1185,2496,4013,5531,6844,7774]⟩,
    ⟨-297300843156232559404770969,40269884395537454726287831040⟩,
    ⟨-1108144051862878203733591739,164798462307442832181609021440⟩⟩

def packet0134 : StripRowPacket :=
  ⟨⟨⟨8,9,5,3⟩,
    ![189,1133,2454,3982,5510,6832,7769],![264,1179,2491,4009,5529,6843,7774]⟩,
    ⟨-99875096317428634953232890461,13367130368064513069081470894080⟩,
    ⟨-2569204642030409512283791349363,377376686843085034323287210352640⟩⟩

def packet0135 : StripRowPacket :=
  ⟨⟨⟨8,10,5,2⟩,
    ![126,1095,2424,3960,5496,6825,7766],![210,1139,2458,3986,5514,6835,7772]⟩,
    ⟨-17395750406804877100621005056587,2143475459841070104027122787205120⟩,
    ⟨-19173683772106405447682483482247,2574529806748077066002418778439680⟩⟩

def packet0136 : StripRowPacket :=
  ⟨⟨⟨8,11,5,2⟩,
    ![126,1090,2420,3957,5494,6824,7766],![208,1134,2454,3982,5511,6834,7771]⟩,
    ⟨-3061111539335033275631929660669,372899853330145185267480758026240⟩,
    ⟨-84299953720372292119638445597,11186962820888753550245936742400⟩⟩

def packet0137 : StripRowPacket :=
  ⟨⟨⟨8,10,5,3⟩,
    ![188,1128,2450,3978,5508,6831,7768],![262,1174,2486,4006,5526,6841,7774]⟩,
    ⟨-162027401510530203783475723953061,21434754598410701040271227872051200⟩,
    ⟨-4434841232503093948959323086509,643632451687019266500604694609920⟩⟩

def packet0138 : StripRowPacket :=
  ⟨⟨⟨8,11,5,3⟩,
    ![187,1124,2445,3975,5505,6830,7768],![259,1169,2481,4002,5524,6840,7773]⟩,
    ⟨-5701643489591180280878343649527,745799706660290370534961516052480⟩,
    ⟨-19496436273023233398862227151,2796740705222188387561484185600⟩⟩

def packet0139 : StripRowPacket :=
  ⟨⟨⟨7,6,5,0⟩,
    ![0,1021,2364,3916,5468,6811,7762],![96,1064,2399,3943,5486,6821,7767]⟩,
    ⟨-540616837727621,56626542122184320⟩,
    ⟨-5576481075517448295704182411,636471434711302648841175203840⟩⟩

def packet0140 : StripRowPacket :=
  ⟨⟨⟨7,6,5,1⟩,
    ![46,1049,2387,3932,5479,6816,7764],![158,1096,2424,3960,5497,6827,7769]⟩,
    ⟨-5220775139744917400920541,581851918939602062249738240⟩,
    ⟨-2605178019303453428370738571,318235717355651324420587601920⟩⟩

def packet0141 : StripRowPacket :=
  ⟨⟨⟨7,7,5,0⟩,
    ![0,1012,2356,3910,5464,6808,7761],![94,1055,2390,3936,5482,6819,7767]⟩,
    ⟨-3140546041,322092708080⟩,
    ⟨-85613255663968011719,9557029566924765136640⟩⟩

def packet0142 : StripRowPacket :=
  ⟨⟨⟨7,7,5,1⟩,
    ![46,1041,2378,3926,5474,6814,7763],![155,1087,2415,3953,5493,6825,7768]⟩,
    ⟨-67151313185534983567947,7329110643752213568192512⟩,
    ⟨-154970943725933581511,18516744785916732452240⟩⟩

def packet0143 : StripRowPacket :=
  ⟨⟨⟨7,6,5,2⟩,
    ![114,1080,2410,3950,5489,6821,7765],![214,1130,2450,3979,5509,6833,7771]⟩,
    ⟨-1165260601666459059506627,138749303747135876382629888⟩,
    ⟨-4844231001696365417778771873,636471434711302648841175203840⟩⟩

def packets005 : List StripRowPacket :=
  [packet0120, packet0121, packet0122, packet0123, packet0124, packet0125,
   packet0126, packet0127, packet0128, packet0129, packet0130, packet0131,
   packet0132, packet0133, packet0134, packet0135, packet0136, packet0137,
   packet0138, packet0139, packet0140, packet0141, packet0142, packet0143]

theorem packet0120_membership : packet0120 ∈ packets005 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0120_shape : checkStripShape packet0120.row = true := by
  decide +kernel

private theorem packet0120_cache : checkStripCache packet0120 = true := by
  decide +kernel

private theorem packet0120_pair (i : Fin 7) : checkEdgePair packet0120 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0120_ok : checkStripPacket packet0120 = true :=
  checkStripPacket_intro packet0120_shape packet0120_cache packet0120_pair

theorem packet0121_membership : packet0121 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0121_shape : checkStripShape packet0121.row = true := by
  decide +kernel

private theorem packet0121_cache : checkStripCache packet0121 = true := by
  decide +kernel

private theorem packet0121_pair (i : Fin 7) : checkEdgePair packet0121 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0121_ok : checkStripPacket packet0121 = true :=
  checkStripPacket_intro packet0121_shape packet0121_cache packet0121_pair

theorem packet0122_membership : packet0122 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0122_shape : checkStripShape packet0122.row = true := by
  decide +kernel

private theorem packet0122_cache : checkStripCache packet0122 = true := by
  decide +kernel

private theorem packet0122_pair (i : Fin 7) : checkEdgePair packet0122 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0122_ok : checkStripPacket packet0122 = true :=
  checkStripPacket_intro packet0122_shape packet0122_cache packet0122_pair

theorem packet0123_membership : packet0123 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0123_shape : checkStripShape packet0123.row = true := by
  decide +kernel

private theorem packet0123_cache : checkStripCache packet0123 = true := by
  decide +kernel

private theorem packet0123_pair (i : Fin 7) : checkEdgePair packet0123 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0123_ok : checkStripPacket packet0123 = true :=
  checkStripPacket_intro packet0123_shape packet0123_cache packet0123_pair

theorem packet0124_membership : packet0124 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0124_shape : checkStripShape packet0124.row = true := by
  decide +kernel

private theorem packet0124_cache : checkStripCache packet0124 = true := by
  decide +kernel

private theorem packet0124_pair (i : Fin 7) : checkEdgePair packet0124 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0124_ok : checkStripPacket packet0124 = true :=
  checkStripPacket_intro packet0124_shape packet0124_cache packet0124_pair

theorem packet0125_membership : packet0125 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0125_shape : checkStripShape packet0125.row = true := by
  decide +kernel

private theorem packet0125_cache : checkStripCache packet0125 = true := by
  decide +kernel

private theorem packet0125_pair (i : Fin 7) : checkEdgePair packet0125 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0125_ok : checkStripPacket packet0125 = true :=
  checkStripPacket_intro packet0125_shape packet0125_cache packet0125_pair

theorem packet0126_membership : packet0126 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0126_shape : checkStripShape packet0126.row = true := by
  decide +kernel

private theorem packet0126_cache : checkStripCache packet0126 = true := by
  decide +kernel

private theorem packet0126_pair (i : Fin 7) : checkEdgePair packet0126 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0126_ok : checkStripPacket packet0126 = true :=
  checkStripPacket_intro packet0126_shape packet0126_cache packet0126_pair

theorem packet0127_membership : packet0127 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0127_shape : checkStripShape packet0127.row = true := by
  decide +kernel

private theorem packet0127_cache : checkStripCache packet0127 = true := by
  decide +kernel

private theorem packet0127_pair (i : Fin 7) : checkEdgePair packet0127 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0127_ok : checkStripPacket packet0127 = true :=
  checkStripPacket_intro packet0127_shape packet0127_cache packet0127_pair

theorem packet0128_membership : packet0128 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0128_shape : checkStripShape packet0128.row = true := by
  decide +kernel

private theorem packet0128_cache : checkStripCache packet0128 = true := by
  decide +kernel

private theorem packet0128_pair (i : Fin 7) : checkEdgePair packet0128 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0128_ok : checkStripPacket packet0128 = true :=
  checkStripPacket_intro packet0128_shape packet0128_cache packet0128_pair

theorem packet0129_membership : packet0129 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0129_shape : checkStripShape packet0129.row = true := by
  decide +kernel

private theorem packet0129_cache : checkStripCache packet0129 = true := by
  decide +kernel

private theorem packet0129_pair (i : Fin 7) : checkEdgePair packet0129 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0129_ok : checkStripPacket packet0129 = true :=
  checkStripPacket_intro packet0129_shape packet0129_cache packet0129_pair

theorem packet0130_membership : packet0130 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0130_shape : checkStripShape packet0130.row = true := by
  decide +kernel

private theorem packet0130_cache : checkStripCache packet0130 = true := by
  decide +kernel

private theorem packet0130_pair (i : Fin 7) : checkEdgePair packet0130 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0130_ok : checkStripPacket packet0130 = true :=
  checkStripPacket_intro packet0130_shape packet0130_cache packet0130_pair

theorem packet0131_membership : packet0131 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0131_shape : checkStripShape packet0131.row = true := by
  decide +kernel

private theorem packet0131_cache : checkStripCache packet0131 = true := by
  decide +kernel

private theorem packet0131_pair (i : Fin 7) : checkEdgePair packet0131 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0131_ok : checkStripPacket packet0131 = true :=
  checkStripPacket_intro packet0131_shape packet0131_cache packet0131_pair

theorem packet0132_membership : packet0132 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0132_shape : checkStripShape packet0132.row = true := by
  decide +kernel

private theorem packet0132_cache : checkStripCache packet0132 = true := by
  decide +kernel

private theorem packet0132_pair (i : Fin 7) : checkEdgePair packet0132 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0132_ok : checkStripPacket packet0132 = true :=
  checkStripPacket_intro packet0132_shape packet0132_cache packet0132_pair

theorem packet0133_membership : packet0133 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0133_shape : checkStripShape packet0133.row = true := by
  decide +kernel

private theorem packet0133_cache : checkStripCache packet0133 = true := by
  decide +kernel

private theorem packet0133_pair (i : Fin 7) : checkEdgePair packet0133 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0133_ok : checkStripPacket packet0133 = true :=
  checkStripPacket_intro packet0133_shape packet0133_cache packet0133_pair

theorem packet0134_membership : packet0134 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0134_shape : checkStripShape packet0134.row = true := by
  decide +kernel

private theorem packet0134_cache : checkStripCache packet0134 = true := by
  decide +kernel

private theorem packet0134_pair (i : Fin 7) : checkEdgePair packet0134 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0134_ok : checkStripPacket packet0134 = true :=
  checkStripPacket_intro packet0134_shape packet0134_cache packet0134_pair

theorem packet0135_membership : packet0135 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0135_shape : checkStripShape packet0135.row = true := by
  decide +kernel

private theorem packet0135_cache : checkStripCache packet0135 = true := by
  decide +kernel

private theorem packet0135_pair (i : Fin 7) : checkEdgePair packet0135 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0135_ok : checkStripPacket packet0135 = true :=
  checkStripPacket_intro packet0135_shape packet0135_cache packet0135_pair

theorem packet0136_membership : packet0136 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0136_shape : checkStripShape packet0136.row = true := by
  decide +kernel

private theorem packet0136_cache : checkStripCache packet0136 = true := by
  decide +kernel

private theorem packet0136_pair (i : Fin 7) : checkEdgePair packet0136 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0136_ok : checkStripPacket packet0136 = true :=
  checkStripPacket_intro packet0136_shape packet0136_cache packet0136_pair

theorem packet0137_membership : packet0137 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0137_shape : checkStripShape packet0137.row = true := by
  decide +kernel

private theorem packet0137_cache : checkStripCache packet0137 = true := by
  decide +kernel

private theorem packet0137_pair (i : Fin 7) : checkEdgePair packet0137 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0137_ok : checkStripPacket packet0137 = true :=
  checkStripPacket_intro packet0137_shape packet0137_cache packet0137_pair

theorem packet0138_membership : packet0138 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0138_shape : checkStripShape packet0138.row = true := by
  decide +kernel

private theorem packet0138_cache : checkStripCache packet0138 = true := by
  decide +kernel

private theorem packet0138_pair (i : Fin 7) : checkEdgePair packet0138 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0138_ok : checkStripPacket packet0138 = true :=
  checkStripPacket_intro packet0138_shape packet0138_cache packet0138_pair

theorem packet0139_membership : packet0139 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0139_shape : checkStripShape packet0139.row = true := by
  decide +kernel

private theorem packet0139_cache : checkStripCache packet0139 = true := by
  decide +kernel

private theorem packet0139_pair (i : Fin 7) : checkEdgePair packet0139 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0139_ok : checkStripPacket packet0139 = true :=
  checkStripPacket_intro packet0139_shape packet0139_cache packet0139_pair

theorem packet0140_membership : packet0140 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0140_shape : checkStripShape packet0140.row = true := by
  decide +kernel

private theorem packet0140_cache : checkStripCache packet0140 = true := by
  decide +kernel

private theorem packet0140_pair (i : Fin 7) : checkEdgePair packet0140 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0140_ok : checkStripPacket packet0140 = true :=
  checkStripPacket_intro packet0140_shape packet0140_cache packet0140_pair

theorem packet0141_membership : packet0141 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0141_shape : checkStripShape packet0141.row = true := by
  decide +kernel

private theorem packet0141_cache : checkStripCache packet0141 = true := by
  decide +kernel

private theorem packet0141_pair (i : Fin 7) : checkEdgePair packet0141 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0141_ok : checkStripPacket packet0141 = true :=
  checkStripPacket_intro packet0141_shape packet0141_cache packet0141_pair

theorem packet0142_membership : packet0142 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0142_shape : checkStripShape packet0142.row = true := by
  decide +kernel

private theorem packet0142_cache : checkStripCache packet0142 = true := by
  decide +kernel

private theorem packet0142_pair (i : Fin 7) : checkEdgePair packet0142 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0142_ok : checkStripPacket packet0142 = true :=
  checkStripPacket_intro packet0142_shape packet0142_cache packet0142_pair

theorem packet0143_membership : packet0143 ∈ packets005 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0143_shape : checkStripShape packet0143.row = true := by
  decide +kernel

private theorem packet0143_cache : checkStripCache packet0143 = true := by
  decide +kernel

private theorem packet0143_pair (i : Fin 7) : checkEdgePair packet0143 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0143_ok : checkStripPacket packet0143 = true :=
  checkStripPacket_intro packet0143_shape packet0143_cache packet0143_pair

theorem packets005_checked : packets005.all checkStripPacket = true := by
  simp only [packets005, List.all_cons, List.all_nil, Bool.true_and, packet0120_ok,
    packet0121_ok, packet0122_ok, packet0123_ok, packet0124_ok, packet0125_ok,
    packet0126_ok, packet0127_ok, packet0128_ok, packet0129_ok, packet0130_ok,
    packet0131_ok, packet0132_ok, packet0133_ok, packet0134_ok, packet0135_ok,
    packet0136_ok, packet0137_ok, packet0138_ok, packet0139_ok, packet0140_ok,
    packet0141_ok, packet0142_ok, packet0143_ok]

theorem packets005_valid : packets005.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
