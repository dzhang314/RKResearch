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

def packet0072 : StripRowPacket :=
  ⟨⟨⟨8,2,6,11⟩,
    ![343,1263,2560,4060,5560,6857,7776],![383,1297,2588,4081,5574,6866,7781]⟩,
    ⟨-9163964021157755421174108503,1640190277820725891604322254848⟩,
    ⟨-360952690785036457831968381727,69390247060175568468785065590784⟩⟩

def packet0073 : StripRowPacket :=
  ⟨⟨⟨8,3,6,10⟩,
    ![314,1238,2540,4045,5550,6852,7775],![356,1270,2567,4065,5564,6861,7780]⟩,
    ⟨-9186071804043202238953711427,1553464078791715986679356784640⟩,
    ⟨-83519371511657049070781557,15107315965651392193879900160⟩⟩

def packet0074 : StripRowPacket :=
  ⟨⟨⟨8,3,6,11⟩,
    ![338,1257,2554,4056,5557,6856,7776],![377,1290,2582,4077,5572,6864,7781]⟩,
    ⟨-17597401247485848761284716333,3106928157583431973358713569280⟩,
    ⟨-1056600390365519803215508353,200171936544880946568908677120⟩⟩

def packet0075 : StripRowPacket :=
  ⟨⟨⟨8,0,6,12⟩,
    ![380,1295,2586,4079,5572,6863,7778],![420,1331,2616,4102,5588,6873,7783]⟩,
    ⟨-3616417600873272973,696066976703538851840⟩,
    ⟨-631843740419413889,131402970357737062400⟩⟩

def packet0076 : StripRowPacket :=
  ⟨⟨⟨8,0,6,13⟩,
    ![402,1314,2602,4090,5579,6867,7779],![441,1350,2632,4114,5595,6877,7785]⟩,
    ⟨-13813053569911372211,2784267906814155407360⟩,
    ⟨-3305097120317196481,722716336967553843200⟩⟩

def packet0077 : StripRowPacket :=
  ⟨⟨⟨8,1,6,12⟩,
    ![373,1288,2581,4075,5569,6862,7778],![411,1323,2610,4097,5585,6871,7783]⟩,
    ⟨-37270908966618774397206748065973,7072969070521184292676135215923200⟩,
    ⟨-71526530212590527264758186144343,14647620957733877103949232986849280⟩⟩

def packet0078 : StripRowPacket :=
  ⟨⟨⟨8,1,6,13⟩,
    ![395,1307,2596,4086,5576,6866,7779],![432,1343,2626,4109,5592,6875,7784]⟩,
    ⟨-142304186036073453393168652817083,28291876282084737170704540863692800⟩,
    ⟨-6800537141869034156572769908641,1464762095773387710394923298684928⟩⟩

def packet0079 : StripRowPacket :=
  ⟨⟨⟨8,0,6,14⟩,
    ![422,1333,2617,4102,5587,6871,7781],![460,1370,2649,4126,5603,6881,7786]⟩,
    ⟨-1316043673632965253,278426790681415540736⟩,
    ⟨-1254021467331046629,289086534787021537280⟩⟩

def packet0080 : StripRowPacket :=
  ⟨⟨⟨8,0,6,15⟩,
    ![441,1352,2633,4114,5594,6875,7782],![478,1390,2666,4139,5611,6885,7787]⟩,
    ⟨-12507819902747932849,2784267906814155407360⟩,
    ⟨-370626277042254583,90339542120944230400⟩⟩

def packet0081 : StripRowPacket :=
  ⟨⟨⟨8,1,6,14⟩,
    ![414,1326,2612,4098,5584,6869,7780],![451,1362,2642,4121,5600,6879,7785]⟩,
    ⟨-67762368102835904598755156685137,14145938141042368585352270431846400⟩,
    ⟨-64484212624790155866697212028477,14647620957733877103949232986849280⟩⟩

def packet0082 : StripRowPacket :=
  ⟨⟨⟨8,1,6,15⟩,
    ![433,1345,2628,4110,5592,6873,7781],![468,1382,2659,4134,5608,6883,7787]⟩,
    ⟨-1980696713465694846182338060361,435259635108995956472377551749120⟩,
    ⟨-3810190864430623135479170310659,915476309858367318996827061678080⟩⟩

def packet0083 : StripRowPacket :=
  ⟨⟨⟨8,2,6,12⟩,
    ![367,1282,2575,4071,5567,6861,7778],![404,1316,2604,4093,5582,6870,7782]⟩,
    ⟨-116106693420813477705628744443,21732521181124618063757269876736⟩,
    ⟨-15133074549943518380602829990171,3053170870647725012626542885994496⟩⟩

def packet0084 : StripRowPacket :=
  ⟨⟨⟨8,2,6,13⟩,
    ![388,1301,2590,4082,5574,6864,7779],![424,1335,2620,4105,5589,6874,7784]⟩,
    ⟨-443163454245146784322802204885,86930084724498472255029079506944⟩,
    ⟨-7192115352672716308299525592177,1526585435323862506313271442997248⟩⟩

def packet0085 : StripRowPacket :=
  ⟨⟨⟨8,3,6,12⟩,
    ![361,1275,2570,4067,5564,6859,7777],![397,1309,2598,4088,5579,6868,7782]⟩,
    ⟨-4205664721721323261165502453,776732039395857993339678392320⟩,
    ⟨-4026276432806334824972644303,800687746179523786275634708480⟩⟩

def packet0086 : StripRowPacket :=
  ⟨⟨⟨8,3,6,13⟩,
    ![383,1294,2585,4078,5571,6863,7778],![417,1328,2614,4100,5587,6872,7783]⟩,
    ⟨-16047916526284737328039303291,3106928157583431973358713569280⟩,
    ⟨-13378151413113952577214179,2799607504124209042921799680⟩⟩

def packet0087 : StripRowPacket :=
  ⟨⟨⟨8,2,6,14⟩,
    ![408,1320,2606,4094,5581,6868,7780],![442,1355,2636,4117,5597,6878,7785]⟩,
    ⟨-210950067403519828911544715999,43465042362249236127514539753472⟩,
    ⟨-13635386860747346852595272378537,3053170870647725012626542885994496⟩⟩

def packet0088 : StripRowPacket :=
  ⟨⟨⟨8,2,6,15⟩,
    ![426,1339,2622,4106,5589,6872,7781],![460,1374,2653,4130,5606,6882,7786]⟩,
    ⟨-400636815368932531323376659111,86930084724498472255029079506944⟩,
    ⟨-805408938509328818036968348295,190823179415482813289158930374656⟩⟩

def packet0089 : StripRowPacket :=
  ⟨⟨⟨8,3,6,14⟩,
    ![402,1313,2601,4090,5579,6867,7779],![435,1348,2631,4113,5595,6876,7784]⟩,
    ⟨-138847037869856196467423607,28244801432576654303261032448⟩,
    ⟨-725205235098969209838773217,160137549235904757255126941696⟩⟩

def packet0090 : StripRowPacket :=
  ⟨⟨⟨8,3,6,15⟩,
    ![420,1332,2617,4102,5587,6871,7781],![452,1367,2648,4126,5603,6881,7786]⟩,
    ⟨-14498431805083625894793890249,3106928157583431973358713569280⟩,
    ⟨-214118815427443853831529811,50042984136220236642227169280⟩⟩

def packet0091 : StripRowPacket :=
  ⟨⟨⟨8,4,6,8⟩,
    ![257,1196,2506,4021,5535,6844,7773],![305,1226,2531,4040,5548,6853,7777]⟩,
    ⟨-134413235419428887659277649701,20675036453914099343679291944960⟩,
    ⟨-2881697418418351134114051751,471100404390448278992892329984⟩⟩

def packet0092 : StripRowPacket :=
  ⟨⟨⟨8,4,6,9⟩,
    ![284,1214,2520,4031,5541,6848,7773],![328,1245,2546,4050,5555,6856,7778]⟩,
    ⟨-1033306823266783397737139412349,165400291631312794749434335559680⟩,
    ⟨-6904580658590640229551031703,1177751010976120697482230824960⟩⟩

def packet0093 : StripRowPacket :=
  ⟨⟨⟨8,5,6,8⟩,
    ![254,1190,2501,4017,5532,6843,7772],![301,1220,2526,4035,5545,6851,7777]⟩,
    ⟨-332377747809689229777957341909,50446538614042353517432866488320⟩,
    ⟨-9001270523072449306382301856873,1450958070828439567023527350435840⟩⟩

def packet0094 : StripRowPacket :=
  ⟨⟨⟨8,5,6,9⟩,
    ![281,1208,2515,4027,5539,6846,7773],![324,1239,2540,4046,5552,6855,7778]⟩,
    ⟨-510954449228094948608737981593,80714461782467765627892586381312⟩,
    ⟨-862580297192697906854915101921,145095807082843956702352735043584⟩⟩

def packet0095 : StripRowPacket :=
  ⟨⟨⟨8,4,6,10⟩,
    ![310,1232,2534,4041,5548,6851,7775],![351,1264,2561,4061,5562,6859,7779]⟩,
    ⟨-99130776317813569420005762709,16540029163131279474943433555968⟩,
    ⟨-1016141195559292711356451389,181192463227095491920343203840⟩⟩

def packets003 : List StripRowPacket :=
  [packet0072, packet0073, packet0074, packet0075, packet0076, packet0077,
   packet0078, packet0079, packet0080, packet0081, packet0082, packet0083,
   packet0084, packet0085, packet0086, packet0087, packet0088, packet0089,
   packet0090, packet0091, packet0092, packet0093, packet0094, packet0095]

theorem packet0072_membership : packet0072 ∈ packets003 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0072_shape : checkStripShape packet0072.row = true := by
  decide +kernel

private theorem packet0072_cache : checkStripCache packet0072 = true := by
  decide +kernel

private theorem packet0072_pair (i : Fin 7) : checkEdgePair packet0072 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0072_ok : checkStripPacket packet0072 = true :=
  checkStripPacket_intro packet0072_shape packet0072_cache packet0072_pair

theorem packet0073_membership : packet0073 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0073_shape : checkStripShape packet0073.row = true := by
  decide +kernel

private theorem packet0073_cache : checkStripCache packet0073 = true := by
  decide +kernel

private theorem packet0073_pair (i : Fin 7) : checkEdgePair packet0073 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0073_ok : checkStripPacket packet0073 = true :=
  checkStripPacket_intro packet0073_shape packet0073_cache packet0073_pair

theorem packet0074_membership : packet0074 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0074_shape : checkStripShape packet0074.row = true := by
  decide +kernel

private theorem packet0074_cache : checkStripCache packet0074 = true := by
  decide +kernel

private theorem packet0074_pair (i : Fin 7) : checkEdgePair packet0074 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0074_ok : checkStripPacket packet0074 = true :=
  checkStripPacket_intro packet0074_shape packet0074_cache packet0074_pair

theorem packet0075_membership : packet0075 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0075_shape : checkStripShape packet0075.row = true := by
  decide +kernel

private theorem packet0075_cache : checkStripCache packet0075 = true := by
  decide +kernel

private theorem packet0075_pair (i : Fin 7) : checkEdgePair packet0075 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0075_ok : checkStripPacket packet0075 = true :=
  checkStripPacket_intro packet0075_shape packet0075_cache packet0075_pair

theorem packet0076_membership : packet0076 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0076_shape : checkStripShape packet0076.row = true := by
  decide +kernel

private theorem packet0076_cache : checkStripCache packet0076 = true := by
  decide +kernel

private theorem packet0076_pair (i : Fin 7) : checkEdgePair packet0076 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0076_ok : checkStripPacket packet0076 = true :=
  checkStripPacket_intro packet0076_shape packet0076_cache packet0076_pair

theorem packet0077_membership : packet0077 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0077_shape : checkStripShape packet0077.row = true := by
  decide +kernel

private theorem packet0077_cache : checkStripCache packet0077 = true := by
  decide +kernel

private theorem packet0077_pair (i : Fin 7) : checkEdgePair packet0077 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0077_ok : checkStripPacket packet0077 = true :=
  checkStripPacket_intro packet0077_shape packet0077_cache packet0077_pair

theorem packet0078_membership : packet0078 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0078_shape : checkStripShape packet0078.row = true := by
  decide +kernel

private theorem packet0078_cache : checkStripCache packet0078 = true := by
  decide +kernel

private theorem packet0078_pair (i : Fin 7) : checkEdgePair packet0078 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0078_ok : checkStripPacket packet0078 = true :=
  checkStripPacket_intro packet0078_shape packet0078_cache packet0078_pair

theorem packet0079_membership : packet0079 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0079_shape : checkStripShape packet0079.row = true := by
  decide +kernel

private theorem packet0079_cache : checkStripCache packet0079 = true := by
  decide +kernel

private theorem packet0079_pair (i : Fin 7) : checkEdgePair packet0079 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0079_ok : checkStripPacket packet0079 = true :=
  checkStripPacket_intro packet0079_shape packet0079_cache packet0079_pair

theorem packet0080_membership : packet0080 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0080_shape : checkStripShape packet0080.row = true := by
  decide +kernel

private theorem packet0080_cache : checkStripCache packet0080 = true := by
  decide +kernel

private theorem packet0080_pair (i : Fin 7) : checkEdgePair packet0080 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0080_ok : checkStripPacket packet0080 = true :=
  checkStripPacket_intro packet0080_shape packet0080_cache packet0080_pair

theorem packet0081_membership : packet0081 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0081_shape : checkStripShape packet0081.row = true := by
  decide +kernel

private theorem packet0081_cache : checkStripCache packet0081 = true := by
  decide +kernel

private theorem packet0081_pair (i : Fin 7) : checkEdgePair packet0081 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0081_ok : checkStripPacket packet0081 = true :=
  checkStripPacket_intro packet0081_shape packet0081_cache packet0081_pair

theorem packet0082_membership : packet0082 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0082_shape : checkStripShape packet0082.row = true := by
  decide +kernel

private theorem packet0082_cache : checkStripCache packet0082 = true := by
  decide +kernel

private theorem packet0082_pair (i : Fin 7) : checkEdgePair packet0082 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0082_ok : checkStripPacket packet0082 = true :=
  checkStripPacket_intro packet0082_shape packet0082_cache packet0082_pair

theorem packet0083_membership : packet0083 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0083_shape : checkStripShape packet0083.row = true := by
  decide +kernel

private theorem packet0083_cache : checkStripCache packet0083 = true := by
  decide +kernel

private theorem packet0083_pair (i : Fin 7) : checkEdgePair packet0083 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0083_ok : checkStripPacket packet0083 = true :=
  checkStripPacket_intro packet0083_shape packet0083_cache packet0083_pair

theorem packet0084_membership : packet0084 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0084_shape : checkStripShape packet0084.row = true := by
  decide +kernel

private theorem packet0084_cache : checkStripCache packet0084 = true := by
  decide +kernel

private theorem packet0084_pair (i : Fin 7) : checkEdgePair packet0084 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0084_ok : checkStripPacket packet0084 = true :=
  checkStripPacket_intro packet0084_shape packet0084_cache packet0084_pair

theorem packet0085_membership : packet0085 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0085_shape : checkStripShape packet0085.row = true := by
  decide +kernel

private theorem packet0085_cache : checkStripCache packet0085 = true := by
  decide +kernel

private theorem packet0085_pair (i : Fin 7) : checkEdgePair packet0085 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0085_ok : checkStripPacket packet0085 = true :=
  checkStripPacket_intro packet0085_shape packet0085_cache packet0085_pair

theorem packet0086_membership : packet0086 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0086_shape : checkStripShape packet0086.row = true := by
  decide +kernel

private theorem packet0086_cache : checkStripCache packet0086 = true := by
  decide +kernel

private theorem packet0086_pair (i : Fin 7) : checkEdgePair packet0086 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0086_ok : checkStripPacket packet0086 = true :=
  checkStripPacket_intro packet0086_shape packet0086_cache packet0086_pair

theorem packet0087_membership : packet0087 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0087_shape : checkStripShape packet0087.row = true := by
  decide +kernel

private theorem packet0087_cache : checkStripCache packet0087 = true := by
  decide +kernel

private theorem packet0087_pair (i : Fin 7) : checkEdgePair packet0087 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0087_ok : checkStripPacket packet0087 = true :=
  checkStripPacket_intro packet0087_shape packet0087_cache packet0087_pair

theorem packet0088_membership : packet0088 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0088_shape : checkStripShape packet0088.row = true := by
  decide +kernel

private theorem packet0088_cache : checkStripCache packet0088 = true := by
  decide +kernel

private theorem packet0088_pair (i : Fin 7) : checkEdgePair packet0088 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0088_ok : checkStripPacket packet0088 = true :=
  checkStripPacket_intro packet0088_shape packet0088_cache packet0088_pair

theorem packet0089_membership : packet0089 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0089_shape : checkStripShape packet0089.row = true := by
  decide +kernel

private theorem packet0089_cache : checkStripCache packet0089 = true := by
  decide +kernel

private theorem packet0089_pair (i : Fin 7) : checkEdgePair packet0089 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0089_ok : checkStripPacket packet0089 = true :=
  checkStripPacket_intro packet0089_shape packet0089_cache packet0089_pair

theorem packet0090_membership : packet0090 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0090_shape : checkStripShape packet0090.row = true := by
  decide +kernel

private theorem packet0090_cache : checkStripCache packet0090 = true := by
  decide +kernel

private theorem packet0090_pair (i : Fin 7) : checkEdgePair packet0090 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0090_ok : checkStripPacket packet0090 = true :=
  checkStripPacket_intro packet0090_shape packet0090_cache packet0090_pair

theorem packet0091_membership : packet0091 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0091_shape : checkStripShape packet0091.row = true := by
  decide +kernel

private theorem packet0091_cache : checkStripCache packet0091 = true := by
  decide +kernel

private theorem packet0091_pair (i : Fin 7) : checkEdgePair packet0091 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0091_ok : checkStripPacket packet0091 = true :=
  checkStripPacket_intro packet0091_shape packet0091_cache packet0091_pair

theorem packet0092_membership : packet0092 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0092_shape : checkStripShape packet0092.row = true := by
  decide +kernel

private theorem packet0092_cache : checkStripCache packet0092 = true := by
  decide +kernel

private theorem packet0092_pair (i : Fin 7) : checkEdgePair packet0092 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0092_ok : checkStripPacket packet0092 = true :=
  checkStripPacket_intro packet0092_shape packet0092_cache packet0092_pair

theorem packet0093_membership : packet0093 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0093_shape : checkStripShape packet0093.row = true := by
  decide +kernel

private theorem packet0093_cache : checkStripCache packet0093 = true := by
  decide +kernel

private theorem packet0093_pair (i : Fin 7) : checkEdgePair packet0093 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0093_ok : checkStripPacket packet0093 = true :=
  checkStripPacket_intro packet0093_shape packet0093_cache packet0093_pair

theorem packet0094_membership : packet0094 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0094_shape : checkStripShape packet0094.row = true := by
  decide +kernel

private theorem packet0094_cache : checkStripCache packet0094 = true := by
  decide +kernel

private theorem packet0094_pair (i : Fin 7) : checkEdgePair packet0094 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0094_ok : checkStripPacket packet0094 = true :=
  checkStripPacket_intro packet0094_shape packet0094_cache packet0094_pair

theorem packet0095_membership : packet0095 ∈ packets003 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0095_shape : checkStripShape packet0095.row = true := by
  decide +kernel

private theorem packet0095_cache : checkStripCache packet0095 = true := by
  decide +kernel

private theorem packet0095_pair (i : Fin 7) : checkEdgePair packet0095 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0095_ok : checkStripPacket packet0095 = true :=
  checkStripPacket_intro packet0095_shape packet0095_cache packet0095_pair

theorem packets003_checked : packets003.all checkStripPacket = true := by
  simp only [packets003, List.all_cons, List.all_nil, Bool.true_and, packet0072_ok,
    packet0073_ok, packet0074_ok, packet0075_ok, packet0076_ok, packet0077_ok,
    packet0078_ok, packet0079_ok, packet0080_ok, packet0081_ok, packet0082_ok,
    packet0083_ok, packet0084_ok, packet0085_ok, packet0086_ok, packet0087_ok,
    packet0088_ok, packet0089_ok, packet0090_ok, packet0091_ok, packet0092_ok,
    packet0093_ok, packet0094_ok, packet0095_ok]

theorem packets003_valid : packets003.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
