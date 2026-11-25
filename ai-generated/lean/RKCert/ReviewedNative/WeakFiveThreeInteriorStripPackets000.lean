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

def packet0000 : StripRowPacket :=
  ⟨⟨⟨8,0,6,0⟩,
    ![0,1104,2437,3971,5504,6829,7768],![66,1129,2457,3987,5515,6836,7772]⟩,
    ⟨-348391756351152001,43504186043971178240⟩,
    ⟨-11031323992363470583,1445432673935107686400⟩⟩

def packet0001 : StripRowPacket :=
  ⟨⟨⟨8,0,6,1⟩,
    ![16,1117,2447,3978,5508,6831,7768],![104,1142,2468,3995,5520,6838,7773]⟩,
    ⟨-21644455572892008383,2784267906814155407360⟩,
    ⟨-485965322199286853,65701485178868531200⟩⟩

def packet0002 : StripRowPacket :=
  ⟨⟨⟨8,1,6,0⟩,
    ![0,1096,2430,3966,5500,6827,7767],![64,1120,2450,3982,5511,6834,7771]⟩,
    ⟨-2918101647560641,358269542957991808⟩,
    ⟨-113780435739392755653124030839539,14647620957733877103949232986849280⟩⟩

def packet0003 : StripRowPacket :=
  ⟨⟨⟨8,1,6,1⟩,
    ![17,1108,2440,3973,5505,6829,7768],![102,1134,2461,3989,5516,6837,7772]⟩,
    ⟨-223657584000893183741068726178791,28291876282084737170704540863692800⟩,
    ⟨-55129638472746284977046771890803,7323810478866938551974616493424640⟩⟩

def packet0004 : StripRowPacket :=
  ⟨⟨⟨8,0,6,2⟩,
    ![57,1130,2458,3986,5513,6834,7769],![141,1156,2479,4003,5525,6841,7774]⟩,
    ⟨-10495919369655144351,1392133953407077703680⟩,
    ⟨-10351150184405150949,1445432673935107686400⟩⟩

def packet0005 : StripRowPacket :=
  ⟨⟨⟨8,0,6,3⟩,
    ![97,1144,2468,3994,5518,6836,7770],![176,1171,2491,4011,5530,6844,7774]⟩,
    ⟨-20339221905728569021,2784267906814155407360⟩,
    ⟨-2502765820106497783,361358168483776921600⟩⟩

def packet0006 : StripRowPacket :=
  ⟨⟨⟨8,1,6,2⟩,
    ![57,1122,2451,3981,5510,6832,7769],![138,1148,2472,3998,5522,6839,7773]⟩,
    ⟨-8341466698865059213285014874307,1088149087772489891180943879372800⟩,
    ⟨-106738118151592384255063056723673,14647620957733877103949232986849280⟩⟩

def packet0007 : StripRowPacket :=
  ⟨⟨⟨8,1,6,3⟩,
    ![97,1136,2462,3989,5515,6834,7769],![172,1163,2484,4006,5527,6842,7774]⟩,
    ⟨-210098684340089895349752047285173,28291876282084737170704540863692800⟩,
    ⟨-5160847967884609927801628483287,732381047886693855197461649342464⟩⟩

def packet0008 : StripRowPacket :=
  ⟨⟨⟨8,2,6,0⟩,
    ![0,1088,2423,3961,5497,6825,7767],![62,1112,2443,3976,5508,6832,7771]⟩,
    ⟨-2137209155904753,258186813379818752⟩,
    ⟨-2192654607738231595331652332725,277560988240702273875140262363136⟩⟩

def packet0009 : StripRowPacket :=
  ⟨⟨⟨8,2,6,1⟩,
    ![17,1101,2434,3968,5502,6828,7767],![99,1126,2454,3984,5513,6835,7772]⟩,
    ⟨-698323287502432302319355479529,86930084724498472255029079506944⟩,
    ⟨-11685178420261230892322198427079,1526585435323862506313271442997248⟩⟩

def packet0010 : StripRowPacket :=
  ⟨⟨⟨8,3,6,0⟩,
    ![0,1080,2417,3956,5494,6824,7766],![60,1104,2437,3972,5505,6831,7770]⟩,
    ⟨-1532479806161,182288803702720⟩,
    ⟨-494444459744251344588101047,61591365090732598944279592960⟩⟩

def packet0011 : StripRowPacket :=
  ⟨⟨⟨8,3,6,1⟩,
    ![18,1093,2427,3964,5499,6826,7767],![97,1118,2448,3980,5510,6833,7771]⟩,
    ⟨-25344824853491405927511781543,3106928157583431973358713569280⟩,
    ⟨-3113826424009761545877962251,400343873089761893137817354240⟩⟩

def packet0012 : StripRowPacket :=
  ⟨⟨⟨8,2,6,2⟩,
    ![58,1114,2444,3976,5507,6830,7768],![135,1140,2466,3993,5518,6838,7772]⟩,
    ⟨-338529984032162587909821353321,43465042362249236127514539753472⟩,
    ⟨-22621512995924376020640618048341,3053170870647725012626542885994496⟩⟩

def packet0013 : StripRowPacket :=
  ⟨⟨⟨8,2,6,3⟩,
    ![96,1128,2455,3984,5512,6833,7769],![169,1155,2477,4001,5524,6840,7773]⟩,
    ⟨-655796648626218049319929933755,86930084724498472255029079506944⟩,
    ⟨-5468167287831572564159209810631,763292717661931253156635721498624⟩⟩

def packet0014 : StripRowPacket :=
  ⟨⟨⟨8,3,6,2⟩,
    ![58,1107,2438,3972,5504,6829,7768],![132,1132,2459,3988,5515,6836,7772]⟩,
    ⟨-12285041246445425105444537511,1553464078791715986679356784640⟩,
    ⟨-547957065396707154896957763,72789795107229435115966791680⟩⟩

def packet0015 : StripRowPacket :=
  ⟨⟨⟨8,3,6,3⟩,
    ![96,1121,2449,3980,5509,6831,7768],![166,1148,2471,3996,5521,6839,7773]⟩,
    ⟨-2163212739299117681296942591,282448014325766543032610324480⟩,
    ⟨-1456850647677008578994286571,200171936544880946568908677120⟩⟩

def packet0016 : StripRowPacket :=
  ⟨⟨⟨8,0,6,4⟩,
    ![135,1158,2480,4002,5523,6839,7771],![209,1187,2503,4020,5536,6846,7775]⟩,
    ⟨-984330253607342467,139213395340707770368⟩,
    ⟨-1934195275289366263,289086534787021537280⟩⟩

def packet0017 : StripRowPacket :=
  ⟨⟨⟨8,0,6,5⟩,
    ![172,1174,2492,4011,5529,6841,7772],![241,1203,2516,4029,5541,6849,7776]⟩,
    ⟨-19033988238565129659,2784267906814155407360⟩,
    ⟨-358880364325679673,55593564382119526400⟩⟩

def packet0018 : StripRowPacket :=
  ⟨⟨⟨8,1,6,4⟩,
    ![134,1151,2473,3997,5520,6837,7770],![205,1179,2496,4015,5532,6845,7775]⟩,
    ⟨-50829808627422062788523426959591,7072969070521184292676135215923200⟩,
    ⟨-99695800563792012857002082607807,14647620957733877103949232986849280⟩⟩

def packet0019 : StripRowPacket :=
  ⟨⟨⟨8,1,6,5⟩,
    ![170,1166,2485,4006,5526,6840,7771],![236,1195,2509,4024,5538,6848,7776]⟩,
    ⟨-39307956935857321391687073678311,5658375256416947434140908172738560⟩,
    ⟨-48087320884945913578985797774937,7323810478866938551974616493424640⟩⟩

def packet0020 : StripRowPacket :=
  ⟨⟨⟨8,0,6,6⟩,
    ![207,1190,2504,4019,5534,6844,7772],![271,1220,2528,4038,5547,6852,7777]⟩,
    ⟨-9190685702491704989,1392133953407077703680⟩,
    ⟨-8990802568488511681,1445432673935107686400⟩⟩

def packet0021 : StripRowPacket :=
  ⟨⟨⟨8,0,6,7⟩,
    ![240,1206,2516,4029,5540,6847,7773],![299,1237,2542,4048,5553,6855,7778]⟩,
    ⟨-1363750351646283869,214174454370319646720⟩,
    ⟨-1081339458063668983,180679084241888460800⟩⟩

def packet0022 : StripRowPacket :=
  ⟨⟨⟨8,1,6,6⟩,
    ![204,1182,2497,4015,5531,6843,7772],![266,1212,2522,4033,5544,6851,7777]⟩,
    ⟨-94880167424442481381388514472373,14145938141042368585352270431846400⟩,
    ⟨-92653482975991641458941108491941,14647620957733877103949232986849280⟩⟩

def packet0023 : StripRowPacket :=
  ⟨⟨⟨8,1,6,7⟩,
    ![236,1199,2510,4024,5537,6846,7773],![294,1229,2535,4043,5550,6854,7777]⟩,
    ⟨-182980885018483318567118689497937,28291876282084737170704540863692800⟩,
    ⟨-857041578673956305383755975327,140842509208979587537973394104320⟩⟩

def packets000 : List StripRowPacket :=
  [packet0000, packet0001, packet0002, packet0003, packet0004, packet0005,
   packet0006, packet0007, packet0008, packet0009, packet0010, packet0011,
   packet0012, packet0013, packet0014, packet0015, packet0016, packet0017,
   packet0018, packet0019, packet0020, packet0021, packet0022, packet0023]

theorem packet0000_membership : packet0000 ∈ packets000 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0000_shape : checkStripShape packet0000.row = true := by
  decide +kernel

private theorem packet0000_cache : checkStripCache packet0000 = true := by
  decide +kernel

private theorem packet0000_pair (i : Fin 7) : checkEdgePair packet0000 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0000_ok : checkStripPacket packet0000 = true :=
  checkStripPacket_intro packet0000_shape packet0000_cache packet0000_pair

theorem packet0001_membership : packet0001 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0001_shape : checkStripShape packet0001.row = true := by
  decide +kernel

private theorem packet0001_cache : checkStripCache packet0001 = true := by
  decide +kernel

private theorem packet0001_pair (i : Fin 7) : checkEdgePair packet0001 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0001_ok : checkStripPacket packet0001 = true :=
  checkStripPacket_intro packet0001_shape packet0001_cache packet0001_pair

theorem packet0002_membership : packet0002 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0002_shape : checkStripShape packet0002.row = true := by
  decide +kernel

private theorem packet0002_cache : checkStripCache packet0002 = true := by
  decide +kernel

private theorem packet0002_pair (i : Fin 7) : checkEdgePair packet0002 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0002_ok : checkStripPacket packet0002 = true :=
  checkStripPacket_intro packet0002_shape packet0002_cache packet0002_pair

theorem packet0003_membership : packet0003 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0003_shape : checkStripShape packet0003.row = true := by
  decide +kernel

private theorem packet0003_cache : checkStripCache packet0003 = true := by
  decide +kernel

private theorem packet0003_pair (i : Fin 7) : checkEdgePair packet0003 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0003_ok : checkStripPacket packet0003 = true :=
  checkStripPacket_intro packet0003_shape packet0003_cache packet0003_pair

theorem packet0004_membership : packet0004 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0004_shape : checkStripShape packet0004.row = true := by
  decide +kernel

private theorem packet0004_cache : checkStripCache packet0004 = true := by
  decide +kernel

private theorem packet0004_pair (i : Fin 7) : checkEdgePair packet0004 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0004_ok : checkStripPacket packet0004 = true :=
  checkStripPacket_intro packet0004_shape packet0004_cache packet0004_pair

theorem packet0005_membership : packet0005 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0005_shape : checkStripShape packet0005.row = true := by
  decide +kernel

private theorem packet0005_cache : checkStripCache packet0005 = true := by
  decide +kernel

private theorem packet0005_pair (i : Fin 7) : checkEdgePair packet0005 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0005_ok : checkStripPacket packet0005 = true :=
  checkStripPacket_intro packet0005_shape packet0005_cache packet0005_pair

theorem packet0006_membership : packet0006 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0006_shape : checkStripShape packet0006.row = true := by
  decide +kernel

private theorem packet0006_cache : checkStripCache packet0006 = true := by
  decide +kernel

private theorem packet0006_pair (i : Fin 7) : checkEdgePair packet0006 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0006_ok : checkStripPacket packet0006 = true :=
  checkStripPacket_intro packet0006_shape packet0006_cache packet0006_pair

theorem packet0007_membership : packet0007 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0007_shape : checkStripShape packet0007.row = true := by
  decide +kernel

private theorem packet0007_cache : checkStripCache packet0007 = true := by
  decide +kernel

private theorem packet0007_pair (i : Fin 7) : checkEdgePair packet0007 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0007_ok : checkStripPacket packet0007 = true :=
  checkStripPacket_intro packet0007_shape packet0007_cache packet0007_pair

theorem packet0008_membership : packet0008 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0008_shape : checkStripShape packet0008.row = true := by
  decide +kernel

private theorem packet0008_cache : checkStripCache packet0008 = true := by
  decide +kernel

private theorem packet0008_pair (i : Fin 7) : checkEdgePair packet0008 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0008_ok : checkStripPacket packet0008 = true :=
  checkStripPacket_intro packet0008_shape packet0008_cache packet0008_pair

theorem packet0009_membership : packet0009 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0009_shape : checkStripShape packet0009.row = true := by
  decide +kernel

private theorem packet0009_cache : checkStripCache packet0009 = true := by
  decide +kernel

private theorem packet0009_pair (i : Fin 7) : checkEdgePair packet0009 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0009_ok : checkStripPacket packet0009 = true :=
  checkStripPacket_intro packet0009_shape packet0009_cache packet0009_pair

theorem packet0010_membership : packet0010 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0010_shape : checkStripShape packet0010.row = true := by
  decide +kernel

private theorem packet0010_cache : checkStripCache packet0010 = true := by
  decide +kernel

private theorem packet0010_pair (i : Fin 7) : checkEdgePair packet0010 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0010_ok : checkStripPacket packet0010 = true :=
  checkStripPacket_intro packet0010_shape packet0010_cache packet0010_pair

theorem packet0011_membership : packet0011 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0011_shape : checkStripShape packet0011.row = true := by
  decide +kernel

private theorem packet0011_cache : checkStripCache packet0011 = true := by
  decide +kernel

private theorem packet0011_pair (i : Fin 7) : checkEdgePair packet0011 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0011_ok : checkStripPacket packet0011 = true :=
  checkStripPacket_intro packet0011_shape packet0011_cache packet0011_pair

theorem packet0012_membership : packet0012 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0012_shape : checkStripShape packet0012.row = true := by
  decide +kernel

private theorem packet0012_cache : checkStripCache packet0012 = true := by
  decide +kernel

private theorem packet0012_pair (i : Fin 7) : checkEdgePair packet0012 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0012_ok : checkStripPacket packet0012 = true :=
  checkStripPacket_intro packet0012_shape packet0012_cache packet0012_pair

theorem packet0013_membership : packet0013 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0013_shape : checkStripShape packet0013.row = true := by
  decide +kernel

private theorem packet0013_cache : checkStripCache packet0013 = true := by
  decide +kernel

private theorem packet0013_pair (i : Fin 7) : checkEdgePair packet0013 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0013_ok : checkStripPacket packet0013 = true :=
  checkStripPacket_intro packet0013_shape packet0013_cache packet0013_pair

theorem packet0014_membership : packet0014 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0014_shape : checkStripShape packet0014.row = true := by
  decide +kernel

private theorem packet0014_cache : checkStripCache packet0014 = true := by
  decide +kernel

private theorem packet0014_pair (i : Fin 7) : checkEdgePair packet0014 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0014_ok : checkStripPacket packet0014 = true :=
  checkStripPacket_intro packet0014_shape packet0014_cache packet0014_pair

theorem packet0015_membership : packet0015 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0015_shape : checkStripShape packet0015.row = true := by
  decide +kernel

private theorem packet0015_cache : checkStripCache packet0015 = true := by
  decide +kernel

private theorem packet0015_pair (i : Fin 7) : checkEdgePair packet0015 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0015_ok : checkStripPacket packet0015 = true :=
  checkStripPacket_intro packet0015_shape packet0015_cache packet0015_pair

theorem packet0016_membership : packet0016 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0016_shape : checkStripShape packet0016.row = true := by
  decide +kernel

private theorem packet0016_cache : checkStripCache packet0016 = true := by
  decide +kernel

private theorem packet0016_pair (i : Fin 7) : checkEdgePair packet0016 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0016_ok : checkStripPacket packet0016 = true :=
  checkStripPacket_intro packet0016_shape packet0016_cache packet0016_pair

theorem packet0017_membership : packet0017 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0017_shape : checkStripShape packet0017.row = true := by
  decide +kernel

private theorem packet0017_cache : checkStripCache packet0017 = true := by
  decide +kernel

private theorem packet0017_pair (i : Fin 7) : checkEdgePair packet0017 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0017_ok : checkStripPacket packet0017 = true :=
  checkStripPacket_intro packet0017_shape packet0017_cache packet0017_pair

theorem packet0018_membership : packet0018 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0018_shape : checkStripShape packet0018.row = true := by
  decide +kernel

private theorem packet0018_cache : checkStripCache packet0018 = true := by
  decide +kernel

private theorem packet0018_pair (i : Fin 7) : checkEdgePair packet0018 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0018_ok : checkStripPacket packet0018 = true :=
  checkStripPacket_intro packet0018_shape packet0018_cache packet0018_pair

theorem packet0019_membership : packet0019 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0019_shape : checkStripShape packet0019.row = true := by
  decide +kernel

private theorem packet0019_cache : checkStripCache packet0019 = true := by
  decide +kernel

private theorem packet0019_pair (i : Fin 7) : checkEdgePair packet0019 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0019_ok : checkStripPacket packet0019 = true :=
  checkStripPacket_intro packet0019_shape packet0019_cache packet0019_pair

theorem packet0020_membership : packet0020 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0020_shape : checkStripShape packet0020.row = true := by
  decide +kernel

private theorem packet0020_cache : checkStripCache packet0020 = true := by
  decide +kernel

private theorem packet0020_pair (i : Fin 7) : checkEdgePair packet0020 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0020_ok : checkStripPacket packet0020 = true :=
  checkStripPacket_intro packet0020_shape packet0020_cache packet0020_pair

theorem packet0021_membership : packet0021 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0021_shape : checkStripShape packet0021.row = true := by
  decide +kernel

private theorem packet0021_cache : checkStripCache packet0021 = true := by
  decide +kernel

private theorem packet0021_pair (i : Fin 7) : checkEdgePair packet0021 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0021_ok : checkStripPacket packet0021 = true :=
  checkStripPacket_intro packet0021_shape packet0021_cache packet0021_pair

theorem packet0022_membership : packet0022 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0022_shape : checkStripShape packet0022.row = true := by
  decide +kernel

private theorem packet0022_cache : checkStripCache packet0022 = true := by
  decide +kernel

private theorem packet0022_pair (i : Fin 7) : checkEdgePair packet0022 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0022_ok : checkStripPacket packet0022 = true :=
  checkStripPacket_intro packet0022_shape packet0022_cache packet0022_pair

theorem packet0023_membership : packet0023 ∈ packets000 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0023_shape : checkStripShape packet0023.row = true := by
  decide +kernel

private theorem packet0023_cache : checkStripCache packet0023 = true := by
  decide +kernel

private theorem packet0023_pair (i : Fin 7) : checkEdgePair packet0023 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0023_ok : checkStripPacket packet0023 = true :=
  checkStripPacket_intro packet0023_shape packet0023_cache packet0023_pair

theorem packets000_checked : packets000.all checkStripPacket = true := by
  simp only [packets000, List.all_cons, List.all_nil, Bool.true_and, packet0000_ok,
    packet0001_ok, packet0002_ok, packet0003_ok, packet0004_ok, packet0005_ok,
    packet0006_ok, packet0007_ok, packet0008_ok, packet0009_ok, packet0010_ok,
    packet0011_ok, packet0012_ok, packet0013_ok, packet0014_ok, packet0015_ok,
    packet0016_ok, packet0017_ok, packet0018_ok, packet0019_ok, packet0020_ok,
    packet0021_ok, packet0022_ok, packet0023_ok]

theorem packets000_valid : packets000.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
