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

def packet0192 : StripRowPacket :=
  ⟨⟨⟨8,3,6,16⟩,
    ![437,1351,2634,4114,5595,6875,7782],![468,1386,2665,4139,5612,6885,7787]⟩,
    ⟨-857730590280191886135698983,194183009848964498334919598080⟩,
    ⟨-3225775918183357273415087867,800687746179523786275634708480⟩⟩

def packet0193 : StripRowPacket :=
  ⟨⟨⟨8,3,6,17⟩,
    ![452,1370,2651,4127,5603,6879,7783],![482,1406,2683,4153,5621,6890,7789]⟩,
    ⟨-12948947083882514461548477207,3106928157583431973358713569280⟩,
    ⟨-1512825394763806442762849379,400343873089761893137817354240⟩⟩

def packet0194 : StripRowPacket :=
  ⟨⟨⟨8,2,6,18⟩,
    ![474,1395,2673,4144,5614,6885,7785],![505,1432,2706,4171,5632,6896,7791]⟩,
    ⟨-168423428527305575912119170225,43465042362249236127514539753472⟩,
    ⟨-10640011482355003796580157155269,3053170870647725012626542885994496⟩⟩

def packet0195 : StripRowPacket :=
  ⟨⟨⟨8,2,6,19⟩,
    ![488,1414,2690,4158,5623,6889,7786],![518,1450,2724,4185,5642,6901,7792]⟩,
    ⟨-24275656739731078871117351351,6686929594192190173463775346688⟩,
    ⟨-2472791909439229508144094587363,763292717661931253156635721498624⟩⟩

def packet0196 : StripRowPacket :=
  ⟨⟨⟨8,3,6,18⟩,
    ![467,1389,2668,4141,5612,6884,7785],![496,1424,2701,4167,5630,6894,7790]⟩,
    ⟨-6087102361640979372462885343,1553464078791715986679356784640⟩,
    ⟨-2825525660871868497636309649,800687746179523786275634708480⟩⟩

def packet0197 : StripRowPacket :=
  ⟨⟨⟨8,3,6,19⟩,
    ![480,1407,2685,4154,5621,6888,7786],![509,1443,2719,4181,5639,6899,7792]⟩,
    ⟨-2279892472536280605660612833,621385631516686394671742713856⟩,
    ⟨-131270026610806205487346027,40034387308976189313781735424⟩⟩

def packet0198 : StripRowPacket :=
  ⟨⟨⟨8,0,6,20⟩,
    ![518,1446,2718,4179,5637,6896,7789],![552,1485,2755,4209,5657,6908,7795]⟩,
    ⟨-16162125410558277,4867601235689082880⟩,
    ⟨-4229585912780274243,1445432673935107686400⟩⟩

def packet0199 : StripRowPacket :=
  ⟨⟨⟨8,0,6,21⟩,
    ![531,1464,2736,4193,5646,6901,7790],![563,1504,2774,4224,5668,6914,7796]⟩,
    ⟨-8592118901257614763,2784267906814155407360⟩,
    ⟨-1944749504400557213,722716336967553843200⟩⟩

def packet0200 : StripRowPacket :=
  ⟨⟨⟨8,1,6,20⟩,
    ![509,1439,2713,4176,5635,6895,7788],![540,1477,2749,4204,5655,6907,7794]⟩,
    ⟨-4742401861163097201178013834471,1414593814104236858535227043184640⟩,
    ⟨-3335173835491464744039560744683,1126740073671836700303787152834560⟩⟩

def packet0201 : StripRowPacket :=
  ⟨⟨⟨8,1,6,21⟩,
    ![521,1457,2731,4190,5644,6900,7790],![552,1495,2767,4219,5665,6912,7796]⟩,
    ⟨-88068587392860299827901937242611,28291876282084737170704540863692800⟩,
    ⟨-19918050533744427986741901311473,7323810478866938551974616493424640⟩⟩

def packet0202 : StripRowPacket :=
  ⟨⟨⟨8,0,6,22⟩,
    ![542,1482,2754,4208,5656,6906,7792],![574,1521,2792,4239,5678,6919,7798]⟩,
    ⟨-3969751033837947541,1392133953407077703680⟩,
    ⟨-3549412104821954609,1445432673935107686400⟩⟩

def packet0203 : StripRowPacket :=
  ⟨⟨⟨8,0,6,23⟩,
    ![553,1499,2772,4223,5666,6912,7794],![585,1539,2811,4255,5689,6925,7800]⟩,
    ⟨-7286885234094175401,2784267906814155407360⟩,
    ⟨-36469604555031759,16425371294717132800⟩⟩

def packet0204 : StripRowPacket :=
  ⟨⟨⟨8,1,6,22⟩,
    ![533,1475,2749,4205,5654,6905,7792],![562,1512,2786,4235,5676,6918,7798]⟩,
    ⟨-40644568781229327816121798897901,14145938141042368585352270431846400⟩,
    ⟨-36314942273588670274453315565013,14647620957733877103949232986849280⟩⟩

def packet0205 : StripRowPacket :=
  ⟨⟨⟨8,1,6,23⟩,
    ![543,1492,2767,4220,5664,6911,7793],![572,1529,2805,4251,5687,6924,7799]⟩,
    ⟨-74509687732057011436585258348993,28291876282084737170704540863692800⟩,
    ⟨-819844586992212114385570712677,366190523943346927598730824671232⟩⟩

def packet0206 : StripRowPacket :=
  ⟨⟨⟨8,2,6,20⟩,
    ![500,1432,2708,4172,5632,6894,7788],![530,1469,2743,4200,5652,6906,7794]⟩,
    ⟨-73580054544599224706203198669,21732521181124618063757269876736⟩,
    ⟨-9142323793158832268572599543635,3053170870647725012626542885994496⟩⟩

def packet0207 : StripRowPacket :=
  ⟨⟨⟨8,2,6,21⟩,
    ![513,1450,2726,4186,5642,6899,7790],![541,1487,2761,4215,5662,6911,7795]⟩,
    ⟨-273056898740289772325100021789,86930084724498472255029079506944⟩,
    ⟨-4196739974280373252284410368909,1526585435323862506313271442997248⟩⟩

def packet0208 : StripRowPacket :=
  ⟨⟨⟨8,3,6,20⟩,
    ![493,1426,2703,4168,5630,6893,7788],![521,1461,2737,4196,5649,6905,7793]⟩,
    ⟨-2656180000520211827920089411,776732039395857993339678392320⟩,
    ⟨-2425275403560379721857531431,800687746179523786275634708480⟩⟩

def packet0209 : StripRowPacket :=
  ⟨⟨⟨8,3,6,21⟩,
    ![505,1443,2721,4183,5640,6898,7789],![532,1479,2755,4211,5660,6910,7795]⟩,
    ⟨-9849977641480291595057651123,3106928157583431973358713569280⟩,
    ⟨-1112575137452317666984071161,400343873089761893137817354240⟩⟩

def packet0210 : StripRowPacket :=
  ⟨⟨⟨8,2,5,11⟩,
    ![524,1468,2744,4201,5652,6904,7791],![562,1521,2798,4247,5684,6923,7799]⟩,
    ⟨-125896789651091322912693624451,43465042362249236127514539753472⟩,
    ⟨-861974032420571872070157890773,381646358830965626578317860749312⟩⟩

def packet0211 : StripRowPacket :=
  ⟨⟨⟨8,3,5,11⟩,
    ![516,1461,2739,4198,5650,6903,7791],![552,1513,2792,4243,5682,6922,7799]⟩,
    ⟨-349047510803066764555190177,119497236830131998975335137280⟩,
    ⟨-228112502199143319773670513,100085968272440473284454338560⟩⟩

def packet0212 : StripRowPacket :=
  ⟨⟨⟨8,4,6,16⟩,
    ![431,1345,2629,4111,5592,6874,7782],![460,1380,2659,4135,5609,6884,7787]⟩,
    ⟨-46207087665390592061097932221,10337518226957049671839645972480⟩,
    ⟨-9613880892807953978824695963,2355502021952241394964461649920⟩⟩

def packet0213 : StripRowPacket :=
  ⟨⟨⟨8,4,6,17⟩,
    ![446,1364,2646,4124,5601,6878,7783],![475,1399,2677,4149,5618,6888,7788]⟩,
    ⟨-697314342557601769440485130277,165400291631312794749434335559680⟩,
    ⟨-4507277558948739383678250307,1177751010976120697482230824960⟩⟩

def packet0214 : StripRowPacket :=
  ⟨⟨⟨8,5,6,16⟩,
    ![425,1340,2624,4107,5590,6872,7781],![454,1373,2654,4131,5607,6882,7786]⟩,
    ⟨-114064005736325067298994257301,25223269307021176758716433244160⟩,
    ⟨-5997530113908687403717095155569,1450958070828439567023527350435840⟩⟩

def packet0215 : StripRowPacket :=
  ⟨⟨⟨8,5,6,17⟩,
    ![440,1359,2641,4120,5598,6877,7783],![468,1392,2672,4145,5616,6887,7788]⟩,
    ⟨-1720774355444161981603939289509,403572308912338828139462931906560⟩,
    ⟨-2811031281381608582941972158953,725479035414219783511763675217920⟩⟩

def packets008 : List StripRowPacket :=
  [packet0192, packet0193, packet0194, packet0195, packet0196, packet0197,
   packet0198, packet0199, packet0200, packet0201, packet0202, packet0203,
   packet0204, packet0205, packet0206, packet0207, packet0208, packet0209,
   packet0210, packet0211, packet0212, packet0213, packet0214, packet0215]

theorem packet0192_membership : packet0192 ∈ packets008 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0192_shape : checkStripShape packet0192.row = true := by
  decide +kernel

private theorem packet0192_cache : checkStripCache packet0192 = true := by
  decide +kernel

private theorem packet0192_pair (i : Fin 7) : checkEdgePair packet0192 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0192_ok : checkStripPacket packet0192 = true :=
  checkStripPacket_intro packet0192_shape packet0192_cache packet0192_pair

theorem packet0193_membership : packet0193 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0193_shape : checkStripShape packet0193.row = true := by
  decide +kernel

private theorem packet0193_cache : checkStripCache packet0193 = true := by
  decide +kernel

private theorem packet0193_pair (i : Fin 7) : checkEdgePair packet0193 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0193_ok : checkStripPacket packet0193 = true :=
  checkStripPacket_intro packet0193_shape packet0193_cache packet0193_pair

theorem packet0194_membership : packet0194 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0194_shape : checkStripShape packet0194.row = true := by
  decide +kernel

private theorem packet0194_cache : checkStripCache packet0194 = true := by
  decide +kernel

private theorem packet0194_pair (i : Fin 7) : checkEdgePair packet0194 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0194_ok : checkStripPacket packet0194 = true :=
  checkStripPacket_intro packet0194_shape packet0194_cache packet0194_pair

theorem packet0195_membership : packet0195 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0195_shape : checkStripShape packet0195.row = true := by
  decide +kernel

private theorem packet0195_cache : checkStripCache packet0195 = true := by
  decide +kernel

private theorem packet0195_pair (i : Fin 7) : checkEdgePair packet0195 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0195_ok : checkStripPacket packet0195 = true :=
  checkStripPacket_intro packet0195_shape packet0195_cache packet0195_pair

theorem packet0196_membership : packet0196 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0196_shape : checkStripShape packet0196.row = true := by
  decide +kernel

private theorem packet0196_cache : checkStripCache packet0196 = true := by
  decide +kernel

private theorem packet0196_pair (i : Fin 7) : checkEdgePair packet0196 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0196_ok : checkStripPacket packet0196 = true :=
  checkStripPacket_intro packet0196_shape packet0196_cache packet0196_pair

theorem packet0197_membership : packet0197 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0197_shape : checkStripShape packet0197.row = true := by
  decide +kernel

private theorem packet0197_cache : checkStripCache packet0197 = true := by
  decide +kernel

private theorem packet0197_pair (i : Fin 7) : checkEdgePair packet0197 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0197_ok : checkStripPacket packet0197 = true :=
  checkStripPacket_intro packet0197_shape packet0197_cache packet0197_pair

theorem packet0198_membership : packet0198 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0198_shape : checkStripShape packet0198.row = true := by
  decide +kernel

private theorem packet0198_cache : checkStripCache packet0198 = true := by
  decide +kernel

private theorem packet0198_pair (i : Fin 7) : checkEdgePair packet0198 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0198_ok : checkStripPacket packet0198 = true :=
  checkStripPacket_intro packet0198_shape packet0198_cache packet0198_pair

theorem packet0199_membership : packet0199 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0199_shape : checkStripShape packet0199.row = true := by
  decide +kernel

private theorem packet0199_cache : checkStripCache packet0199 = true := by
  decide +kernel

private theorem packet0199_pair (i : Fin 7) : checkEdgePair packet0199 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0199_ok : checkStripPacket packet0199 = true :=
  checkStripPacket_intro packet0199_shape packet0199_cache packet0199_pair

theorem packet0200_membership : packet0200 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0200_shape : checkStripShape packet0200.row = true := by
  decide +kernel

private theorem packet0200_cache : checkStripCache packet0200 = true := by
  decide +kernel

private theorem packet0200_pair (i : Fin 7) : checkEdgePair packet0200 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0200_ok : checkStripPacket packet0200 = true :=
  checkStripPacket_intro packet0200_shape packet0200_cache packet0200_pair

theorem packet0201_membership : packet0201 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0201_shape : checkStripShape packet0201.row = true := by
  decide +kernel

private theorem packet0201_cache : checkStripCache packet0201 = true := by
  decide +kernel

private theorem packet0201_pair (i : Fin 7) : checkEdgePair packet0201 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0201_ok : checkStripPacket packet0201 = true :=
  checkStripPacket_intro packet0201_shape packet0201_cache packet0201_pair

theorem packet0202_membership : packet0202 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0202_shape : checkStripShape packet0202.row = true := by
  decide +kernel

private theorem packet0202_cache : checkStripCache packet0202 = true := by
  decide +kernel

private theorem packet0202_pair (i : Fin 7) : checkEdgePair packet0202 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0202_ok : checkStripPacket packet0202 = true :=
  checkStripPacket_intro packet0202_shape packet0202_cache packet0202_pair

theorem packet0203_membership : packet0203 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0203_shape : checkStripShape packet0203.row = true := by
  decide +kernel

private theorem packet0203_cache : checkStripCache packet0203 = true := by
  decide +kernel

private theorem packet0203_pair (i : Fin 7) : checkEdgePair packet0203 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0203_ok : checkStripPacket packet0203 = true :=
  checkStripPacket_intro packet0203_shape packet0203_cache packet0203_pair

theorem packet0204_membership : packet0204 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0204_shape : checkStripShape packet0204.row = true := by
  decide +kernel

private theorem packet0204_cache : checkStripCache packet0204 = true := by
  decide +kernel

private theorem packet0204_pair (i : Fin 7) : checkEdgePair packet0204 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0204_ok : checkStripPacket packet0204 = true :=
  checkStripPacket_intro packet0204_shape packet0204_cache packet0204_pair

theorem packet0205_membership : packet0205 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0205_shape : checkStripShape packet0205.row = true := by
  decide +kernel

private theorem packet0205_cache : checkStripCache packet0205 = true := by
  decide +kernel

private theorem packet0205_pair (i : Fin 7) : checkEdgePair packet0205 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0205_ok : checkStripPacket packet0205 = true :=
  checkStripPacket_intro packet0205_shape packet0205_cache packet0205_pair

theorem packet0206_membership : packet0206 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0206_shape : checkStripShape packet0206.row = true := by
  decide +kernel

private theorem packet0206_cache : checkStripCache packet0206 = true := by
  decide +kernel

private theorem packet0206_pair (i : Fin 7) : checkEdgePair packet0206 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0206_ok : checkStripPacket packet0206 = true :=
  checkStripPacket_intro packet0206_shape packet0206_cache packet0206_pair

theorem packet0207_membership : packet0207 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0207_shape : checkStripShape packet0207.row = true := by
  decide +kernel

private theorem packet0207_cache : checkStripCache packet0207 = true := by
  decide +kernel

private theorem packet0207_pair (i : Fin 7) : checkEdgePair packet0207 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0207_ok : checkStripPacket packet0207 = true :=
  checkStripPacket_intro packet0207_shape packet0207_cache packet0207_pair

theorem packet0208_membership : packet0208 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0208_shape : checkStripShape packet0208.row = true := by
  decide +kernel

private theorem packet0208_cache : checkStripCache packet0208 = true := by
  decide +kernel

private theorem packet0208_pair (i : Fin 7) : checkEdgePair packet0208 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0208_ok : checkStripPacket packet0208 = true :=
  checkStripPacket_intro packet0208_shape packet0208_cache packet0208_pair

theorem packet0209_membership : packet0209 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0209_shape : checkStripShape packet0209.row = true := by
  decide +kernel

private theorem packet0209_cache : checkStripCache packet0209 = true := by
  decide +kernel

private theorem packet0209_pair (i : Fin 7) : checkEdgePair packet0209 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0209_ok : checkStripPacket packet0209 = true :=
  checkStripPacket_intro packet0209_shape packet0209_cache packet0209_pair

theorem packet0210_membership : packet0210 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0210_shape : checkStripShape packet0210.row = true := by
  decide +kernel

private theorem packet0210_cache : checkStripCache packet0210 = true := by
  decide +kernel

private theorem packet0210_pair (i : Fin 7) : checkEdgePair packet0210 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0210_ok : checkStripPacket packet0210 = true :=
  checkStripPacket_intro packet0210_shape packet0210_cache packet0210_pair

theorem packet0211_membership : packet0211 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0211_shape : checkStripShape packet0211.row = true := by
  decide +kernel

private theorem packet0211_cache : checkStripCache packet0211 = true := by
  decide +kernel

private theorem packet0211_pair (i : Fin 7) : checkEdgePair packet0211 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0211_ok : checkStripPacket packet0211 = true :=
  checkStripPacket_intro packet0211_shape packet0211_cache packet0211_pair

theorem packet0212_membership : packet0212 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0212_shape : checkStripShape packet0212.row = true := by
  decide +kernel

private theorem packet0212_cache : checkStripCache packet0212 = true := by
  decide +kernel

private theorem packet0212_pair (i : Fin 7) : checkEdgePair packet0212 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0212_ok : checkStripPacket packet0212 = true :=
  checkStripPacket_intro packet0212_shape packet0212_cache packet0212_pair

theorem packet0213_membership : packet0213 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0213_shape : checkStripShape packet0213.row = true := by
  decide +kernel

private theorem packet0213_cache : checkStripCache packet0213 = true := by
  decide +kernel

private theorem packet0213_pair (i : Fin 7) : checkEdgePair packet0213 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0213_ok : checkStripPacket packet0213 = true :=
  checkStripPacket_intro packet0213_shape packet0213_cache packet0213_pair

theorem packet0214_membership : packet0214 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0214_shape : checkStripShape packet0214.row = true := by
  decide +kernel

private theorem packet0214_cache : checkStripCache packet0214 = true := by
  decide +kernel

private theorem packet0214_pair (i : Fin 7) : checkEdgePair packet0214 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0214_ok : checkStripPacket packet0214 = true :=
  checkStripPacket_intro packet0214_shape packet0214_cache packet0214_pair

theorem packet0215_membership : packet0215 ∈ packets008 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0215_shape : checkStripShape packet0215.row = true := by
  decide +kernel

private theorem packet0215_cache : checkStripCache packet0215 = true := by
  decide +kernel

private theorem packet0215_pair (i : Fin 7) : checkEdgePair packet0215 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0215_ok : checkStripPacket packet0215 = true :=
  checkStripPacket_intro packet0215_shape packet0215_cache packet0215_pair

theorem packets008_checked : packets008.all checkStripPacket = true := by
  simp only [packets008, List.all_cons, List.all_nil, Bool.true_and, packet0192_ok,
    packet0193_ok, packet0194_ok, packet0195_ok, packet0196_ok, packet0197_ok,
    packet0198_ok, packet0199_ok, packet0200_ok, packet0201_ok, packet0202_ok,
    packet0203_ok, packet0204_ok, packet0205_ok, packet0206_ok, packet0207_ok,
    packet0208_ok, packet0209_ok, packet0210_ok, packet0211_ok, packet0212_ok,
    packet0213_ok, packet0214_ok, packet0215_ok]

theorem packets008_valid : packets008.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
