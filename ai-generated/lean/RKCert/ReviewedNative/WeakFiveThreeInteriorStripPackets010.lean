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

def packet0240 : StripRowPacket :=
  ⟨⟨⟨8,1,5,13⟩,
    ![572,1541,2822,4267,5697,6929,7799],![607,1593,2879,4318,5735,6950,7808]⟩,
    ⟨-27085669120426039424805120004283,14145938141042368585352270431846400⟩,
    ⟨-4677287076021935444825220068837,3661905239433469275987308246712320⟩⟩

def packet0241 : StripRowPacket :=
  ⟨⟨⟨8,2,5,12⟩,
    ![544,1501,2780,4232,5673,6915,7795],![580,1553,2836,4280,5707,6935,7803]⟩,
    ⟨-26158367553246049103245212891,10866260590562309031878634938368⟩,
    ⟨-2699052285084201724276852757275,1526585435323862506313271442997248⟩⟩

def packet0242 : StripRowPacket :=
  ⟨⟨⟨8,3,5,12⟩,
    ![536,1495,2775,4228,5671,6914,7794],![570,1545,2830,4276,5705,6934,7803]⟩,
    ⟨-188143763991965611129738289,77673203939585799333967839232⟩,
    ⟨-37490783165306783747646997,21070730162619047007253544960⟩⟩

def packet0243 : StripRowPacket :=
  ⟨⟨⟨8,2,5,13⟩,
    ![562,1533,2816,4264,5695,6928,7799],![595,1584,2873,4314,5733,6949,7808]⟩,
    ⟨-4387902672361951048066740983,2287633808539433480395502092288⟩,
    ⟨-975104220243057980136536975729,763292717661931253156635721498624⟩⟩

def packet0244 : StripRowPacket :=
  ⟨⟨⟨8,3,5,13⟩,
    ![553,1526,2811,4260,5693,6927,7798],![585,1575,2866,4310,5730,6948,7807]⟩,
    ⟨-2988132919238756505972059259,1553464078791715986679356784640⟩,
    ⟨-256099875742542251657951917,200171936544880946568908677120⟩⟩

def packet0245 : StripRowPacket :=
  ⟨⟨⟨8,0,5,14⟩,
    ![598,1579,2863,4303,5723,6942,7803],![634,1631,2923,4358,5764,6967,7813]⟩,
    ⟨-1005950266546394249,696066976703538851840⟩,
    ⟨-116880377696783589,144543267393510768640⟩⟩

def packet0246 : StripRowPacket :=
  ⟨⟨⟨8,1,5,14⟩,
    ![587,1571,2858,4300,5721,6942,7803],![621,1621,2916,4354,5762,6965,7813]⟩,
    ⟨-781008434231707508813337713749,544074543886244945590471939686400⟩,
    ⟨-5833415358143685190619953079741,7323810478866938551974616493424640⟩⟩

def packet0247 : StripRowPacket :=
  ⟨⟨⟨7,0,5,15⟩,
    ![599,1594,2887,4327,5742,6953,7807],![649,1663,2966,4402,5799,6987,7820]⟩,
    ⟨-12027006719231057,11464625374655737856⟩,
    ⟨-8584806594757,35016229887961088⟩⟩

def packet0248 : StripRowPacket :=
  ⟨⟨⟨7,1,5,14⟩,
    ![567,1552,2842,4288,5714,6938,7802],![611,1616,2915,4355,5764,6967,7814]⟩,
    ⟨-8377881886827082816139363,5579603720678195724620349440⟩,
    ⟨-157544556812543959605026137,222212768437402460489915613184⟩⟩

def packet0249 : StripRowPacket :=
  ⟨⟨⟨7,1,5,15⟩,
    ![581,1580,2877,4322,5739,6952,7807],![623,1642,2950,4392,5793,6984,7819]⟩,
    ⟨-123767565915880656921979129,122751281854920305941647687680⟩,
    ⟨-1139090151406527907219751,5341653087437559146392202240⟩⟩

def packet0250 : StripRowPacket :=
  ⟨⟨⟨8,4,5,12⟩,
    ![528,1488,2770,4225,5669,6913,7794],![561,1538,2824,4272,5703,6933,7802]⟩,
    ⟨-50415115242133480585114079183,20675036453914099343679291944960⟩,
    ⟨-2109974459306838537805468911,1177751010976120697482230824960⟩⟩

def packet0251 : StripRowPacket :=
  ⟨⟨⟨8,5,5,12⟩,
    ![522,1482,2765,4222,5667,6912,7794],![553,1530,2818,4268,5700,6932,7802]⟩,
    ⟨-2252332275192927989418539769,917209792982588245771506663424⟩,
    ⟨-1309161076799727631609368808301,725479035414219783511763675217920⟩⟩

def packet0252 : StripRowPacket :=
  ⟨⟨⟨7,2,5,13⟩,
    ![537,1510,2797,4250,5687,6923,7797],![578,1571,2865,4311,5731,6949,7808]⟩,
    ⟨-49392797492131529512734241,24654281127306123084914769920⟩,
    ⟨-1206335680253452024793983,991831065336201015636705280⟩⟩

def packet0253 : StripRowPacket :=
  ⟨⟨⟨7,3,5,12⟩,
    ![508,1467,2753,4212,5661,6909,7793],![547,1527,2817,4268,5701,6932,7802]⟩,
    ⟨-2030188611412758511601543,797174800093391539335127040⟩,
    ⟨-25075949174409344896640117,14238415818334798793222840320⟩⟩

def packet0254 : StripRowPacket :=
  ⟨⟨⟨7,3,5,13⟩,
    ![524,1498,2789,4244,5683,6922,7797],![562,1556,2854,4303,5726,6946,7807]⟩,
    ⟨-6434646126110233635420233,3188699200373566157340508160⟩,
    ⟨-8762546812398178514103647,7119207909167399396611420160⟩⟩

def packet0255 : StripRowPacket :=
  ⟨⟨⟨7,2,5,14⟩,
    ![552,1539,2833,4283,5711,6936,7802],![591,1599,2902,4346,5759,6964,7813]⟩,
    ⟨-202277374822086752291792033,135598546200183676967031234560⟩,
    ⟨-1393833149361996788534983,1983662130672402031273410560⟩⟩

def packet0256 : StripRowPacket :=
  ⟨⟨⟨7,2,5,15⟩,
    ![565,1567,2868,4316,5736,6951,7806],![603,1625,2937,4383,5788,6981,7819]⟩,
    ⟨-20445286682684629579007037,20861314800028257994927882240⟩,
    ⟨-4687436727713619093525,24795776633405025390917632⟩⟩

def packet0257 : StripRowPacket :=
  ⟨⟨⟨7,3,5,14⟩,
    ![539,1528,2824,4277,5707,6935,7801],![575,1584,2890,4338,5754,6962,7812]⟩,
    ⟨-182636069483439739401319,122642276937444852205404160⟩,
    ⟨-9974238075183369159774471,14238415818334798793222840320⟩⟩

def packet0258 : StripRowPacket :=
  ⟨⟨⟨7,3,5,15⟩,
    ![552,1555,2859,4311,5733,6949,7806],![586,1609,2925,4374,5783,6979,7818]⟩,
    ⟨-612485897405726562689671,637739840074713231468101632⟩,
    ⟨-151461407848148830708853,889900988645924924576427520⟩⟩

def packet0259 : StripRowPacket :=
  ⟨⟨⟨8,8,5,8⟩,
    ![412,1324,2610,4097,5583,6869,7780],![451,1375,2657,4134,5608,6883,7787]⟩,
    ⟨-23538921505834049275668733,5033735549442181840785978880⟩,
    ⟨-2646320399218480200585480851,659193849229771328726436085760⟩⟩

def packet0260 : StripRowPacket :=
  ⟨⟨⟨8,9,5,8⟩,
    ![408,1319,2606,4093,5581,6868,7780],![446,1369,2652,4130,5606,6882,7786]⟩,
    ⟨-102667155465240257502803288531,21721586848104833737257390202880⟩,
    ⟨-6128447512519853962685813929707,1509506747372340137293148841410560⟩⟩

def packet0261 : StripRowPacket :=
  ⟨⟨⟨8,8,5,9⟩,
    ![440,1361,2645,4123,5601,6878,7783],![476,1411,2693,4162,5628,6893,7790]⟩,
    ⟨-166513477824760361165465643,40269884395537454726287831040⟩,
    ⟨-228906923757187367771570363,65919384922977132872643608576⟩⟩

def packet0262 : StripRowPacket :=
  ⟨⟨⟨8,9,5,9⟩,
    ![436,1356,2640,4120,5599,6877,7783],![471,1406,2688,4159,5625,6892,7789]⟩,
    ⟨-725929442040992021148506054699,173772694784838669898059121623040⟩,
    ⟨-2649386650699748572697971818079,754753373686170068646574420705280⟩⟩

def packet0263 : StripRowPacket :=
  ⟨⟨⟨8,10,5,8⟩,
    ![404,1315,2602,4090,5579,6867,7779],![442,1364,2648,4127,5604,6881,7786]⟩,
    ⟨-12797111090367170958725511361127,2679344324801337630033903484006400⟩,
    ⟨-10567770719542227536611336664981,2574529806748077066002418778439680⟩⟩

def packets010 : List StripRowPacket :=
  [packet0240, packet0241, packet0242, packet0243, packet0244, packet0245,
   packet0246, packet0247, packet0248, packet0249, packet0250, packet0251,
   packet0252, packet0253, packet0254, packet0255, packet0256, packet0257,
   packet0258, packet0259, packet0260, packet0261, packet0262, packet0263]

theorem packet0240_membership : packet0240 ∈ packets010 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0240_shape : checkStripShape packet0240.row = true := by
  decide +kernel

private theorem packet0240_cache : checkStripCache packet0240 = true := by
  decide +kernel

private theorem packet0240_pair (i : Fin 7) : checkEdgePair packet0240 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0240_ok : checkStripPacket packet0240 = true :=
  checkStripPacket_intro packet0240_shape packet0240_cache packet0240_pair

theorem packet0241_membership : packet0241 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0241_shape : checkStripShape packet0241.row = true := by
  decide +kernel

private theorem packet0241_cache : checkStripCache packet0241 = true := by
  decide +kernel

private theorem packet0241_pair (i : Fin 7) : checkEdgePair packet0241 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0241_ok : checkStripPacket packet0241 = true :=
  checkStripPacket_intro packet0241_shape packet0241_cache packet0241_pair

theorem packet0242_membership : packet0242 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0242_shape : checkStripShape packet0242.row = true := by
  decide +kernel

private theorem packet0242_cache : checkStripCache packet0242 = true := by
  decide +kernel

private theorem packet0242_pair (i : Fin 7) : checkEdgePair packet0242 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0242_ok : checkStripPacket packet0242 = true :=
  checkStripPacket_intro packet0242_shape packet0242_cache packet0242_pair

theorem packet0243_membership : packet0243 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0243_shape : checkStripShape packet0243.row = true := by
  decide +kernel

private theorem packet0243_cache : checkStripCache packet0243 = true := by
  decide +kernel

private theorem packet0243_pair (i : Fin 7) : checkEdgePair packet0243 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0243_ok : checkStripPacket packet0243 = true :=
  checkStripPacket_intro packet0243_shape packet0243_cache packet0243_pair

theorem packet0244_membership : packet0244 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0244_shape : checkStripShape packet0244.row = true := by
  decide +kernel

private theorem packet0244_cache : checkStripCache packet0244 = true := by
  decide +kernel

private theorem packet0244_pair (i : Fin 7) : checkEdgePair packet0244 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0244_ok : checkStripPacket packet0244 = true :=
  checkStripPacket_intro packet0244_shape packet0244_cache packet0244_pair

theorem packet0245_membership : packet0245 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0245_shape : checkStripShape packet0245.row = true := by
  decide +kernel

private theorem packet0245_cache : checkStripCache packet0245 = true := by
  decide +kernel

private theorem packet0245_pair (i : Fin 7) : checkEdgePair packet0245 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0245_ok : checkStripPacket packet0245 = true :=
  checkStripPacket_intro packet0245_shape packet0245_cache packet0245_pair

theorem packet0246_membership : packet0246 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0246_shape : checkStripShape packet0246.row = true := by
  decide +kernel

private theorem packet0246_cache : checkStripCache packet0246 = true := by
  decide +kernel

private theorem packet0246_pair (i : Fin 7) : checkEdgePair packet0246 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0246_ok : checkStripPacket packet0246 = true :=
  checkStripPacket_intro packet0246_shape packet0246_cache packet0246_pair

theorem packet0247_membership : packet0247 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0247_shape : checkStripShape packet0247.row = true := by
  decide +kernel

private theorem packet0247_cache : checkStripCache packet0247 = true := by
  decide +kernel

private theorem packet0247_pair (i : Fin 7) : checkEdgePair packet0247 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0247_ok : checkStripPacket packet0247 = true :=
  checkStripPacket_intro packet0247_shape packet0247_cache packet0247_pair

theorem packet0248_membership : packet0248 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0248_shape : checkStripShape packet0248.row = true := by
  decide +kernel

private theorem packet0248_cache : checkStripCache packet0248 = true := by
  decide +kernel

private theorem packet0248_pair (i : Fin 7) : checkEdgePair packet0248 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0248_ok : checkStripPacket packet0248 = true :=
  checkStripPacket_intro packet0248_shape packet0248_cache packet0248_pair

theorem packet0249_membership : packet0249 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0249_shape : checkStripShape packet0249.row = true := by
  decide +kernel

private theorem packet0249_cache : checkStripCache packet0249 = true := by
  decide +kernel

private theorem packet0249_pair (i : Fin 7) : checkEdgePair packet0249 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0249_ok : checkStripPacket packet0249 = true :=
  checkStripPacket_intro packet0249_shape packet0249_cache packet0249_pair

theorem packet0250_membership : packet0250 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0250_shape : checkStripShape packet0250.row = true := by
  decide +kernel

private theorem packet0250_cache : checkStripCache packet0250 = true := by
  decide +kernel

private theorem packet0250_pair (i : Fin 7) : checkEdgePair packet0250 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0250_ok : checkStripPacket packet0250 = true :=
  checkStripPacket_intro packet0250_shape packet0250_cache packet0250_pair

theorem packet0251_membership : packet0251 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0251_shape : checkStripShape packet0251.row = true := by
  decide +kernel

private theorem packet0251_cache : checkStripCache packet0251 = true := by
  decide +kernel

private theorem packet0251_pair (i : Fin 7) : checkEdgePair packet0251 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0251_ok : checkStripPacket packet0251 = true :=
  checkStripPacket_intro packet0251_shape packet0251_cache packet0251_pair

theorem packet0252_membership : packet0252 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0252_shape : checkStripShape packet0252.row = true := by
  decide +kernel

private theorem packet0252_cache : checkStripCache packet0252 = true := by
  decide +kernel

private theorem packet0252_pair (i : Fin 7) : checkEdgePair packet0252 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0252_ok : checkStripPacket packet0252 = true :=
  checkStripPacket_intro packet0252_shape packet0252_cache packet0252_pair

theorem packet0253_membership : packet0253 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0253_shape : checkStripShape packet0253.row = true := by
  decide +kernel

private theorem packet0253_cache : checkStripCache packet0253 = true := by
  decide +kernel

private theorem packet0253_pair (i : Fin 7) : checkEdgePair packet0253 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0253_ok : checkStripPacket packet0253 = true :=
  checkStripPacket_intro packet0253_shape packet0253_cache packet0253_pair

theorem packet0254_membership : packet0254 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0254_shape : checkStripShape packet0254.row = true := by
  decide +kernel

private theorem packet0254_cache : checkStripCache packet0254 = true := by
  decide +kernel

private theorem packet0254_pair (i : Fin 7) : checkEdgePair packet0254 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0254_ok : checkStripPacket packet0254 = true :=
  checkStripPacket_intro packet0254_shape packet0254_cache packet0254_pair

theorem packet0255_membership : packet0255 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0255_shape : checkStripShape packet0255.row = true := by
  decide +kernel

private theorem packet0255_cache : checkStripCache packet0255 = true := by
  decide +kernel

private theorem packet0255_pair (i : Fin 7) : checkEdgePair packet0255 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0255_ok : checkStripPacket packet0255 = true :=
  checkStripPacket_intro packet0255_shape packet0255_cache packet0255_pair

theorem packet0256_membership : packet0256 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0256_shape : checkStripShape packet0256.row = true := by
  decide +kernel

private theorem packet0256_cache : checkStripCache packet0256 = true := by
  decide +kernel

private theorem packet0256_pair (i : Fin 7) : checkEdgePair packet0256 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0256_ok : checkStripPacket packet0256 = true :=
  checkStripPacket_intro packet0256_shape packet0256_cache packet0256_pair

theorem packet0257_membership : packet0257 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0257_shape : checkStripShape packet0257.row = true := by
  decide +kernel

private theorem packet0257_cache : checkStripCache packet0257 = true := by
  decide +kernel

private theorem packet0257_pair (i : Fin 7) : checkEdgePair packet0257 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0257_ok : checkStripPacket packet0257 = true :=
  checkStripPacket_intro packet0257_shape packet0257_cache packet0257_pair

theorem packet0258_membership : packet0258 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0258_shape : checkStripShape packet0258.row = true := by
  decide +kernel

private theorem packet0258_cache : checkStripCache packet0258 = true := by
  decide +kernel

private theorem packet0258_pair (i : Fin 7) : checkEdgePair packet0258 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0258_ok : checkStripPacket packet0258 = true :=
  checkStripPacket_intro packet0258_shape packet0258_cache packet0258_pair

theorem packet0259_membership : packet0259 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0259_shape : checkStripShape packet0259.row = true := by
  decide +kernel

private theorem packet0259_cache : checkStripCache packet0259 = true := by
  decide +kernel

private theorem packet0259_pair (i : Fin 7) : checkEdgePair packet0259 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0259_ok : checkStripPacket packet0259 = true :=
  checkStripPacket_intro packet0259_shape packet0259_cache packet0259_pair

theorem packet0260_membership : packet0260 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0260_shape : checkStripShape packet0260.row = true := by
  decide +kernel

private theorem packet0260_cache : checkStripCache packet0260 = true := by
  decide +kernel

private theorem packet0260_pair (i : Fin 7) : checkEdgePair packet0260 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0260_ok : checkStripPacket packet0260 = true :=
  checkStripPacket_intro packet0260_shape packet0260_cache packet0260_pair

theorem packet0261_membership : packet0261 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0261_shape : checkStripShape packet0261.row = true := by
  decide +kernel

private theorem packet0261_cache : checkStripCache packet0261 = true := by
  decide +kernel

private theorem packet0261_pair (i : Fin 7) : checkEdgePair packet0261 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0261_ok : checkStripPacket packet0261 = true :=
  checkStripPacket_intro packet0261_shape packet0261_cache packet0261_pair

theorem packet0262_membership : packet0262 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0262_shape : checkStripShape packet0262.row = true := by
  decide +kernel

private theorem packet0262_cache : checkStripCache packet0262 = true := by
  decide +kernel

private theorem packet0262_pair (i : Fin 7) : checkEdgePair packet0262 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0262_ok : checkStripPacket packet0262 = true :=
  checkStripPacket_intro packet0262_shape packet0262_cache packet0262_pair

theorem packet0263_membership : packet0263 ∈ packets010 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0263_shape : checkStripShape packet0263.row = true := by
  decide +kernel

private theorem packet0263_cache : checkStripCache packet0263 = true := by
  decide +kernel

private theorem packet0263_pair (i : Fin 7) : checkEdgePair packet0263 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0263_ok : checkStripPacket packet0263 = true :=
  checkStripPacket_intro packet0263_shape packet0263_cache packet0263_pair

theorem packets010_checked : packets010.all checkStripPacket = true := by
  simp only [packets010, List.all_cons, List.all_nil, Bool.true_and, packet0240_ok,
    packet0241_ok, packet0242_ok, packet0243_ok, packet0244_ok, packet0245_ok,
    packet0246_ok, packet0247_ok, packet0248_ok, packet0249_ok, packet0250_ok,
    packet0251_ok, packet0252_ok, packet0253_ok, packet0254_ok, packet0255_ok,
    packet0256_ok, packet0257_ok, packet0258_ok, packet0259_ok, packet0260_ok,
    packet0261_ok, packet0262_ok, packet0263_ok]

theorem packets010_valid : packets010.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
