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

def packet0432 : StripRowPacket :=
  ⟨⟨⟨7,0,5,23⟩,
    ![670,1757,3129,4605,5994,7123,7872],![711,1812,3199,4688,6081,7197,7910]⟩,
    ⟨31360857815547319,11464625374655737856⟩,
    ⟨211304003519559,59258235195011072⟩⟩

def packet0433 : StripRowPacket :=
  ⟨⟨⟨7,1,4,11⟩,
    ![644,1725,3092,4566,5957,7096,7860],![685,1789,3181,4675,6073,7193,7909]⟩,
    ⟨30005328324432549830962887,12275128185492030594164768768⟩,
    ⟨521175688633592267735708951,138882980273376537806197258240⟩⟩

def packet0434 : StripRowPacket :=
  ⟨⟨⟨7,2,4,10⟩,
    ![614,1677,3028,4492,5887,7045,7840],![652,1742,3118,4599,5992,7124,7875]⟩,
    ⟨107010346742866603938842861,67799273100091838483515617280⟩,
    ⟨2869017164326177019417949,991831065336201015636705280⟩⟩

def packet0435 : StripRowPacket :=
  ⟨⟨⟨7,3,4,10⟩,
    ![599,1664,3019,4487,5884,7045,7840],![635,1725,3105,4590,5987,7122,7874]⟩,
    ⟨268405605533768462074067,159434960018678307867025408⟩,
    ⟨4288175077210754591925529,1423841581833479879322284032⟩⟩

def packet0436 : StripRowPacket :=
  ⟨⟨⟨7,2,4,11⟩,
    ![627,1710,3082,4561,5955,7096,7861],![663,1769,3165,4664,6066,7189,7908]⟩,
    ⟨352786716255006527934178307,135598546200183676967031234560⟩,
    ⟨971963843867771070117733,247957766334050253909176320⟩⟩

def packet0437 : StripRowPacket :=
  ⟨⟨⟨7,3,4,11⟩,
    ![613,1697,3072,4555,5953,7096,7861],![645,1752,3152,4654,6060,7186,7907]⟩,
    ⟨4370164374878485031726609,1594349600186783078670254080⟩,
    ⟨557533287224360785155009,136907844407065373011758080⟩⟩

def packet0438 : StripRowPacket :=
  ⟨⟨⟨7,4,4,8⟩,
    ![553,1569,2885,4340,5757,6964,7811],![592,1641,2980,4440,5841,7016,7831]⟩,
    ⟨-25278555635609939980665,62885425927783485455576576⟩,
    ⟨33511489034368044617285725,35768134032456914063407038464⟩⟩

def packet0439 : StripRowPacket :=
  ⟨⟨⟨7,5,4,8⟩,
    ![543,1559,2878,4335,5754,6962,7810],![579,1628,2970,4433,5837,7014,7830]⟩,
    ⟨-9916495419714018813956015,26263682434622256812300130304⟩,
    ⟨4817549440297780740154855,4921056517497656095022374912⟩⟩

def packet0440 : StripRowPacket :=
  ⟨⟨⟨7,4,4,9⟩,
    ![572,1614,2950,4411,5817,7000,7824],![607,1678,3040,4512,5909,7063,7849]⟩,
    ⟨345933058372207286970931,503083407422267883644612608⟩,
    ⟨36287039981761514067986057,17884067016228457031703519232⟩⟩

def packet0441 : StripRowPacket :=
  ⟨⟨⟨7,5,4,9⟩,
    ![562,1604,2942,4406,5814,6999,7823],![594,1666,3029,4505,5905,7061,7849]⟩,
    ⟨155970275731291962428044473,210109459476978054498401042432⟩,
    ⟨5169425487945584654825419,2460528258748828047511187456⟩⟩

def packet0442 : StripRowPacket :=
  ⟨⟨⟨7,6,4,8⟩,
    ![534,1550,2870,4330,5751,6961,7810],![569,1617,2960,4426,5833,7012,7830]⟩,
    ⟨-402610162518813377400491,1127338092945478995608867840⟩,
    ⟨323822275980878083330903581,318235717355651324420587601920⟩⟩

def packet0443 : StripRowPacket :=
  ⟨⟨⟨7,7,4,8⟩,
    ![527,1541,2863,4325,5748,6960,7810],![559,1606,2952,4420,5829,7010,7829]⟩,
    ⟨-155629065888956079051,458069415234513348012032⟩,
    ⟨9752441121068738801,9258372392958366226120⟩⟩

def packet0444 : StripRowPacket :=
  ⟨⟨⟨7,6,4,9⟩,
    ![553,1594,2935,4401,5811,6998,7823],![584,1654,3020,4498,5901,7059,7848]⟩,
    ⟨7139269815302254673471333,9018704743563831964870942720⟩,
    ⟨68994731289141952229360885,31823571735565132442058760192⟩⟩

def packet0445 : StripRowPacket :=
  ⟨⟨⟨7,7,4,9⟩,
    ![545,1585,2928,4396,5809,6997,7823],![574,1643,3011,4492,5897,7057,7847]⟩,
    ⟨15328586741545652272337,18322776609380533920481280⟩,
    ⟨330514883905170879929,148133958287333859617920⟩⟩

def packet0446 : StripRowPacket :=
  ⟨⟨⟨7,4,4,10⟩,
    ![587,1652,3010,4481,5882,7044,7840],![620,1710,3093,4581,5982,7119,7873]⟩,
    ⟨447047280914647046893591,251541703711133941822306304⟩,
    ⟨111636670892678011654658503,35768134032456914063407038464⟩⟩

def packet0447 : StripRowPacket :=
  ⟨⟨⟨7,5,4,10⟩,
    ![577,1642,3002,4476,5879,7043,7840],![607,1697,3082,4574,5977,7117,7873]⟩,
    ⟨195636257410148037683868533,105054729738489027249200521216⟩,
    ⟨15860152511484557879146821,4921056517497656095022374912⟩⟩

def packet0448 : StripRowPacket :=
  ⟨⟨⟨7,4,4,11⟩,
    ![600,1685,3063,4549,5951,7095,7861],![630,1738,3140,4646,6054,7184,7906]⟩,
    ⟨1442256065286380900603433,503083407422267883644612608⟩,
    ⟨37674815455458248793336223,8942033508114228515851759616⟩⟩

def packet0449 : StripRowPacket :=
  ⟨⟨⟨7,5,4,11⟩,
    ![589,1674,3055,4544,5948,7095,7861],![617,1724,3129,4638,6050,7181,7905]⟩,
    ⟨626574753909300188307429659,210109459476978054498401042432⟩,
    ⟨5345363511769486612160701,1230264129374414023755593728⟩⟩

def packet0450 : StripRowPacket :=
  ⟨⟨⟨7,6,4,10⟩,
    ![568,1632,2994,4471,5877,7042,7840],![596,1685,3072,4567,5973,7115,7872]⟩,
    ⟨795428224125228016643027,409941124707446907494133760⟩,
    ⟨1056072349801960961256314119,318235717355651324420587601920⟩⟩

def packet0451 : StripRowPacket :=
  ⟨⟨⟨7,7,4,10⟩,
    ![560,1623,2986,4466,5874,7041,7839],![586,1675,3063,4560,5969,7113,7871]⟩,
    ⟨18441168059324773853357,9161388304690266960240640⟩,
    ⟨252495354936620969521,74066979143666929808960⟩⟩

def packet0452 : StripRowPacket :=
  ⟨⟨⟨7,6,4,11⟩,
    ![580,1664,3047,4539,5946,7094,7861],![606,1712,3119,4631,6045,7179,7905]⟩,
    ⟨5571914409241555611764371,1803740948712766392974188544⟩,
    ⟨355549346678125600054754847,79558929338912831105146900480⟩⟩

def packet0453 : StripRowPacket :=
  ⟨⟨⟨7,7,4,11⟩,
    ![572,1654,3039,4534,5944,7093,7861],![596,1701,3109,4624,6041,7177,7904]⟩,
    ⟨58436085495753443141091,18322776609380533920481280⟩,
    ⟨10453331320635584587,2278983973651290147968⟩⟩

def packet0454 : StripRowPacket :=
  ⟨⟨⟨7,0,4,12⟩,
    ![676,1771,3152,4637,6029,7153,7886],![721,1836,3241,4748,6153,7270,7958]⟩,
    ⟨4598042610299327,1433078171831967232⟩,
    ⟨13923625973855989,3081428230140575744⟩⟩

def packet0455 : StripRowPacket :=
  ⟨⟨⟨7,1,4,12⟩,
    ![655,1754,3141,4631,6028,7154,7887],![694,1812,3222,4734,6145,7265,7955]⟩,
    ⟨52643119304119478546975323,15343910231865038242705960960⟩,
    ⟨2635494787104531064266258281,555531921093506151224789032960⟩⟩

def packets018 : List StripRowPacket :=
  [packet0432, packet0433, packet0434, packet0435, packet0436, packet0437,
   packet0438, packet0439, packet0440, packet0441, packet0442, packet0443,
   packet0444, packet0445, packet0446, packet0447, packet0448, packet0449,
   packet0450, packet0451, packet0452, packet0453, packet0454, packet0455]

theorem packet0432_membership : packet0432 ∈ packets018 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0432_shape : checkStripShape packet0432.row = true := by
  decide +kernel

private theorem packet0432_cache : checkStripCache packet0432 = true := by
  decide +kernel

private theorem packet0432_pair (i : Fin 7) : checkEdgePair packet0432 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0432_ok : checkStripPacket packet0432 = true :=
  checkStripPacket_intro packet0432_shape packet0432_cache packet0432_pair

theorem packet0433_membership : packet0433 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0433_shape : checkStripShape packet0433.row = true := by
  decide +kernel

private theorem packet0433_cache : checkStripCache packet0433 = true := by
  decide +kernel

private theorem packet0433_pair (i : Fin 7) : checkEdgePair packet0433 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0433_ok : checkStripPacket packet0433 = true :=
  checkStripPacket_intro packet0433_shape packet0433_cache packet0433_pair

theorem packet0434_membership : packet0434 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0434_shape : checkStripShape packet0434.row = true := by
  decide +kernel

private theorem packet0434_cache : checkStripCache packet0434 = true := by
  decide +kernel

private theorem packet0434_pair (i : Fin 7) : checkEdgePair packet0434 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0434_ok : checkStripPacket packet0434 = true :=
  checkStripPacket_intro packet0434_shape packet0434_cache packet0434_pair

theorem packet0435_membership : packet0435 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0435_shape : checkStripShape packet0435.row = true := by
  decide +kernel

private theorem packet0435_cache : checkStripCache packet0435 = true := by
  decide +kernel

private theorem packet0435_pair (i : Fin 7) : checkEdgePair packet0435 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0435_ok : checkStripPacket packet0435 = true :=
  checkStripPacket_intro packet0435_shape packet0435_cache packet0435_pair

theorem packet0436_membership : packet0436 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0436_shape : checkStripShape packet0436.row = true := by
  decide +kernel

private theorem packet0436_cache : checkStripCache packet0436 = true := by
  decide +kernel

private theorem packet0436_pair (i : Fin 7) : checkEdgePair packet0436 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0436_ok : checkStripPacket packet0436 = true :=
  checkStripPacket_intro packet0436_shape packet0436_cache packet0436_pair

theorem packet0437_membership : packet0437 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0437_shape : checkStripShape packet0437.row = true := by
  decide +kernel

private theorem packet0437_cache : checkStripCache packet0437 = true := by
  decide +kernel

private theorem packet0437_pair (i : Fin 7) : checkEdgePair packet0437 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0437_ok : checkStripPacket packet0437 = true :=
  checkStripPacket_intro packet0437_shape packet0437_cache packet0437_pair

theorem packet0438_membership : packet0438 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0438_shape : checkStripShape packet0438.row = true := by
  decide +kernel

private theorem packet0438_cache : checkStripCache packet0438 = true := by
  decide +kernel

private theorem packet0438_pair (i : Fin 7) : checkEdgePair packet0438 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0438_ok : checkStripPacket packet0438 = true :=
  checkStripPacket_intro packet0438_shape packet0438_cache packet0438_pair

theorem packet0439_membership : packet0439 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0439_shape : checkStripShape packet0439.row = true := by
  decide +kernel

private theorem packet0439_cache : checkStripCache packet0439 = true := by
  decide +kernel

private theorem packet0439_pair (i : Fin 7) : checkEdgePair packet0439 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0439_ok : checkStripPacket packet0439 = true :=
  checkStripPacket_intro packet0439_shape packet0439_cache packet0439_pair

theorem packet0440_membership : packet0440 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0440_shape : checkStripShape packet0440.row = true := by
  decide +kernel

private theorem packet0440_cache : checkStripCache packet0440 = true := by
  decide +kernel

private theorem packet0440_pair (i : Fin 7) : checkEdgePair packet0440 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0440_ok : checkStripPacket packet0440 = true :=
  checkStripPacket_intro packet0440_shape packet0440_cache packet0440_pair

theorem packet0441_membership : packet0441 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0441_shape : checkStripShape packet0441.row = true := by
  decide +kernel

private theorem packet0441_cache : checkStripCache packet0441 = true := by
  decide +kernel

private theorem packet0441_pair (i : Fin 7) : checkEdgePair packet0441 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0441_ok : checkStripPacket packet0441 = true :=
  checkStripPacket_intro packet0441_shape packet0441_cache packet0441_pair

theorem packet0442_membership : packet0442 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0442_shape : checkStripShape packet0442.row = true := by
  decide +kernel

private theorem packet0442_cache : checkStripCache packet0442 = true := by
  decide +kernel

private theorem packet0442_pair (i : Fin 7) : checkEdgePair packet0442 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0442_ok : checkStripPacket packet0442 = true :=
  checkStripPacket_intro packet0442_shape packet0442_cache packet0442_pair

theorem packet0443_membership : packet0443 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0443_shape : checkStripShape packet0443.row = true := by
  decide +kernel

private theorem packet0443_cache : checkStripCache packet0443 = true := by
  decide +kernel

private theorem packet0443_pair (i : Fin 7) : checkEdgePair packet0443 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0443_ok : checkStripPacket packet0443 = true :=
  checkStripPacket_intro packet0443_shape packet0443_cache packet0443_pair

theorem packet0444_membership : packet0444 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0444_shape : checkStripShape packet0444.row = true := by
  decide +kernel

private theorem packet0444_cache : checkStripCache packet0444 = true := by
  decide +kernel

private theorem packet0444_pair (i : Fin 7) : checkEdgePair packet0444 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0444_ok : checkStripPacket packet0444 = true :=
  checkStripPacket_intro packet0444_shape packet0444_cache packet0444_pair

theorem packet0445_membership : packet0445 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0445_shape : checkStripShape packet0445.row = true := by
  decide +kernel

private theorem packet0445_cache : checkStripCache packet0445 = true := by
  decide +kernel

private theorem packet0445_pair (i : Fin 7) : checkEdgePair packet0445 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0445_ok : checkStripPacket packet0445 = true :=
  checkStripPacket_intro packet0445_shape packet0445_cache packet0445_pair

theorem packet0446_membership : packet0446 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0446_shape : checkStripShape packet0446.row = true := by
  decide +kernel

private theorem packet0446_cache : checkStripCache packet0446 = true := by
  decide +kernel

private theorem packet0446_pair (i : Fin 7) : checkEdgePair packet0446 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0446_ok : checkStripPacket packet0446 = true :=
  checkStripPacket_intro packet0446_shape packet0446_cache packet0446_pair

theorem packet0447_membership : packet0447 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0447_shape : checkStripShape packet0447.row = true := by
  decide +kernel

private theorem packet0447_cache : checkStripCache packet0447 = true := by
  decide +kernel

private theorem packet0447_pair (i : Fin 7) : checkEdgePair packet0447 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0447_ok : checkStripPacket packet0447 = true :=
  checkStripPacket_intro packet0447_shape packet0447_cache packet0447_pair

theorem packet0448_membership : packet0448 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0448_shape : checkStripShape packet0448.row = true := by
  decide +kernel

private theorem packet0448_cache : checkStripCache packet0448 = true := by
  decide +kernel

private theorem packet0448_pair (i : Fin 7) : checkEdgePair packet0448 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0448_ok : checkStripPacket packet0448 = true :=
  checkStripPacket_intro packet0448_shape packet0448_cache packet0448_pair

theorem packet0449_membership : packet0449 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0449_shape : checkStripShape packet0449.row = true := by
  decide +kernel

private theorem packet0449_cache : checkStripCache packet0449 = true := by
  decide +kernel

private theorem packet0449_pair (i : Fin 7) : checkEdgePair packet0449 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0449_ok : checkStripPacket packet0449 = true :=
  checkStripPacket_intro packet0449_shape packet0449_cache packet0449_pair

theorem packet0450_membership : packet0450 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0450_shape : checkStripShape packet0450.row = true := by
  decide +kernel

private theorem packet0450_cache : checkStripCache packet0450 = true := by
  decide +kernel

private theorem packet0450_pair (i : Fin 7) : checkEdgePair packet0450 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0450_ok : checkStripPacket packet0450 = true :=
  checkStripPacket_intro packet0450_shape packet0450_cache packet0450_pair

theorem packet0451_membership : packet0451 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0451_shape : checkStripShape packet0451.row = true := by
  decide +kernel

private theorem packet0451_cache : checkStripCache packet0451 = true := by
  decide +kernel

private theorem packet0451_pair (i : Fin 7) : checkEdgePair packet0451 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0451_ok : checkStripPacket packet0451 = true :=
  checkStripPacket_intro packet0451_shape packet0451_cache packet0451_pair

theorem packet0452_membership : packet0452 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0452_shape : checkStripShape packet0452.row = true := by
  decide +kernel

private theorem packet0452_cache : checkStripCache packet0452 = true := by
  decide +kernel

private theorem packet0452_pair (i : Fin 7) : checkEdgePair packet0452 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0452_ok : checkStripPacket packet0452 = true :=
  checkStripPacket_intro packet0452_shape packet0452_cache packet0452_pair

theorem packet0453_membership : packet0453 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0453_shape : checkStripShape packet0453.row = true := by
  decide +kernel

private theorem packet0453_cache : checkStripCache packet0453 = true := by
  decide +kernel

private theorem packet0453_pair (i : Fin 7) : checkEdgePair packet0453 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0453_ok : checkStripPacket packet0453 = true :=
  checkStripPacket_intro packet0453_shape packet0453_cache packet0453_pair

theorem packet0454_membership : packet0454 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0454_shape : checkStripShape packet0454.row = true := by
  decide +kernel

private theorem packet0454_cache : checkStripCache packet0454 = true := by
  decide +kernel

private theorem packet0454_pair (i : Fin 7) : checkEdgePair packet0454 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0454_ok : checkStripPacket packet0454 = true :=
  checkStripPacket_intro packet0454_shape packet0454_cache packet0454_pair

theorem packet0455_membership : packet0455 ∈ packets018 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0455_shape : checkStripShape packet0455.row = true := by
  decide +kernel

private theorem packet0455_cache : checkStripCache packet0455 = true := by
  decide +kernel

private theorem packet0455_pair (i : Fin 7) : checkEdgePair packet0455 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0455_ok : checkStripPacket packet0455 = true :=
  checkStripPacket_intro packet0455_shape packet0455_cache packet0455_pair

theorem packets018_checked : packets018.all checkStripPacket = true := by
  simp only [packets018, List.all_cons, List.all_nil, Bool.true_and, packet0432_ok,
    packet0433_ok, packet0434_ok, packet0435_ok, packet0436_ok, packet0437_ok,
    packet0438_ok, packet0439_ok, packet0440_ok, packet0441_ok, packet0442_ok,
    packet0443_ok, packet0444_ok, packet0445_ok, packet0446_ok, packet0447_ok,
    packet0448_ok, packet0449_ok, packet0450_ok, packet0451_ok, packet0452_ok,
    packet0453_ok, packet0454_ok, packet0455_ok]

theorem packets018_valid : packets018.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
