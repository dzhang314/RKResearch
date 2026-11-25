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

def packet0528 : StripRowPacket :=
  ⟨⟨⟨7,19,5,7⟩,
    ![326,1190,2478,3992,5514,6833,7769],![363,1239,2524,4028,5539,6847,7775]⟩,
    ⟨-6171677751187723686447895347,912666293875446443850437459968⟩,
    ⟨-19046368166873637203195,3239778653435669493564416⟩⟩

def packet0529 : StripRowPacket :=
  ⟨⟨⟨6,10,4,0⟩,
    ![0,931,2270,3839,5416,6784,7753],![147,1014,2332,3886,5447,6801,7761]⟩,
    ⟨-9604130309491,790814972009920⟩,
    ⟨-46321552641183982197601789,4471960371468889458688122880⟩⟩

def packet0530 : StripRowPacket :=
  ⟨⟨⟨7,20,4,1⟩,
    ![113,999,2323,3878,5441,6796,7757],![233,1084,2388,3926,5473,6814,7765]⟩,
    ⟨-80906238449264529246963049,7688870636356158014812254208⟩,
    ⟨-2365461610623021874223489331,265860268987325301036650586112⟩⟩

def packet0531 : StripRowPacket :=
  ⟨⟨⟨7,21,4,1⟩,
    ![113,996,2318,3874,5438,6795,7757],![232,1080,2383,3922,5470,6812,7764]⟩,
    ⟨-4791374237499686622009766007,449693070794346010459023392768⟩,
    ⟨-87527886288748077331089414073,9712003929586385921915008839680⟩⟩

def packet0532 : StripRowPacket :=
  ⟨⟨⟨6,11,4,0⟩,
    ![0,924,2261,3831,5411,6781,7753],![145,1007,2323,3877,5442,6798,7760]⟩,
    ⟨-878322447,70592810288⟩,
    ⟨-217585413609176613823,20477583048113076041728⟩⟩

def packet0533 : StripRowPacket :=
  ⟨⟨⟨6,11,4,1⟩,
    ![102,986,2309,3866,5433,6792,7756],![237,1079,2380,3918,5468,6811,7764]⟩,
    ⟨-73759716187315088709169,6752215440589849971220480⟩,
    ⟨-466197007986287778379,51193957620282690104320⟩⟩

def packet0534 : StripRowPacket :=
  ⟨⟨⟨7,20,5,4⟩,
    ![215,1071,2379,3918,5466,6809,7761],![272,1121,2419,3948,5487,6821,7767]⟩,
    ⟨-34800657535019273042428441,3844435318178079007406127104⟩,
    ⟨-8679833077822679960861360383,1063441075949301204146602344448⟩⟩

def packet0535 : StripRowPacket :=
  ⟨⟨⟨7,20,5,5⟩,
    ![257,1109,2409,3940,5480,6816,7764],![306,1160,2451,3972,5502,6829,7770]⟩,
    ⟨-127897706760851109007607597,15377741272712316029624508416⟩,
    ⟨-3948909856576636212414381721,531720537974650602073301172224⟩⟩

def packet0536 : StripRowPacket :=
  ⟨⟨⟨7,21,5,4⟩,
    ![214,1067,2374,3914,5464,6807,7761],![271,1118,2414,3944,5484,6819,7767]⟩,
    ⟨-792578209531932574842452063,86479436691220386626735267840⟩,
    ⟨-64233043433791692215941704601,7769603143669108737532007071744⟩⟩

def packet0537 : StripRowPacket :=
  ⟨⟨⟨7,21,5,5⟩,
    ![256,1105,2404,3936,5477,6814,7763],![305,1156,2446,3968,5499,6827,7769]⟩,
    ⟨-37864229155992307727662430879,4496930707943460104590233927680⟩,
    ⟨-13282676781042027856139063169,1765818896288433803984547061760⟩⟩

def packet0538 : StripRowPacket :=
  ⟨⟨⟨7,20,5,6⟩,
    ![293,1147,2441,3963,5495,6823,7766],![336,1198,2485,3997,5518,6837,7772]⟩,
    ⟨-58296391690812562922750715,7688870636356158014812254208⟩,
    ⟨-7115806348483864888796166501,1063441075949301204146602344448⟩⟩

def packet0539 : StripRowPacket :=
  ⟨⟨⟨7,20,5,7⟩,
    ![325,1186,2474,3988,5511,6832,7768],![361,1235,2520,4024,5536,6846,7775]⟩,
    ⟨-15041122857485591811913609,2196820181816045147089215488⟩,
    ⟨-791724122976807169095446195,132930134493662650518325293056⟩⟩

def packet0540 : StripRowPacket :=
  ⟨⟨⟨7,21,5,6⟩,
    ![292,1144,2436,3959,5492,6822,7765],![334,1194,2480,3993,5516,6835,7772]⟩,
    ⟨-17257195708162060781758677241,2248465353971730052295116963840⟩,
    ⟨-263272561196890764590410256431,38848015718345543687660035358720⟩⟩

def packet0541 : StripRowPacket :=
  ⟨⟨⟨7,21,5,7⟩,
    ![324,1182,2470,3984,5508,6830,7768],![360,1231,2515,4020,5533,6844,7774]⟩,
    ⟨-6232910735331187079874455617,899386141588692020918046785536⟩,
    ⟨-29290779151357114543220140393,4856001964793192960957504419840⟩⟩

def packet0542 : StripRowPacket :=
  ⟨⟨⟨7,22,4,2⟩,
    ![214,1064,2370,3910,5461,6806,7760],![303,1152,2442,3964,5497,6826,7769]⟩,
    ⟨-310676152390597634537231397,33491877028138508535646171136⟩,
    ⟨-233093478584191039979774191,30604877623623393357865861120⟩⟩

def packet0543 : StripRowPacket :=
  ⟨⟨⟨7,23,4,2⟩,
    ![213,1060,2365,3906,5458,6805,7760],![302,1149,2438,3960,5494,6824,7768]⟩,
    ⟨-36631797424848352477579,3902817069262209366794240⟩,
    ⟨-454332010867903031189113,58934667582777754362383360⟩⟩

def packet0544 : StripRowPacket :=
  ⟨⟨⟨7,22,5,6⟩,
    ![291,1140,2432,3956,5490,6821,7765],![333,1190,2476,3990,5513,6834,7771]⟩,
    ⟨-33817453795301250647799134671,4353944013658006109634002247680⟩,
    ⟨-419990133241921913517881987,61209755247246786715731722240⟩⟩

def packet0545 : StripRowPacket :=
  ⟨⟨⟨7,22,5,7⟩,
    ![322,1179,2465,3981,5506,6829,7768],![358,1228,2511,4017,5531,6843,7774]⟩,
    ⟨-61064461575126059453557322403,8707888027316012219268004495360⟩,
    ⟨-46724163664432718384526949,7651219405905848339466465280⟩⟩

def packet0546 : StripRowPacket :=
  ⟨⟨⟨7,23,5,6⟩,
    ![290,1137,2428,3952,5487,6819,7765],![331,1187,2472,3986,5510,6833,7771]⟩,
    ⟨-429353202622308312859239,54639438969670931135119360⟩,
    ⟨-163717484433725080443801,23573867033111101744953344⟩⟩

def packet0547 : StripRowPacket :=
  ⟨⟨⟨7,23,5,7⟩,
    ![321,1176,2461,3977,5503,6827,7767],![357,1224,2507,4013,5528,6842,7774]⟩,
    ⟨-775214443919048003891611,109278877939341862270238720⟩,
    ⟨-91063852825180592757473,14733666895694438590595840⟩⟩

def packet0548 : StripRowPacket :=
  ⟨⟨⟨7,16,5,8⟩,
    ![360,1240,2527,4030,5539,6846,7773],![392,1290,2575,4069,5566,6861,7780]⟩,
    ⟨-13176959627445698319601,2269152542682738893340160⟩,
    ⟨-732762899826458337197311,148158269056858425147228160⟩⟩

def packet0549 : StripRowPacket :=
  ⟨⟨⟨7,16,5,9⟩,
    ![384,1277,2562,4058,5557,6855,7776],![413,1325,2612,4099,5586,6872,7783]⟩,
    ⟨-92809795060160647492981,18153220341461911146721280⟩,
    ⟨-62983810342040417337031,14815826905685842514722816⟩⟩

def packet0550 : StripRowPacket :=
  ⟨⟨⟨7,17,5,8⟩,
    ![358,1236,2522,4026,5536,6845,7772],![390,1285,2570,4065,5563,6860,7779]⟩,
    ⟨-589329805730612695492035953,100144960764441208125394227200⟩,
    ⟨-2048108289830210494001970661,408303806880379592353778647040⟩⟩

def packet0551 : StripRowPacket :=
  ⟨⟨⟨7,17,5,9⟩,
    ![382,1273,2557,4054,5555,6854,7775],![410,1321,2607,4095,5583,6870,7783]⟩,
    ⟨-16402857918990894937907181,3166639075555453221356339200⟩,
    ⟨-80009109188513125483100211,18559263949108163288808120320⟩⟩

def packets022 : List StripRowPacket :=
  [packet0528, packet0529, packet0530, packet0531, packet0532, packet0533,
   packet0534, packet0535, packet0536, packet0537, packet0538, packet0539,
   packet0540, packet0541, packet0542, packet0543, packet0544, packet0545,
   packet0546, packet0547, packet0548, packet0549, packet0550, packet0551]

theorem packet0528_membership : packet0528 ∈ packets022 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0528_shape : checkStripShape packet0528.row = true := by
  decide +kernel

private theorem packet0528_cache : checkStripCache packet0528 = true := by
  decide +kernel

private theorem packet0528_pair (i : Fin 7) : checkEdgePair packet0528 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0528_ok : checkStripPacket packet0528 = true :=
  checkStripPacket_intro packet0528_shape packet0528_cache packet0528_pair

theorem packet0529_membership : packet0529 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0529_shape : checkStripShape packet0529.row = true := by
  decide +kernel

private theorem packet0529_cache : checkStripCache packet0529 = true := by
  decide +kernel

private theorem packet0529_pair (i : Fin 7) : checkEdgePair packet0529 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0529_ok : checkStripPacket packet0529 = true :=
  checkStripPacket_intro packet0529_shape packet0529_cache packet0529_pair

theorem packet0530_membership : packet0530 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0530_shape : checkStripShape packet0530.row = true := by
  decide +kernel

private theorem packet0530_cache : checkStripCache packet0530 = true := by
  decide +kernel

private theorem packet0530_pair (i : Fin 7) : checkEdgePair packet0530 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0530_ok : checkStripPacket packet0530 = true :=
  checkStripPacket_intro packet0530_shape packet0530_cache packet0530_pair

theorem packet0531_membership : packet0531 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0531_shape : checkStripShape packet0531.row = true := by
  decide +kernel

private theorem packet0531_cache : checkStripCache packet0531 = true := by
  decide +kernel

private theorem packet0531_pair (i : Fin 7) : checkEdgePair packet0531 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0531_ok : checkStripPacket packet0531 = true :=
  checkStripPacket_intro packet0531_shape packet0531_cache packet0531_pair

theorem packet0532_membership : packet0532 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0532_shape : checkStripShape packet0532.row = true := by
  decide +kernel

private theorem packet0532_cache : checkStripCache packet0532 = true := by
  decide +kernel

private theorem packet0532_pair (i : Fin 7) : checkEdgePair packet0532 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0532_ok : checkStripPacket packet0532 = true :=
  checkStripPacket_intro packet0532_shape packet0532_cache packet0532_pair

theorem packet0533_membership : packet0533 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0533_shape : checkStripShape packet0533.row = true := by
  decide +kernel

private theorem packet0533_cache : checkStripCache packet0533 = true := by
  decide +kernel

private theorem packet0533_pair (i : Fin 7) : checkEdgePair packet0533 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0533_ok : checkStripPacket packet0533 = true :=
  checkStripPacket_intro packet0533_shape packet0533_cache packet0533_pair

theorem packet0534_membership : packet0534 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0534_shape : checkStripShape packet0534.row = true := by
  decide +kernel

private theorem packet0534_cache : checkStripCache packet0534 = true := by
  decide +kernel

private theorem packet0534_pair (i : Fin 7) : checkEdgePair packet0534 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0534_ok : checkStripPacket packet0534 = true :=
  checkStripPacket_intro packet0534_shape packet0534_cache packet0534_pair

theorem packet0535_membership : packet0535 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0535_shape : checkStripShape packet0535.row = true := by
  decide +kernel

private theorem packet0535_cache : checkStripCache packet0535 = true := by
  decide +kernel

private theorem packet0535_pair (i : Fin 7) : checkEdgePair packet0535 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0535_ok : checkStripPacket packet0535 = true :=
  checkStripPacket_intro packet0535_shape packet0535_cache packet0535_pair

theorem packet0536_membership : packet0536 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0536_shape : checkStripShape packet0536.row = true := by
  decide +kernel

private theorem packet0536_cache : checkStripCache packet0536 = true := by
  decide +kernel

private theorem packet0536_pair (i : Fin 7) : checkEdgePair packet0536 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0536_ok : checkStripPacket packet0536 = true :=
  checkStripPacket_intro packet0536_shape packet0536_cache packet0536_pair

theorem packet0537_membership : packet0537 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0537_shape : checkStripShape packet0537.row = true := by
  decide +kernel

private theorem packet0537_cache : checkStripCache packet0537 = true := by
  decide +kernel

private theorem packet0537_pair (i : Fin 7) : checkEdgePair packet0537 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0537_ok : checkStripPacket packet0537 = true :=
  checkStripPacket_intro packet0537_shape packet0537_cache packet0537_pair

theorem packet0538_membership : packet0538 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0538_shape : checkStripShape packet0538.row = true := by
  decide +kernel

private theorem packet0538_cache : checkStripCache packet0538 = true := by
  decide +kernel

private theorem packet0538_pair (i : Fin 7) : checkEdgePair packet0538 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0538_ok : checkStripPacket packet0538 = true :=
  checkStripPacket_intro packet0538_shape packet0538_cache packet0538_pair

theorem packet0539_membership : packet0539 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0539_shape : checkStripShape packet0539.row = true := by
  decide +kernel

private theorem packet0539_cache : checkStripCache packet0539 = true := by
  decide +kernel

private theorem packet0539_pair (i : Fin 7) : checkEdgePair packet0539 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0539_ok : checkStripPacket packet0539 = true :=
  checkStripPacket_intro packet0539_shape packet0539_cache packet0539_pair

theorem packet0540_membership : packet0540 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0540_shape : checkStripShape packet0540.row = true := by
  decide +kernel

private theorem packet0540_cache : checkStripCache packet0540 = true := by
  decide +kernel

private theorem packet0540_pair (i : Fin 7) : checkEdgePair packet0540 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0540_ok : checkStripPacket packet0540 = true :=
  checkStripPacket_intro packet0540_shape packet0540_cache packet0540_pair

theorem packet0541_membership : packet0541 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0541_shape : checkStripShape packet0541.row = true := by
  decide +kernel

private theorem packet0541_cache : checkStripCache packet0541 = true := by
  decide +kernel

private theorem packet0541_pair (i : Fin 7) : checkEdgePair packet0541 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0541_ok : checkStripPacket packet0541 = true :=
  checkStripPacket_intro packet0541_shape packet0541_cache packet0541_pair

theorem packet0542_membership : packet0542 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0542_shape : checkStripShape packet0542.row = true := by
  decide +kernel

private theorem packet0542_cache : checkStripCache packet0542 = true := by
  decide +kernel

private theorem packet0542_pair (i : Fin 7) : checkEdgePair packet0542 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0542_ok : checkStripPacket packet0542 = true :=
  checkStripPacket_intro packet0542_shape packet0542_cache packet0542_pair

theorem packet0543_membership : packet0543 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0543_shape : checkStripShape packet0543.row = true := by
  decide +kernel

private theorem packet0543_cache : checkStripCache packet0543 = true := by
  decide +kernel

private theorem packet0543_pair (i : Fin 7) : checkEdgePair packet0543 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0543_ok : checkStripPacket packet0543 = true :=
  checkStripPacket_intro packet0543_shape packet0543_cache packet0543_pair

theorem packet0544_membership : packet0544 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0544_shape : checkStripShape packet0544.row = true := by
  decide +kernel

private theorem packet0544_cache : checkStripCache packet0544 = true := by
  decide +kernel

private theorem packet0544_pair (i : Fin 7) : checkEdgePair packet0544 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0544_ok : checkStripPacket packet0544 = true :=
  checkStripPacket_intro packet0544_shape packet0544_cache packet0544_pair

theorem packet0545_membership : packet0545 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0545_shape : checkStripShape packet0545.row = true := by
  decide +kernel

private theorem packet0545_cache : checkStripCache packet0545 = true := by
  decide +kernel

private theorem packet0545_pair (i : Fin 7) : checkEdgePair packet0545 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0545_ok : checkStripPacket packet0545 = true :=
  checkStripPacket_intro packet0545_shape packet0545_cache packet0545_pair

theorem packet0546_membership : packet0546 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0546_shape : checkStripShape packet0546.row = true := by
  decide +kernel

private theorem packet0546_cache : checkStripCache packet0546 = true := by
  decide +kernel

private theorem packet0546_pair (i : Fin 7) : checkEdgePair packet0546 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0546_ok : checkStripPacket packet0546 = true :=
  checkStripPacket_intro packet0546_shape packet0546_cache packet0546_pair

theorem packet0547_membership : packet0547 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0547_shape : checkStripShape packet0547.row = true := by
  decide +kernel

private theorem packet0547_cache : checkStripCache packet0547 = true := by
  decide +kernel

private theorem packet0547_pair (i : Fin 7) : checkEdgePair packet0547 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0547_ok : checkStripPacket packet0547 = true :=
  checkStripPacket_intro packet0547_shape packet0547_cache packet0547_pair

theorem packet0548_membership : packet0548 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0548_shape : checkStripShape packet0548.row = true := by
  decide +kernel

private theorem packet0548_cache : checkStripCache packet0548 = true := by
  decide +kernel

private theorem packet0548_pair (i : Fin 7) : checkEdgePair packet0548 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0548_ok : checkStripPacket packet0548 = true :=
  checkStripPacket_intro packet0548_shape packet0548_cache packet0548_pair

theorem packet0549_membership : packet0549 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0549_shape : checkStripShape packet0549.row = true := by
  decide +kernel

private theorem packet0549_cache : checkStripCache packet0549 = true := by
  decide +kernel

private theorem packet0549_pair (i : Fin 7) : checkEdgePair packet0549 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0549_ok : checkStripPacket packet0549 = true :=
  checkStripPacket_intro packet0549_shape packet0549_cache packet0549_pair

theorem packet0550_membership : packet0550 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0550_shape : checkStripShape packet0550.row = true := by
  decide +kernel

private theorem packet0550_cache : checkStripCache packet0550 = true := by
  decide +kernel

private theorem packet0550_pair (i : Fin 7) : checkEdgePair packet0550 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0550_ok : checkStripPacket packet0550 = true :=
  checkStripPacket_intro packet0550_shape packet0550_cache packet0550_pair

theorem packet0551_membership : packet0551 ∈ packets022 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0551_shape : checkStripShape packet0551.row = true := by
  decide +kernel

private theorem packet0551_cache : checkStripCache packet0551 = true := by
  decide +kernel

private theorem packet0551_pair (i : Fin 7) : checkEdgePair packet0551 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0551_ok : checkStripPacket packet0551 = true :=
  checkStripPacket_intro packet0551_shape packet0551_cache packet0551_pair

theorem packets022_checked : packets022.all checkStripPacket = true := by
  simp only [packets022, List.all_cons, List.all_nil, Bool.true_and, packet0528_ok,
    packet0529_ok, packet0530_ok, packet0531_ok, packet0532_ok, packet0533_ok,
    packet0534_ok, packet0535_ok, packet0536_ok, packet0537_ok, packet0538_ok,
    packet0539_ok, packet0540_ok, packet0541_ok, packet0542_ok, packet0543_ok,
    packet0544_ok, packet0545_ok, packet0546_ok, packet0547_ok, packet0548_ok,
    packet0549_ok, packet0550_ok, packet0551_ok]

theorem packets022_valid : packets022.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
