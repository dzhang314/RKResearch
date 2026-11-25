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

def packet0504 : StripRowPacket :=
  ⟨⟨⟨7,16,5,2⟩,
    ![113,1016,2343,3895,5453,6802,7759],![192,1064,2379,3923,5472,6813,7765]⟩,
    ⟨-18105096877599522093977,1815322034146191114672128⟩,
    ⟨-122755607114798483650847,13468933550623493195202560⟩⟩

def packet0505 : StripRowPacket :=
  ⟨⟨⟨7,16,5,3⟩,
    ![169,1050,2370,3914,5465,6808,7761],![238,1101,2408,3943,5485,6820,7767]⟩,
    ⟨-168445086816590281875943,18153220341461911146721280⟩,
    ⟨-311846720464182289083079,37039567264214606286807040⟩⟩

def packet0506 : StripRowPacket :=
  ⟨⟨⟨7,17,5,2⟩,
    ![113,1011,2338,3890,5450,6801,7759],![191,1059,2374,3918,5469,6812,7764]⟩,
    ⟨-810293079988613243181091261,80115968611552966500315381760⟩,
    ⟨-755111123185548178848913355,81660761376075918470755729408⟩⟩

def packet0507 : StripRowPacket :=
  ⟨⟨⟨7,17,5,3⟩,
    ![168,1046,2365,3910,5462,6807,7761],![237,1096,2403,3939,5482,6818,7766]⟩,
    ⟨-7538215407545927287165141779,801159686115529665003153817600⟩,
    ⟨-124558847437314970031100027,14582278817156414012634951680⟩⟩

def packet0508 : StripRowPacket :=
  ⟨⟨⟨7,18,4,0⟩,
    ![0,945,2284,3851,5425,6788,7755],![139,1020,2342,3894,5453,6804,7762]⟩,
    ⟨-991640620679051,84882367361078144⟩,
    ⟨-4748828142054861368083404059,470507658475467461050082017280⟩⟩

def packet0509 : StripRowPacket :=
  ⟨⟨⟨7,19,4,0⟩,
    ![0,941,2279,3847,5422,6787,7754],![138,1016,2336,3890,5450,6802,7761]⟩,
    ⟨-1107008533661,93506569183456⟩,
    ⟨-132592781207734455854387,12959114613742677974257664⟩⟩

def packet0510 : StripRowPacket :=
  ⟨⟨⟨7,18,5,2⟩,
    ![113,1007,2333,3886,5447,6799,7758],![190,1055,2369,3914,5465,6810,7764]⟩,
    ⟨-53578988953604422263382309,5226070270002998490434314240⟩,
    ⟨-44122365879647188373952080277,4705076584754674610500820172800⟩⟩

def packet0511 : StripRowPacket :=
  ⟨⟨⟨7,18,5,3⟩,
    ![168,1042,2359,3905,5459,6805,7760],![235,1092,2398,3934,5479,6817,7766]⟩,
    ⟨-99683255384872118214673967,10452140540005996980868628480⟩,
    ⟨-10189112584686440766767529991,1176269146188668652625205043200⟩⟩

def packet0512 : StripRowPacket :=
  ⟨⟨⟨7,19,4,1⟩,
    ![113,1003,2328,3882,5444,6798,7758],![234,1088,2393,3930,5476,6815,7765]⟩,
    ⟨-364658619090224037081302537,35102549764440247840401440768⟩,
    ⟨-56895172513827243420259,6479557306871338987128832⟩⟩

def packet0513 : StripRowPacket :=
  ⟨⟨⟨7,16,5,4⟩,
    ![218,1087,2398,3934,5478,6815,7763],![278,1139,2439,3966,5499,6827,7769]⟩,
    ⟨-5565685887756619386147,648329297909353969525760⟩,
    ⟨-228892417090134998501063,29631653811371685029445632⟩⟩

def packet0514 : StripRowPacket :=
  ⟨⟨⟨7,16,5,5⟩,
    ![261,1125,2428,3956,5492,6822,7765],![313,1177,2471,3989,5514,6835,7771]⟩,
    ⟨-143233322897780403748289,18153220341461911146721280⟩,
    ⟨-520768644522310414339157,74079134528429212573614080⟩⟩

def packet0515 : StripRowPacket :=
  ⟨⟨⟨7,17,5,4⟩,
    ![217,1083,2393,3930,5475,6813,7763],![276,1134,2433,3961,5496,6825,7769]⟩,
    ⟨-1743375003801430535629842737,200289921528882416250788454400⟩,
    ⟨-3199739840561897427497034737,408303806880379592353778647040⟩⟩

def packet0516 : StripRowPacket :=
  ⟨⟨⟨7,17,5,5⟩,
    ![260,1120,2423,3952,5489,6820,7765],![311,1172,2466,3985,5511,6833,7771]⟩,
    ⟨-6408784622865516997873600117,801159686115529665003153817600⟩,
    ⟨-1455915976439487847061634359,204151903440189796176889323520⟩⟩

def packet0517 : StripRowPacket :=
  ⟨⟨⟨7,16,5,6⟩,
    ![299,1164,2460,3979,5506,6829,7768],![343,1215,2505,4014,5530,6843,7774]⟩,
    ⟨-65313720469187732342231,9076610170730955573360640⟩,
    ⟨-938612492638566664851313,148158269056858425147228160⟩⟩

def packet0518 : StripRowPacket :=
  ⟨⟨⟨7,16,5,7⟩,
    ![331,1202,2493,4004,5522,6837,7770],![369,1253,2539,4041,5547,6852,7777]⟩,
    ⟨-23604311795794105124127,3630644068292382229344256⟩,
    ⟨-104460962029064062628039,18519783632107303143403520⟩⟩

def packet0519 : StripRowPacket :=
  ⟨⟨⟨7,17,5,6⟩,
    ![297,1159,2455,3975,5503,6828,7767],![341,1210,2499,4010,5527,6841,7774]⟩,
    ⟨-2922034615262655926613914643,400579843057764832501576908800⟩,
    ⟨-2623924065196053960749502699,408303806880379592353778647040⟩⟩

def packet0520 : StripRowPacket :=
  ⟨⟨⟨7,17,5,7⟩,
    ![330,1198,2488,4000,5519,6836,7770],![367,1248,2534,4037,5544,6850,7776]⟩,
    ⟨-1055870767637021341716411691,160231937223105933000630763520⟩,
    ⟨-58400404437828305684393417,10207595172009489808844466176⟩⟩

def packet0521 : StripRowPacket :=
  ⟨⟨⟨7,18,5,4⟩,
    ![216,1078,2388,3926,5472,6812,7762],![275,1130,2428,3957,5493,6824,7768]⟩,
    ⟨-23052133215633847975645829,2613035135001499245217157120⟩,
    ⟨-37390534797844337760188159651,4705076584754674610500820172800⟩⟩

def packet0522 : StripRowPacket :=
  ⟨⟨⟨7,18,5,5⟩,
    ![259,1116,2418,3948,5486,6819,7764],![309,1168,2461,3980,5508,6832,7770]⟩,
    ⟨-1303597082156902547546041,160802162153938415090286592⟩,
    ⟨-17012309628471456226653099669,2352538292377337305250410086400⟩⟩

def packet0523 : StripRowPacket :=
  ⟨⟨⟨7,19,5,4⟩,
    ![216,1074,2383,3922,5469,6810,7762],![273,1125,2423,3952,5490,6822,7768]⟩,
    ⟨-2039336389570646113261869429,228166573468861610962609364992⟩,
    ⟨-208778253875229004667167,25918229227485355948515328⟩⟩

def packet0524 : StripRowPacket :=
  ⟨⟨⟨7,19,5,5⟩,
    ![258,1112,2413,3944,5483,6817,7764],![308,1164,2456,3976,5505,6830,7770]⟩,
    ⟨-7495456289250964197514283593,912666293875446443850437459968⟩,
    ⟨-7306762219044193678973,996854970287898305712128⟩⟩

def packet0525 : StripRowPacket :=
  ⟨⟨⟨7,18,5,6⟩,
    ![296,1155,2450,3971,5501,6826,7767],![339,1206,2494,4006,5524,6840,7773]⟩,
    ⟨-3511776718993724512654637,475097297272999862766755840⟩,
    ⟨-1226348148641659485856969561,188203063390186984420032806912⟩⟩

def packet0526 : StripRowPacket :=
  ⟨⟨⟨7,18,5,7⟩,
    ![328,1194,2483,3996,5516,6834,7769],![365,1244,2529,4032,5541,6849,7776]⟩,
    ⟨-69784365295525212966311363,10452140540005996980868628480⟩,
    ⟨-3411598521892507729942784839,588134573094334326312602521600⟩⟩

def packet0527 : StripRowPacket :=
  ⟨⟨⟨7,19,5,6⟩,
    ![295,1151,2445,3967,5498,6825,7766],![337,1202,2489,4001,5521,6838,7773]⟩,
    ⟨-310616682737242906453685885,41484831539793020175019884544⟩,
    ⟨-2223030928767130735577,336600379577731895435264⟩⟩

def packets021 : List StripRowPacket :=
  [packet0504, packet0505, packet0506, packet0507, packet0508, packet0509,
   packet0510, packet0511, packet0512, packet0513, packet0514, packet0515,
   packet0516, packet0517, packet0518, packet0519, packet0520, packet0521,
   packet0522, packet0523, packet0524, packet0525, packet0526, packet0527]

theorem packet0504_membership : packet0504 ∈ packets021 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0504_shape : checkStripShape packet0504.row = true := by
  decide +kernel

private theorem packet0504_cache : checkStripCache packet0504 = true := by
  decide +kernel

private theorem packet0504_pair (i : Fin 7) : checkEdgePair packet0504 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0504_ok : checkStripPacket packet0504 = true :=
  checkStripPacket_intro packet0504_shape packet0504_cache packet0504_pair

theorem packet0505_membership : packet0505 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0505_shape : checkStripShape packet0505.row = true := by
  decide +kernel

private theorem packet0505_cache : checkStripCache packet0505 = true := by
  decide +kernel

private theorem packet0505_pair (i : Fin 7) : checkEdgePair packet0505 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0505_ok : checkStripPacket packet0505 = true :=
  checkStripPacket_intro packet0505_shape packet0505_cache packet0505_pair

theorem packet0506_membership : packet0506 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0506_shape : checkStripShape packet0506.row = true := by
  decide +kernel

private theorem packet0506_cache : checkStripCache packet0506 = true := by
  decide +kernel

private theorem packet0506_pair (i : Fin 7) : checkEdgePair packet0506 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0506_ok : checkStripPacket packet0506 = true :=
  checkStripPacket_intro packet0506_shape packet0506_cache packet0506_pair

theorem packet0507_membership : packet0507 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0507_shape : checkStripShape packet0507.row = true := by
  decide +kernel

private theorem packet0507_cache : checkStripCache packet0507 = true := by
  decide +kernel

private theorem packet0507_pair (i : Fin 7) : checkEdgePair packet0507 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0507_ok : checkStripPacket packet0507 = true :=
  checkStripPacket_intro packet0507_shape packet0507_cache packet0507_pair

theorem packet0508_membership : packet0508 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0508_shape : checkStripShape packet0508.row = true := by
  decide +kernel

private theorem packet0508_cache : checkStripCache packet0508 = true := by
  decide +kernel

private theorem packet0508_pair (i : Fin 7) : checkEdgePair packet0508 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0508_ok : checkStripPacket packet0508 = true :=
  checkStripPacket_intro packet0508_shape packet0508_cache packet0508_pair

theorem packet0509_membership : packet0509 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0509_shape : checkStripShape packet0509.row = true := by
  decide +kernel

private theorem packet0509_cache : checkStripCache packet0509 = true := by
  decide +kernel

private theorem packet0509_pair (i : Fin 7) : checkEdgePair packet0509 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0509_ok : checkStripPacket packet0509 = true :=
  checkStripPacket_intro packet0509_shape packet0509_cache packet0509_pair

theorem packet0510_membership : packet0510 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0510_shape : checkStripShape packet0510.row = true := by
  decide +kernel

private theorem packet0510_cache : checkStripCache packet0510 = true := by
  decide +kernel

private theorem packet0510_pair (i : Fin 7) : checkEdgePair packet0510 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0510_ok : checkStripPacket packet0510 = true :=
  checkStripPacket_intro packet0510_shape packet0510_cache packet0510_pair

theorem packet0511_membership : packet0511 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0511_shape : checkStripShape packet0511.row = true := by
  decide +kernel

private theorem packet0511_cache : checkStripCache packet0511 = true := by
  decide +kernel

private theorem packet0511_pair (i : Fin 7) : checkEdgePair packet0511 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0511_ok : checkStripPacket packet0511 = true :=
  checkStripPacket_intro packet0511_shape packet0511_cache packet0511_pair

theorem packet0512_membership : packet0512 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0512_shape : checkStripShape packet0512.row = true := by
  decide +kernel

private theorem packet0512_cache : checkStripCache packet0512 = true := by
  decide +kernel

private theorem packet0512_pair (i : Fin 7) : checkEdgePair packet0512 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0512_ok : checkStripPacket packet0512 = true :=
  checkStripPacket_intro packet0512_shape packet0512_cache packet0512_pair

theorem packet0513_membership : packet0513 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0513_shape : checkStripShape packet0513.row = true := by
  decide +kernel

private theorem packet0513_cache : checkStripCache packet0513 = true := by
  decide +kernel

private theorem packet0513_pair (i : Fin 7) : checkEdgePair packet0513 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0513_ok : checkStripPacket packet0513 = true :=
  checkStripPacket_intro packet0513_shape packet0513_cache packet0513_pair

theorem packet0514_membership : packet0514 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0514_shape : checkStripShape packet0514.row = true := by
  decide +kernel

private theorem packet0514_cache : checkStripCache packet0514 = true := by
  decide +kernel

private theorem packet0514_pair (i : Fin 7) : checkEdgePair packet0514 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0514_ok : checkStripPacket packet0514 = true :=
  checkStripPacket_intro packet0514_shape packet0514_cache packet0514_pair

theorem packet0515_membership : packet0515 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0515_shape : checkStripShape packet0515.row = true := by
  decide +kernel

private theorem packet0515_cache : checkStripCache packet0515 = true := by
  decide +kernel

private theorem packet0515_pair (i : Fin 7) : checkEdgePair packet0515 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0515_ok : checkStripPacket packet0515 = true :=
  checkStripPacket_intro packet0515_shape packet0515_cache packet0515_pair

theorem packet0516_membership : packet0516 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0516_shape : checkStripShape packet0516.row = true := by
  decide +kernel

private theorem packet0516_cache : checkStripCache packet0516 = true := by
  decide +kernel

private theorem packet0516_pair (i : Fin 7) : checkEdgePair packet0516 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0516_ok : checkStripPacket packet0516 = true :=
  checkStripPacket_intro packet0516_shape packet0516_cache packet0516_pair

theorem packet0517_membership : packet0517 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0517_shape : checkStripShape packet0517.row = true := by
  decide +kernel

private theorem packet0517_cache : checkStripCache packet0517 = true := by
  decide +kernel

private theorem packet0517_pair (i : Fin 7) : checkEdgePair packet0517 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0517_ok : checkStripPacket packet0517 = true :=
  checkStripPacket_intro packet0517_shape packet0517_cache packet0517_pair

theorem packet0518_membership : packet0518 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0518_shape : checkStripShape packet0518.row = true := by
  decide +kernel

private theorem packet0518_cache : checkStripCache packet0518 = true := by
  decide +kernel

private theorem packet0518_pair (i : Fin 7) : checkEdgePair packet0518 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0518_ok : checkStripPacket packet0518 = true :=
  checkStripPacket_intro packet0518_shape packet0518_cache packet0518_pair

theorem packet0519_membership : packet0519 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0519_shape : checkStripShape packet0519.row = true := by
  decide +kernel

private theorem packet0519_cache : checkStripCache packet0519 = true := by
  decide +kernel

private theorem packet0519_pair (i : Fin 7) : checkEdgePair packet0519 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0519_ok : checkStripPacket packet0519 = true :=
  checkStripPacket_intro packet0519_shape packet0519_cache packet0519_pair

theorem packet0520_membership : packet0520 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0520_shape : checkStripShape packet0520.row = true := by
  decide +kernel

private theorem packet0520_cache : checkStripCache packet0520 = true := by
  decide +kernel

private theorem packet0520_pair (i : Fin 7) : checkEdgePair packet0520 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0520_ok : checkStripPacket packet0520 = true :=
  checkStripPacket_intro packet0520_shape packet0520_cache packet0520_pair

theorem packet0521_membership : packet0521 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0521_shape : checkStripShape packet0521.row = true := by
  decide +kernel

private theorem packet0521_cache : checkStripCache packet0521 = true := by
  decide +kernel

private theorem packet0521_pair (i : Fin 7) : checkEdgePair packet0521 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0521_ok : checkStripPacket packet0521 = true :=
  checkStripPacket_intro packet0521_shape packet0521_cache packet0521_pair

theorem packet0522_membership : packet0522 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0522_shape : checkStripShape packet0522.row = true := by
  decide +kernel

private theorem packet0522_cache : checkStripCache packet0522 = true := by
  decide +kernel

private theorem packet0522_pair (i : Fin 7) : checkEdgePair packet0522 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0522_ok : checkStripPacket packet0522 = true :=
  checkStripPacket_intro packet0522_shape packet0522_cache packet0522_pair

theorem packet0523_membership : packet0523 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0523_shape : checkStripShape packet0523.row = true := by
  decide +kernel

private theorem packet0523_cache : checkStripCache packet0523 = true := by
  decide +kernel

private theorem packet0523_pair (i : Fin 7) : checkEdgePair packet0523 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0523_ok : checkStripPacket packet0523 = true :=
  checkStripPacket_intro packet0523_shape packet0523_cache packet0523_pair

theorem packet0524_membership : packet0524 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0524_shape : checkStripShape packet0524.row = true := by
  decide +kernel

private theorem packet0524_cache : checkStripCache packet0524 = true := by
  decide +kernel

private theorem packet0524_pair (i : Fin 7) : checkEdgePair packet0524 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0524_ok : checkStripPacket packet0524 = true :=
  checkStripPacket_intro packet0524_shape packet0524_cache packet0524_pair

theorem packet0525_membership : packet0525 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0525_shape : checkStripShape packet0525.row = true := by
  decide +kernel

private theorem packet0525_cache : checkStripCache packet0525 = true := by
  decide +kernel

private theorem packet0525_pair (i : Fin 7) : checkEdgePair packet0525 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0525_ok : checkStripPacket packet0525 = true :=
  checkStripPacket_intro packet0525_shape packet0525_cache packet0525_pair

theorem packet0526_membership : packet0526 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0526_shape : checkStripShape packet0526.row = true := by
  decide +kernel

private theorem packet0526_cache : checkStripCache packet0526 = true := by
  decide +kernel

private theorem packet0526_pair (i : Fin 7) : checkEdgePair packet0526 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0526_ok : checkStripPacket packet0526 = true :=
  checkStripPacket_intro packet0526_shape packet0526_cache packet0526_pair

theorem packet0527_membership : packet0527 ∈ packets021 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0527_shape : checkStripShape packet0527.row = true := by
  decide +kernel

private theorem packet0527_cache : checkStripCache packet0527 = true := by
  decide +kernel

private theorem packet0527_pair (i : Fin 7) : checkEdgePair packet0527 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0527_ok : checkStripPacket packet0527 = true :=
  checkStripPacket_intro packet0527_shape packet0527_cache packet0527_pair

theorem packets021_checked : packets021.all checkStripPacket = true := by
  simp only [packets021, List.all_cons, List.all_nil, Bool.true_and, packet0504_ok,
    packet0505_ok, packet0506_ok, packet0507_ok, packet0508_ok, packet0509_ok,
    packet0510_ok, packet0511_ok, packet0512_ok, packet0513_ok, packet0514_ok,
    packet0515_ok, packet0516_ok, packet0517_ok, packet0518_ok, packet0519_ok,
    packet0520_ok, packet0521_ok, packet0522_ok, packet0523_ok, packet0524_ok,
    packet0525_ok, packet0526_ok, packet0527_ok]

theorem packets021_valid : packets021.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
