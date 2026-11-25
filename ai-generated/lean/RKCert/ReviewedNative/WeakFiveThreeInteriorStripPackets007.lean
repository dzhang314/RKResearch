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

def packet0168 : StripRowPacket :=
  ⟨⟨⟨8,11,5,7⟩,
    ![369,1272,2564,4062,5561,6857,7777],![411,1322,2608,4096,5584,6871,7783]⟩,
    ⟨-4019325133275635199336280962283,745799706660290370534961516052480⟩,
    ⟨-6591113822371937437336345079,1398370352611094193780742092800⟩⟩

def packet0169 : StripRowPacket :=
  ⟨⟨⟨8,12,5,4⟩,
    ![240,1154,2468,3991,5516,6835,7769],![302,1202,2506,4020,5535,6846,7775]⟩,
    ⟨-283124355062383100140434375,39551433170227107051834748928⟩,
    ⟨-321743989103511862366305069847,49659792910158780612092474884096⟩⟩

def packet0170 : StripRowPacket :=
  ⟨⟨⟨8,13,5,4⟩,
    ![239,1150,2464,3988,5514,6834,7769],![300,1198,2502,4017,5533,6845,7775]⟩,
    ⟨-568218469091049363626695013993,78542811863831680844798684119040⟩,
    ⟨-3562496796698566080114666958783,543887680393468787917274698252288⟩⟩

def packet0171 : StripRowPacket :=
  ⟨⟨⟨8,12,5,5⟩,
    ![288,1192,2497,4012,5529,6841,7772],![342,1240,2537,4043,5550,6853,7777]⟩,
    ⟨-11463584113304427440351557393,1740263059489992710280728952832⟩,
    ⟨-11283080075098774275418536453,1909992035006106946618941341696⟩⟩

def packet0172 : StripRowPacket :=
  ⟨⟨⟨8,13,5,5⟩,
    ![286,1187,2493,4009,5527,6840,7771],![339,1236,2533,4039,5547,6852,7777]⟩,
    ⟨-2091239626487524707490388371853,314171247455326723379194736476160⟩,
    ⟨-738142621656531765752044373143,123610836453061088163016976875520⟩⟩

def packet0173 : StripRowPacket :=
  ⟨⟨⟨7,7,5,4⟩,
    ![230,1140,2455,3981,5509,6831,7768],![302,1195,2499,4014,5531,6844,7774]⟩,
    ⟨-67773829449090807884151,9161388304690266960240640⟩,
    ⟨-1956107621710724126837,296267916574667719235840⟩⟩

def packet0174 : StripRowPacket :=
  ⟨⟨⟨7,7,5,5⟩,
    ![278,1178,2484,4002,5522,6838,7770],![340,1233,2530,4037,5546,6851,7777]⟩,
    ⟨-249541568419259336102227,36645553218761067840962560⟩,
    ⟨-445407948935663266931,74066979143666929808960⟩⟩

def packet0175 : StripRowPacket :=
  ⟨⟨⟨8,12,5,6⟩,
    ![330,1230,2528,4035,5543,6849,7774],![376,1279,2570,4067,5565,6861,7780]⟩,
    ⟨-5234848301931999237262001143,870131529744996355140364476416⟩,
    ⟨-264976174801624399955458825709,49659792910158780612092474884096⟩⟩

def packet0176 : StripRowPacket :=
  ⟨⟨⟨8,13,5,6⟩,
    ![328,1226,2524,4032,5541,6848,7773],![374,1274,2566,4064,5563,6860,7779]⟩,
    ⟨-954802688305425980236998343867,157085623727663361689597368238080⟩,
    ⟨-14665791369394567292516617624377,2719438401967343939586373491261440⟩⟩

def packet0177 : StripRowPacket :=
  ⟨⟨⟨8,12,5,7⟩,
    ![367,1268,2560,4059,5559,6856,7776],![407,1317,2604,4093,5582,6870,7782]⟩,
    ⟨-9475809094423569508696447179,1740263059489992710280728952832⟩,
    ⟨-29574033456335083593754462955,6207474113769847576511559360512⟩⟩

def packet0178 : StripRowPacket :=
  ⟨⟨⟨8,13,5,7⟩,
    ![364,1264,2556,4055,5557,6855,7776],![404,1313,2600,4090,5580,6869,7782]⟩,
    ⟨-345594225346835842691521000723,62834249491065344675838947295232⟩,
    ⟨-1636555632793179467311032379951,339929800245917992448296686407680⟩⟩

def packet0179 : StripRowPacket :=
  ⟨⟨⟨7,7,5,6⟩,
    ![320,1216,2515,4025,5537,6845,7773],![373,1272,2563,4062,5562,6859,7779]⟩,
    ⟨-2072616536746867642435,333141392897827889463296⟩,
    ⟨-1607155969774582008611,296267916574667719235840⟩⟩

def packet0180 : StripRowPacket :=
  ⟨⟨⟨8,14,5,7⟩,
    ![361,1260,2552,4052,5555,6854,7776],![401,1308,2596,4087,5578,6868,7782]⟩,
    ⟨-1491082187261805681564475593611,268448183214231501402704242769920⟩,
    ⟨-3653878466278508556068393012747,751232861952089038678448323665920⟩⟩

def packet0181 : StripRowPacket :=
  ⟨⟨⟨8,15,5,7⟩,
    ![359,1256,2548,4050,5553,6853,7775],![398,1304,2592,4084,5576,6867,7781]⟩,
    ⟨-306735550837519109501358627,54694719266083358683678572544⟩,
    ⟨-21347249021964728313015899,4345375626861326390953917440⟩⟩

def packet0182 : StripRowPacket :=
  ⟨⟨⟨8,0,6,16⟩,
    ![458,1371,2650,4126,5602,6879,7783],![495,1409,2683,4152,5620,6889,7788]⟩,
    ⟨-740950191822888323,174016744175884712960⟩,
    ⟨-5589933528696913511,1445432673935107686400⟩⟩

def packet0183 : StripRowPacket :=
  ⟨⟨⟨8,0,6,17⟩,
    ![475,1390,2666,4139,5610,6883,7784],![511,1429,2701,4165,5629,6894,7790]⟩,
    ⟨-11202586235584493487,2784267906814155407360⟩,
    ⟨-2624923312358876847,722716336967553843200⟩⟩

def packet0184 : StripRowPacket :=
  ⟨⟨⟨8,1,6,16⟩,
    ![450,1364,2644,4122,5600,6877,7783],![485,1401,2677,4147,5617,6888,7788]⟩,
    ⟨-7622864784054282550387102154791,1768242267630296073169033803980800⟩,
    ⟨-57441895036989784468636237912611,14647620957733877103949232986849280⟩⟩

def packet0185 : StripRowPacket :=
  ⟨⟨⟨8,1,6,17⟩,
    ![466,1383,2661,4135,5608,6882,7784],![500,1421,2694,4161,5626,6892,7789]⟩,
    ⟨-115186386714466876610535295029847,28291876282084737170704540863692800⟩,
    ⟨-26960368121544799384802875427339,7323810478866938551974616493424640⟩⟩

def packet0186 : StripRowPacket :=
  ⟨⟨⟨8,0,6,18⟩,
    ![490,1409,2683,4152,5619,6887,7786],![525,1448,2719,4179,5638,6898,7791]⟩,
    ⟨-5274984701001386903,1392133953407077703680⟩,
    ⟨-377673824672199529,111187128764239052800⟩⟩

def packet0187 : StripRowPacket :=
  ⟨⟨⟨8,0,6,19⟩,
    ![505,1428,2701,4165,5628,6892,7787],![539,1467,2737,4194,5647,6903,7793]⟩,
    ⟨-1979470513684210825,556853581362831081472⟩,
    ⟨-228483640837971703,72271633696755384320⟩⟩

def packet0188 : StripRowPacket :=
  ⟨⟨⟨8,1,6,18⟩,
    ![482,1402,2678,4148,5616,6886,7785],![514,1440,2712,4175,5635,6897,7791]⟩,
    ⟨-54203468442032616207438477791519,14145938141042368585352270431846400⟩,
    ⟨-10079915489837882614115052759349,2929524191546775420789846597369856⟩⟩

def packet0189 : StripRowPacket :=
  ⟨⟨⟨8,1,6,19⟩,
    ![496,1421,2695,4162,5625,6891,7787],![528,1458,2730,4189,5645,6902,7792]⟩,
    ⟨-9238862459423962565383510557839,2571988752916794288245867351244800⟩,
    ⟨-1065418605802027894807835834973,332900476312133570544300749701120⟩⟩

def packet0190 : StripRowPacket :=
  ⟨⟨⟨8,2,6,16⟩,
    ![443,1358,2639,4118,5597,6876,7782],![476,1394,2671,4143,5614,6886,7788]⟩,
    ⟨-2155531226879689800134453899,493920935934650410539937951744⟩,
    ⟨-12137699171551175324587714766903,3053170870647725012626542885994496⟩⟩

def packet0191 : StripRowPacket :=
  ⟨⟨⟨8,2,6,17⟩,
    ![459,1377,2656,4131,5605,6880,7784],![491,1413,2688,4157,5623,6891,7789]⟩,
    ⟨-358110176492718278323951113337,86930084724498472255029079506944⟩,
    ⟨-438032897190503444637843690811,117429648871066346639482418692096⟩⟩

def packets007 : List StripRowPacket :=
  [packet0168, packet0169, packet0170, packet0171, packet0172, packet0173,
   packet0174, packet0175, packet0176, packet0177, packet0178, packet0179,
   packet0180, packet0181, packet0182, packet0183, packet0184, packet0185,
   packet0186, packet0187, packet0188, packet0189, packet0190, packet0191]

theorem packet0168_membership : packet0168 ∈ packets007 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0168_shape : checkStripShape packet0168.row = true := by
  decide +kernel

private theorem packet0168_cache : checkStripCache packet0168 = true := by
  decide +kernel

private theorem packet0168_pair (i : Fin 7) : checkEdgePair packet0168 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0168_ok : checkStripPacket packet0168 = true :=
  checkStripPacket_intro packet0168_shape packet0168_cache packet0168_pair

theorem packet0169_membership : packet0169 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0169_shape : checkStripShape packet0169.row = true := by
  decide +kernel

private theorem packet0169_cache : checkStripCache packet0169 = true := by
  decide +kernel

private theorem packet0169_pair (i : Fin 7) : checkEdgePair packet0169 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0169_ok : checkStripPacket packet0169 = true :=
  checkStripPacket_intro packet0169_shape packet0169_cache packet0169_pair

theorem packet0170_membership : packet0170 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0170_shape : checkStripShape packet0170.row = true := by
  decide +kernel

private theorem packet0170_cache : checkStripCache packet0170 = true := by
  decide +kernel

private theorem packet0170_pair (i : Fin 7) : checkEdgePair packet0170 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0170_ok : checkStripPacket packet0170 = true :=
  checkStripPacket_intro packet0170_shape packet0170_cache packet0170_pair

theorem packet0171_membership : packet0171 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0171_shape : checkStripShape packet0171.row = true := by
  decide +kernel

private theorem packet0171_cache : checkStripCache packet0171 = true := by
  decide +kernel

private theorem packet0171_pair (i : Fin 7) : checkEdgePair packet0171 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0171_ok : checkStripPacket packet0171 = true :=
  checkStripPacket_intro packet0171_shape packet0171_cache packet0171_pair

theorem packet0172_membership : packet0172 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0172_shape : checkStripShape packet0172.row = true := by
  decide +kernel

private theorem packet0172_cache : checkStripCache packet0172 = true := by
  decide +kernel

private theorem packet0172_pair (i : Fin 7) : checkEdgePair packet0172 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0172_ok : checkStripPacket packet0172 = true :=
  checkStripPacket_intro packet0172_shape packet0172_cache packet0172_pair

theorem packet0173_membership : packet0173 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0173_shape : checkStripShape packet0173.row = true := by
  decide +kernel

private theorem packet0173_cache : checkStripCache packet0173 = true := by
  decide +kernel

private theorem packet0173_pair (i : Fin 7) : checkEdgePair packet0173 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0173_ok : checkStripPacket packet0173 = true :=
  checkStripPacket_intro packet0173_shape packet0173_cache packet0173_pair

theorem packet0174_membership : packet0174 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0174_shape : checkStripShape packet0174.row = true := by
  decide +kernel

private theorem packet0174_cache : checkStripCache packet0174 = true := by
  decide +kernel

private theorem packet0174_pair (i : Fin 7) : checkEdgePair packet0174 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0174_ok : checkStripPacket packet0174 = true :=
  checkStripPacket_intro packet0174_shape packet0174_cache packet0174_pair

theorem packet0175_membership : packet0175 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0175_shape : checkStripShape packet0175.row = true := by
  decide +kernel

private theorem packet0175_cache : checkStripCache packet0175 = true := by
  decide +kernel

private theorem packet0175_pair (i : Fin 7) : checkEdgePair packet0175 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0175_ok : checkStripPacket packet0175 = true :=
  checkStripPacket_intro packet0175_shape packet0175_cache packet0175_pair

theorem packet0176_membership : packet0176 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0176_shape : checkStripShape packet0176.row = true := by
  decide +kernel

private theorem packet0176_cache : checkStripCache packet0176 = true := by
  decide +kernel

private theorem packet0176_pair (i : Fin 7) : checkEdgePair packet0176 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0176_ok : checkStripPacket packet0176 = true :=
  checkStripPacket_intro packet0176_shape packet0176_cache packet0176_pair

theorem packet0177_membership : packet0177 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0177_shape : checkStripShape packet0177.row = true := by
  decide +kernel

private theorem packet0177_cache : checkStripCache packet0177 = true := by
  decide +kernel

private theorem packet0177_pair (i : Fin 7) : checkEdgePair packet0177 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0177_ok : checkStripPacket packet0177 = true :=
  checkStripPacket_intro packet0177_shape packet0177_cache packet0177_pair

theorem packet0178_membership : packet0178 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0178_shape : checkStripShape packet0178.row = true := by
  decide +kernel

private theorem packet0178_cache : checkStripCache packet0178 = true := by
  decide +kernel

private theorem packet0178_pair (i : Fin 7) : checkEdgePair packet0178 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0178_ok : checkStripPacket packet0178 = true :=
  checkStripPacket_intro packet0178_shape packet0178_cache packet0178_pair

theorem packet0179_membership : packet0179 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0179_shape : checkStripShape packet0179.row = true := by
  decide +kernel

private theorem packet0179_cache : checkStripCache packet0179 = true := by
  decide +kernel

private theorem packet0179_pair (i : Fin 7) : checkEdgePair packet0179 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0179_ok : checkStripPacket packet0179 = true :=
  checkStripPacket_intro packet0179_shape packet0179_cache packet0179_pair

theorem packet0180_membership : packet0180 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0180_shape : checkStripShape packet0180.row = true := by
  decide +kernel

private theorem packet0180_cache : checkStripCache packet0180 = true := by
  decide +kernel

private theorem packet0180_pair (i : Fin 7) : checkEdgePair packet0180 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0180_ok : checkStripPacket packet0180 = true :=
  checkStripPacket_intro packet0180_shape packet0180_cache packet0180_pair

theorem packet0181_membership : packet0181 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0181_shape : checkStripShape packet0181.row = true := by
  decide +kernel

private theorem packet0181_cache : checkStripCache packet0181 = true := by
  decide +kernel

private theorem packet0181_pair (i : Fin 7) : checkEdgePair packet0181 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0181_ok : checkStripPacket packet0181 = true :=
  checkStripPacket_intro packet0181_shape packet0181_cache packet0181_pair

theorem packet0182_membership : packet0182 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0182_shape : checkStripShape packet0182.row = true := by
  decide +kernel

private theorem packet0182_cache : checkStripCache packet0182 = true := by
  decide +kernel

private theorem packet0182_pair (i : Fin 7) : checkEdgePair packet0182 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0182_ok : checkStripPacket packet0182 = true :=
  checkStripPacket_intro packet0182_shape packet0182_cache packet0182_pair

theorem packet0183_membership : packet0183 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0183_shape : checkStripShape packet0183.row = true := by
  decide +kernel

private theorem packet0183_cache : checkStripCache packet0183 = true := by
  decide +kernel

private theorem packet0183_pair (i : Fin 7) : checkEdgePair packet0183 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0183_ok : checkStripPacket packet0183 = true :=
  checkStripPacket_intro packet0183_shape packet0183_cache packet0183_pair

theorem packet0184_membership : packet0184 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0184_shape : checkStripShape packet0184.row = true := by
  decide +kernel

private theorem packet0184_cache : checkStripCache packet0184 = true := by
  decide +kernel

private theorem packet0184_pair (i : Fin 7) : checkEdgePair packet0184 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0184_ok : checkStripPacket packet0184 = true :=
  checkStripPacket_intro packet0184_shape packet0184_cache packet0184_pair

theorem packet0185_membership : packet0185 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0185_shape : checkStripShape packet0185.row = true := by
  decide +kernel

private theorem packet0185_cache : checkStripCache packet0185 = true := by
  decide +kernel

private theorem packet0185_pair (i : Fin 7) : checkEdgePair packet0185 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0185_ok : checkStripPacket packet0185 = true :=
  checkStripPacket_intro packet0185_shape packet0185_cache packet0185_pair

theorem packet0186_membership : packet0186 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0186_shape : checkStripShape packet0186.row = true := by
  decide +kernel

private theorem packet0186_cache : checkStripCache packet0186 = true := by
  decide +kernel

private theorem packet0186_pair (i : Fin 7) : checkEdgePair packet0186 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0186_ok : checkStripPacket packet0186 = true :=
  checkStripPacket_intro packet0186_shape packet0186_cache packet0186_pair

theorem packet0187_membership : packet0187 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0187_shape : checkStripShape packet0187.row = true := by
  decide +kernel

private theorem packet0187_cache : checkStripCache packet0187 = true := by
  decide +kernel

private theorem packet0187_pair (i : Fin 7) : checkEdgePair packet0187 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0187_ok : checkStripPacket packet0187 = true :=
  checkStripPacket_intro packet0187_shape packet0187_cache packet0187_pair

theorem packet0188_membership : packet0188 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0188_shape : checkStripShape packet0188.row = true := by
  decide +kernel

private theorem packet0188_cache : checkStripCache packet0188 = true := by
  decide +kernel

private theorem packet0188_pair (i : Fin 7) : checkEdgePair packet0188 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0188_ok : checkStripPacket packet0188 = true :=
  checkStripPacket_intro packet0188_shape packet0188_cache packet0188_pair

theorem packet0189_membership : packet0189 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0189_shape : checkStripShape packet0189.row = true := by
  decide +kernel

private theorem packet0189_cache : checkStripCache packet0189 = true := by
  decide +kernel

private theorem packet0189_pair (i : Fin 7) : checkEdgePair packet0189 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0189_ok : checkStripPacket packet0189 = true :=
  checkStripPacket_intro packet0189_shape packet0189_cache packet0189_pair

theorem packet0190_membership : packet0190 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0190_shape : checkStripShape packet0190.row = true := by
  decide +kernel

private theorem packet0190_cache : checkStripCache packet0190 = true := by
  decide +kernel

private theorem packet0190_pair (i : Fin 7) : checkEdgePair packet0190 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0190_ok : checkStripPacket packet0190 = true :=
  checkStripPacket_intro packet0190_shape packet0190_cache packet0190_pair

theorem packet0191_membership : packet0191 ∈ packets007 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0191_shape : checkStripShape packet0191.row = true := by
  decide +kernel

private theorem packet0191_cache : checkStripCache packet0191 = true := by
  decide +kernel

private theorem packet0191_pair (i : Fin 7) : checkEdgePair packet0191 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0191_ok : checkStripPacket packet0191 = true :=
  checkStripPacket_intro packet0191_shape packet0191_cache packet0191_pair

theorem packets007_checked : packets007.all checkStripPacket = true := by
  simp only [packets007, List.all_cons, List.all_nil, Bool.true_and, packet0168_ok,
    packet0169_ok, packet0170_ok, packet0171_ok, packet0172_ok, packet0173_ok,
    packet0174_ok, packet0175_ok, packet0176_ok, packet0177_ok, packet0178_ok,
    packet0179_ok, packet0180_ok, packet0181_ok, packet0182_ok, packet0183_ok,
    packet0184_ok, packet0185_ok, packet0186_ok, packet0187_ok, packet0188_ok,
    packet0189_ok, packet0190_ok, packet0191_ok]

theorem packets007_valid : packets007.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
