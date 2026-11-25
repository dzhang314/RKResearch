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

def packet0024 : StripRowPacket :=
  ⟨⟨⟨8,2,6,4⟩,
    ![133,1143,2467,3993,5517,6836,7770],![201,1171,2490,4010,5529,6843,7774]⟩,
    ⟨-158633332297027730705054290217,21732521181124618063757269876736⟩,
    ⟨-1624909638979092653279466187439,234859297742132693278964837384192⟩⟩

def packet0025 : StripRowPacket :=
  ⟨⟨⟨8,2,6,5⟩,
    ![168,1159,2479,4001,5523,6838,7771],![232,1187,2502,4019,5535,6846,7775]⟩,
    ⟨-55751819068182163301864035271,7902734974954406568639007227904⟩,
    ⟨-10187490731065059364314640815445,1526585435323862506313271442997248⟩⟩

def packet0026 : StripRowPacket :=
  ⟨⟨⟨8,3,6,4⟩,
    ![132,1136,2461,3988,5514,6834,7769],![198,1164,2483,4005,5526,6842,7774]⟩,
    ⟨-1151029888584486938882183099,155346407879171598667935678464⟩,
    ⟨-1125455492410457985617551435,160137549235904757255126941696⟩⟩

def packet0027 : StripRowPacket :=
  ⟨⟨⟨8,3,6,5⟩,
    ![166,1152,2473,3997,5520,6837,7770],![228,1180,2496,4014,5532,6845,7775]⟩,
    ⟨-22245855411089183061020955459,3106928157583431973358713569280⟩,
    ⟨-2713576166698272770099184033,400343873089761893137817354240⟩⟩

def packet0028 : StripRowPacket :=
  ⟨⟨⟨8,2,6,6⟩,
    ![201,1175,2491,4010,5528,6841,7772],![261,1204,2515,4029,5541,6849,7776]⟩,
    ⟨-22769488088919102685415062119,3343464797096095086731887673344⟩,
    ⟨-19626137617532032964625502825073,3053170870647725012626542885994496⟩⟩

def packet0029 : StripRowPacket :=
  ⟨⟨⟨8,2,6,7⟩,
    ![233,1192,2504,4019,5534,6844,7772],![288,1222,2529,4038,5547,6852,7777]⟩,
    ⟨-30039124782831028595846254853,4575267617078866960791004184576⟩,
    ⟨-2359661721616743400077715502407,381646358830965626578317860749312⟩⟩

def packet0030 : StripRowPacket :=
  ⟨⟨⟨8,3,6,6⟩,
    ![199,1168,2485,4006,5525,6840,7771],![257,1197,2509,4024,5538,6848,7776]⟩,
    ⟨-10735556525244313672199124469,1553464078791715986679356784640⟩,
    ⟨-275106694986357955384683103,42141460325238094014507089920⟩⟩

def packet0031 : StripRowPacket :=
  ⟨⟨⟨8,3,6,7⟩,
    ![230,1185,2498,4015,5531,6843,7772],![284,1215,2523,4034,5544,6851,7777]⟩,
    ⟨-20696370689888071627775542417,3106928157583431973358713569280⟩,
    ⟨-628362759510632095552448731,100085968272440473284454338560⟩⟩

def packet0032 : StripRowPacket :=
  ⟨⟨⟨8,4,6,0⟩,
    ![0,1073,2411,3952,5491,6822,7766],![59,1096,2430,3967,5502,6829,7770]⟩,
    ⟨-455082057999043757,53334367151419557632⟩,
    ⟨-19203093291375557362315821547,2355502021952241394964461649920⟩⟩

def packet0033 : StripRowPacket :=
  ⟨⟨⟨8,4,6,1⟩,
    ![19,1086,2421,3959,5496,6825,7766],![95,1111,2442,3975,5507,6832,7771]⟩,
    ⟨-1369299303975965026033793694421,165400291631312794749434335559680⟩,
    ⟨-845625796202958279583983009,107068273725101881589293711360⟩⟩

def packet0034 : StripRowPacket :=
  ⟨⟨⟨8,5,6,0⟩,
    ![0,1066,2405,3947,5488,6821,7765],![58,1089,2424,3962,5499,6828,7769]⟩,
    ⟨-3784474694902347,437246063892077440⟩,
    ⟨-12005010932236211209047508558177,1450958070828439567023527350435840⟩⟩

def packet0035 : StripRowPacket :=
  ⟨⟨⟨8,5,6,1⟩,
    ![19,1079,2415,3955,5493,6823,7766],![94,1104,2436,3970,5504,6830,7770]⟩,
    ⟨-3388770136836787504483440526421,403572308912338828139462931906560⟩,
    ⟨-528615608231397316873379896387,65952639583110889410160334110720⟩⟩

def packet0036 : StripRowPacket :=
  ⟨⟨⟨8,4,6,2⟩,
    ![58,1100,2432,3967,5501,6827,7767],![130,1125,2453,3983,5512,6835,7772]⟩,
    ⟨-51050009380281435480642765737,6361549678127415182670551367680⟩,
    ⟨-18004441741554606939379430849,2355502021952241394964461649920⟩⟩

def packet0037 : StripRowPacket :=
  ⟨⟨⟨8,4,6,3⟩,
    ![95,1115,2443,3975,5506,6830,7768],![163,1141,2465,3992,5518,6837,7772]⟩,
    ⟨-1285301183798669618959630123903,165400291631312794749434335559680⟩,
    ⟨-870255798332206586395561775,117775101097612069748223082496⟩⟩

def packet0038 : StripRowPacket :=
  ⟨⟨⟨8,5,6,2⟩,
    ![58,1093,2426,3963,5498,6826,7767],![128,1118,2447,3979,5509,6833,7771]⟩,
    ⟨-149296381840897654968339622687,18344195859651764915430133268480⟩,
    ⟨-11254075829945270733381206882851,1450958070828439567023527350435840⟩⟩

def packet0039 : StripRowPacket :=
  ⟨⟨⟨8,5,6,3⟩,
    ![95,1108,2438,3971,5503,6829,7768],![161,1134,2459,3987,5515,6836,7772]⟩,
    ⟨-3180270664162709314123502871807,403572308912338828139462931906560⟩,
    ⟨-2719652069699950123887014011297,362739517707109891755881837608960⟩⟩

def packet0040 : StripRowPacket :=
  ⟨⟨⟨8,6,5,0⟩,
    ![0,1060,2399,3943,5486,6820,7765],![92,1097,2430,3966,5501,6829,7770]⟩,
    ⟨-30285590080940039,3451352915849842432⟩,
    ⟨-226260896989943509029095013920761,27832690416295247735334473185034240⟩⟩

def packet0041 : StripRowPacket :=
  ⟨⟨⟨8,7,5,0⟩,
    ![0,1053,2394,3939,5483,6818,7764],![91,1091,2424,3962,5499,6828,7769]⟩,
    ⟨-260559827953,29302578983392⟩,
    ⟨-933662373709472962778559,113295708903420931177292288⟩⟩

def packet0042 : StripRowPacket :=
  ⟨⟨⟨8,6,5,1⟩,
    ![58,1087,2421,3959,5496,6825,7766],![159,1128,2453,3983,5512,6834,7771]⟩,
    ⟨-4196756759994762645842991,508705651193714583363420160⟩,
    ⟨-21162285567059016156429536843621,2783269041629524773533447318503424⟩⟩

def packet0043 : StripRowPacket :=
  ⟨⟨⟨8,7,5,1⟩,
    ![58,1081,2415,3955,5493,6823,7766],![157,1122,2448,3979,5509,6833,7771]⟩,
    ⟨-62364093818251104541683927569,7460966962027045030733297942528⟩,
    ⟨-6766958567680558138079213,878041744001512216624015232⟩⟩

def packet0044 : StripRowPacket :=
  ⟨⟨⟨8,4,6,4⟩,
    ![131,1130,2455,3984,5511,6833,7769],![195,1157,2477,4001,5523,6840,7773]⟩,
    ⟨-310825530927505478855637084661,41350072907828198687358583889920⟩,
    ⟨-16805790191733656516443040151,2355502021952241394964461649920⟩⟩

def packet0045 : StripRowPacket :=
  ⟨⟨⟨8,4,6,5⟩,
    ![165,1145,2467,3992,5517,6835,7770],![225,1173,2490,4010,5529,6843,7774]⟩,
    ⟨-240260612724274842377093310677,33080058326262558949886867111936⟩,
    ⟨-8103232208411590652487422401,1177751010976120697482230824960⟩⟩

def packet0046 : StripRowPacket :=
  ⟨⟨⟨8,5,6,4⟩,
    ![130,1123,2449,3979,5509,6831,7768],![192,1150,2471,3996,5521,6839,7773]⟩,
    ⟨-21971578055897644421025243175,2882659349373848772424735227904⟩,
    ⟨-2100628145530866051542981041505,290191614165687913404705470087168⟩⟩

def packet0047 : StripRowPacket :=
  ⟨⟨⟨8,5,6,5⟩,
    ![163,1139,2462,3988,5514,6834,7769],![222,1167,2484,4006,5526,6842,7774]⟩,
    ⟨-2971771191488631123763565217193,403572308912338828139462931906560⟩,
    ⟨-5063836588254430009940877184931,725479035414219783511763675217920⟩⟩

def packets001 : List StripRowPacket :=
  [packet0024, packet0025, packet0026, packet0027, packet0028, packet0029,
   packet0030, packet0031, packet0032, packet0033, packet0034, packet0035,
   packet0036, packet0037, packet0038, packet0039, packet0040, packet0041,
   packet0042, packet0043, packet0044, packet0045, packet0046, packet0047]

theorem packet0024_membership : packet0024 ∈ packets001 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0024_shape : checkStripShape packet0024.row = true := by
  decide +kernel

private theorem packet0024_cache : checkStripCache packet0024 = true := by
  decide +kernel

private theorem packet0024_pair (i : Fin 7) : checkEdgePair packet0024 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0024_ok : checkStripPacket packet0024 = true :=
  checkStripPacket_intro packet0024_shape packet0024_cache packet0024_pair

theorem packet0025_membership : packet0025 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0025_shape : checkStripShape packet0025.row = true := by
  decide +kernel

private theorem packet0025_cache : checkStripCache packet0025 = true := by
  decide +kernel

private theorem packet0025_pair (i : Fin 7) : checkEdgePair packet0025 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0025_ok : checkStripPacket packet0025 = true :=
  checkStripPacket_intro packet0025_shape packet0025_cache packet0025_pair

theorem packet0026_membership : packet0026 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0026_shape : checkStripShape packet0026.row = true := by
  decide +kernel

private theorem packet0026_cache : checkStripCache packet0026 = true := by
  decide +kernel

private theorem packet0026_pair (i : Fin 7) : checkEdgePair packet0026 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0026_ok : checkStripPacket packet0026 = true :=
  checkStripPacket_intro packet0026_shape packet0026_cache packet0026_pair

theorem packet0027_membership : packet0027 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0027_shape : checkStripShape packet0027.row = true := by
  decide +kernel

private theorem packet0027_cache : checkStripCache packet0027 = true := by
  decide +kernel

private theorem packet0027_pair (i : Fin 7) : checkEdgePair packet0027 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0027_ok : checkStripPacket packet0027 = true :=
  checkStripPacket_intro packet0027_shape packet0027_cache packet0027_pair

theorem packet0028_membership : packet0028 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0028_shape : checkStripShape packet0028.row = true := by
  decide +kernel

private theorem packet0028_cache : checkStripCache packet0028 = true := by
  decide +kernel

private theorem packet0028_pair (i : Fin 7) : checkEdgePair packet0028 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0028_ok : checkStripPacket packet0028 = true :=
  checkStripPacket_intro packet0028_shape packet0028_cache packet0028_pair

theorem packet0029_membership : packet0029 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0029_shape : checkStripShape packet0029.row = true := by
  decide +kernel

private theorem packet0029_cache : checkStripCache packet0029 = true := by
  decide +kernel

private theorem packet0029_pair (i : Fin 7) : checkEdgePair packet0029 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0029_ok : checkStripPacket packet0029 = true :=
  checkStripPacket_intro packet0029_shape packet0029_cache packet0029_pair

theorem packet0030_membership : packet0030 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0030_shape : checkStripShape packet0030.row = true := by
  decide +kernel

private theorem packet0030_cache : checkStripCache packet0030 = true := by
  decide +kernel

private theorem packet0030_pair (i : Fin 7) : checkEdgePair packet0030 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0030_ok : checkStripPacket packet0030 = true :=
  checkStripPacket_intro packet0030_shape packet0030_cache packet0030_pair

theorem packet0031_membership : packet0031 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0031_shape : checkStripShape packet0031.row = true := by
  decide +kernel

private theorem packet0031_cache : checkStripCache packet0031 = true := by
  decide +kernel

private theorem packet0031_pair (i : Fin 7) : checkEdgePair packet0031 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0031_ok : checkStripPacket packet0031 = true :=
  checkStripPacket_intro packet0031_shape packet0031_cache packet0031_pair

theorem packet0032_membership : packet0032 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0032_shape : checkStripShape packet0032.row = true := by
  decide +kernel

private theorem packet0032_cache : checkStripCache packet0032 = true := by
  decide +kernel

private theorem packet0032_pair (i : Fin 7) : checkEdgePair packet0032 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0032_ok : checkStripPacket packet0032 = true :=
  checkStripPacket_intro packet0032_shape packet0032_cache packet0032_pair

theorem packet0033_membership : packet0033 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0033_shape : checkStripShape packet0033.row = true := by
  decide +kernel

private theorem packet0033_cache : checkStripCache packet0033 = true := by
  decide +kernel

private theorem packet0033_pair (i : Fin 7) : checkEdgePair packet0033 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0033_ok : checkStripPacket packet0033 = true :=
  checkStripPacket_intro packet0033_shape packet0033_cache packet0033_pair

theorem packet0034_membership : packet0034 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0034_shape : checkStripShape packet0034.row = true := by
  decide +kernel

private theorem packet0034_cache : checkStripCache packet0034 = true := by
  decide +kernel

private theorem packet0034_pair (i : Fin 7) : checkEdgePair packet0034 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0034_ok : checkStripPacket packet0034 = true :=
  checkStripPacket_intro packet0034_shape packet0034_cache packet0034_pair

theorem packet0035_membership : packet0035 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0035_shape : checkStripShape packet0035.row = true := by
  decide +kernel

private theorem packet0035_cache : checkStripCache packet0035 = true := by
  decide +kernel

private theorem packet0035_pair (i : Fin 7) : checkEdgePair packet0035 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0035_ok : checkStripPacket packet0035 = true :=
  checkStripPacket_intro packet0035_shape packet0035_cache packet0035_pair

theorem packet0036_membership : packet0036 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0036_shape : checkStripShape packet0036.row = true := by
  decide +kernel

private theorem packet0036_cache : checkStripCache packet0036 = true := by
  decide +kernel

private theorem packet0036_pair (i : Fin 7) : checkEdgePair packet0036 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0036_ok : checkStripPacket packet0036 = true :=
  checkStripPacket_intro packet0036_shape packet0036_cache packet0036_pair

theorem packet0037_membership : packet0037 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0037_shape : checkStripShape packet0037.row = true := by
  decide +kernel

private theorem packet0037_cache : checkStripCache packet0037 = true := by
  decide +kernel

private theorem packet0037_pair (i : Fin 7) : checkEdgePair packet0037 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0037_ok : checkStripPacket packet0037 = true :=
  checkStripPacket_intro packet0037_shape packet0037_cache packet0037_pair

theorem packet0038_membership : packet0038 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0038_shape : checkStripShape packet0038.row = true := by
  decide +kernel

private theorem packet0038_cache : checkStripCache packet0038 = true := by
  decide +kernel

private theorem packet0038_pair (i : Fin 7) : checkEdgePair packet0038 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0038_ok : checkStripPacket packet0038 = true :=
  checkStripPacket_intro packet0038_shape packet0038_cache packet0038_pair

theorem packet0039_membership : packet0039 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0039_shape : checkStripShape packet0039.row = true := by
  decide +kernel

private theorem packet0039_cache : checkStripCache packet0039 = true := by
  decide +kernel

private theorem packet0039_pair (i : Fin 7) : checkEdgePair packet0039 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0039_ok : checkStripPacket packet0039 = true :=
  checkStripPacket_intro packet0039_shape packet0039_cache packet0039_pair

theorem packet0040_membership : packet0040 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0040_shape : checkStripShape packet0040.row = true := by
  decide +kernel

private theorem packet0040_cache : checkStripCache packet0040 = true := by
  decide +kernel

private theorem packet0040_pair (i : Fin 7) : checkEdgePair packet0040 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0040_ok : checkStripPacket packet0040 = true :=
  checkStripPacket_intro packet0040_shape packet0040_cache packet0040_pair

theorem packet0041_membership : packet0041 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0041_shape : checkStripShape packet0041.row = true := by
  decide +kernel

private theorem packet0041_cache : checkStripCache packet0041 = true := by
  decide +kernel

private theorem packet0041_pair (i : Fin 7) : checkEdgePair packet0041 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0041_ok : checkStripPacket packet0041 = true :=
  checkStripPacket_intro packet0041_shape packet0041_cache packet0041_pair

theorem packet0042_membership : packet0042 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0042_shape : checkStripShape packet0042.row = true := by
  decide +kernel

private theorem packet0042_cache : checkStripCache packet0042 = true := by
  decide +kernel

private theorem packet0042_pair (i : Fin 7) : checkEdgePair packet0042 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0042_ok : checkStripPacket packet0042 = true :=
  checkStripPacket_intro packet0042_shape packet0042_cache packet0042_pair

theorem packet0043_membership : packet0043 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0043_shape : checkStripShape packet0043.row = true := by
  decide +kernel

private theorem packet0043_cache : checkStripCache packet0043 = true := by
  decide +kernel

private theorem packet0043_pair (i : Fin 7) : checkEdgePair packet0043 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0043_ok : checkStripPacket packet0043 = true :=
  checkStripPacket_intro packet0043_shape packet0043_cache packet0043_pair

theorem packet0044_membership : packet0044 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0044_shape : checkStripShape packet0044.row = true := by
  decide +kernel

private theorem packet0044_cache : checkStripCache packet0044 = true := by
  decide +kernel

private theorem packet0044_pair (i : Fin 7) : checkEdgePair packet0044 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0044_ok : checkStripPacket packet0044 = true :=
  checkStripPacket_intro packet0044_shape packet0044_cache packet0044_pair

theorem packet0045_membership : packet0045 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0045_shape : checkStripShape packet0045.row = true := by
  decide +kernel

private theorem packet0045_cache : checkStripCache packet0045 = true := by
  decide +kernel

private theorem packet0045_pair (i : Fin 7) : checkEdgePair packet0045 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0045_ok : checkStripPacket packet0045 = true :=
  checkStripPacket_intro packet0045_shape packet0045_cache packet0045_pair

theorem packet0046_membership : packet0046 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0046_shape : checkStripShape packet0046.row = true := by
  decide +kernel

private theorem packet0046_cache : checkStripCache packet0046 = true := by
  decide +kernel

private theorem packet0046_pair (i : Fin 7) : checkEdgePair packet0046 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0046_ok : checkStripPacket packet0046 = true :=
  checkStripPacket_intro packet0046_shape packet0046_cache packet0046_pair

theorem packet0047_membership : packet0047 ∈ packets001 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0047_shape : checkStripShape packet0047.row = true := by
  decide +kernel

private theorem packet0047_cache : checkStripCache packet0047 = true := by
  decide +kernel

private theorem packet0047_pair (i : Fin 7) : checkEdgePair packet0047 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0047_ok : checkStripPacket packet0047 = true :=
  checkStripPacket_intro packet0047_shape packet0047_cache packet0047_pair

theorem packets001_checked : packets001.all checkStripPacket = true := by
  simp only [packets001, List.all_cons, List.all_nil, Bool.true_and, packet0024_ok,
    packet0025_ok, packet0026_ok, packet0027_ok, packet0028_ok, packet0029_ok,
    packet0030_ok, packet0031_ok, packet0032_ok, packet0033_ok, packet0034_ok,
    packet0035_ok, packet0036_ok, packet0037_ok, packet0038_ok, packet0039_ok,
    packet0040_ok, packet0041_ok, packet0042_ok, packet0043_ok, packet0044_ok,
    packet0045_ok, packet0046_ok, packet0047_ok]

theorem packets001_valid : packets001.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
