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

def packet1008 : StripRowPacket :=
  ⟨⟨⟨5,23,4,14⟩,
    ![466,1492,2910,4499,6018,7238,7981],![476,1518,2955,4564,6100,7333,8096]⟩,
    ⟨424293872616384462097,28031853643679972669440⟩,
    ⟨3795307643082637447,209642866703979554560⟩⟩

def packet1009 : StripRowPacket :=
  ⟨⟨⟨5,23,4,15⟩,
    ![471,1507,2939,4544,6076,7309,8063],![480,1530,2980,4602,6150,7395,8192]⟩,
    ⟨198448698282441060981,11212741457471989067776⟩,
    ⟨1687987,81677024⟩⟩

def packet1010 : StripRowPacket :=
  ⟨⟨⟨4,12,3,0⟩,
    ![0,818,2095,3663,5280,6706,7728],![223,987,2229,3759,5345,6741,7741]⟩,
    ⟨-19829621453,921535034992⟩,
    ⟨-441510386451652433,28555113063356658688⟩⟩

def packet1011 : StripRowPacket :=
  ⟨⟨⟨5,24,3,1⟩,
    ![192,959,2210,3748,5335,6735,7737],![324,1126,2360,3863,5413,6776,7752]⟩,
    ⟨-1028868356361584389,64688352104670044608⟩,
    ⟨-10820670160239511783,1052007395502154144768⟩⟩

def packet1012 : StripRowPacket :=
  ⟨⟨⟨5,25,4,2⟩,
    ![192,957,2206,3743,5331,6732,7736],![277,1051,2286,3802,5372,6754,7745]⟩,
    ⟨-10079342826229554078951,622382409054092642695168⟩,
    ⟨-2401313830942355564498845,182707107329938474337646592⟩⟩

def packet1013 : StripRowPacket :=
  ⟨⟨⟨5,25,4,3⟩,
    ![261,1033,2271,3792,5362,6748,7741],![323,1123,2356,3858,5408,6773,7751]⟩,
    ⟨-1531416650399797002431,113160438009835025944576⟩,
    ⟨-478728526472752483515439,45676776832484618584411648⟩⟩

def packet1014 : StripRowPacket :=
  ⟨⟨⟨4,13,3,0⟩,
    ![0,814,2087,3653,5271,6700,7726],![222,982,2221,3749,5336,6736,7739]⟩,
    ⟨-195052163,8753047160⟩,
    ⟨-14587829248182189093,909059514856686702080⟩⟩

def packet1015 : StripRowPacket :=
  ⟨⟨⟨5,26,4,2⟩,
    ![192,955,2202,3738,5327,6729,7735],![276,1049,2282,3798,5367,6752,7744]⟩,
    ⟨-262753740843853702848841,15942108930606585131525120⟩,
    ⟨-1907981645338151988389,142547884757711788625920⟩⟩

def packet1016 : StripRowPacket :=
  ⟨⟨⟨5,26,4,3⟩,
    ![261,1031,2267,3787,5358,6745,7740],![322,1121,2352,3853,5404,6771,7750]⟩,
    ⟨-439084965592229311513659,31884217861213170263050240⟩,
    ⟨-4184195096034530308253,392006683083707418721280⟩⟩

def packet1017 : StripRowPacket :=
  ⟨⟨⟨5,27,4,2⟩,
    ![192,954,2199,3734,5323,6727,7734],![275,1047,2278,3793,5363,6749,7743]⟩,
    ⟨-9988304818526440333,595745638097703368704⟩,
    ⟨-1190025007405996043265,87345598719524885003264⟩⟩

def packet1018 : StripRowPacket :=
  ⟨⟨⟨5,27,4,3⟩,
    ![260,1029,2263,3783,5354,6743,7739],![321,1119,2348,3849,5400,6768,7749]⟩,
    ⟨-83446845079193697859,5957456380977033687040⟩,
    ⟨-1186245814188358847983,109181998399406106254080⟩⟩

def packet1019 : StripRowPacket :=
  ⟨⟨⟨5,24,4,4⟩,
    ![312,1109,2345,3851,5402,6769,7747],![358,1192,2433,3925,5455,6798,7759]⟩,
    ⟨-7851171027349255,735094910280341416⟩,
    ⟨-32287880885271368579,4208029582008616579072⟩⟩

def packet1020 : StripRowPacket :=
  ⟨⟨⟨5,24,4,5⟩,
    ![349,1178,2418,3911,5443,6790,7754],![384,1251,2507,3992,5503,6824,7767]⟩,
    ⟨-1043840794858618931,129376704209340089216⟩,
    ⟨-10646540564792345013,2104014791004308289536⟩⟩

def packet1021 : StripRowPacket :=
  ⟨⟨⟨5,25,4,4⟩,
    ![311,1107,2341,3846,5398,6766,7747],![357,1189,2428,3920,5450,6796,7758]⟩,
    ⟨-3383120164084106473895,311191204527046321347584⟩,
    ⟨-1428514380839664303624667,182707107329938474337646592⟩⟩

def packet1022 : StripRowPacket :=
  ⟨⟨⟨5,25,4,5⟩,
    ![349,1176,2414,3906,5439,6788,7753],![383,1248,2502,3987,5499,6822,7766]⟩,
    ⟨-10219378158275084764419,1244764818108185285390336⟩,
    ⟨-471057327894159336593789,91353553664969237168823296⟩⟩

def packet1023 : StripRowPacket :=
  ⟨⟨⟨5,24,4,6⟩,
    ![377,1239,2491,3976,5490,6815,7762],![404,1302,2578,4063,5557,6855,7777]⟩,
    ⟨-352937744451884491,64688352104670044608⟩,
    ⟨-10298281373898011473,4208029582008616579072⟩⟩

def packet1024 : StripRowPacket :=
  ⟨⟨⟨5,24,4,7⟩,
    ![398,1290,2562,4046,5543,6845,7772],![420,1346,2645,4137,5618,6891,7790]⟩,
    ⟨-367910182948919033,129376704209340089216⟩,
    ⟨87064797723583385,526003697751077072384⟩⟩

def packet1025 : StripRowPacket :=
  ⟨⟨⟨5,25,4,6⟩,
    ![376,1236,2487,3972,5486,6813,7762],![403,1299,2574,4058,5553,6852,7777]⟩,
    ⟨-3453137830106871816629,622382409054092642695168⟩,
    ⟨-65102132962424720392927,26101015332848353476806656⟩⟩

def packet1026 : StripRowPacket :=
  ⟨⟨⟨5,25,4,7⟩,
    ![397,1288,2558,4041,5539,6843,7771],![419,1343,2641,4132,5614,6889,7789]⟩,
    ⟨-3593173162152402502097,1244764818108185285390336⟩,
    ⟨3835599289296573460825,22838388416242309292205824⟩⟩

def packet1027 : StripRowPacket :=
  ⟨⟨⟨5,26,4,4⟩,
    ![311,1105,2337,3842,5394,6764,7746],![356,1187,2424,3915,5446,6793,7757]⟩,
    ⟨-6781970182629831102493,613158035792560966597120⟩,
    ⟨-192088656454716470673,24123488189766610382848⟩⟩

def packet1028 : StripRowPacket :=
  ⟨⟨⟨5,26,4,5⟩,
    ![348,1173,2411,3902,5435,6785,7753],![382,1245,2498,3982,5494,6819,7766]⟩,
    ⟨-266239933401273123145613,31884217861213170263050240⟩,
    ⟨-4117372477487509977239,784013366167414837442560⟩⟩

def packet1029 : StripRowPacket :=
  ⟨⟨⟨5,27,4,4⟩,
    ![310,1103,2334,3837,5390,6761,7745],![355,1184,2420,3911,5442,6791,7756]⟩,
    ⟨-16752660493280748097,1489364095244258421760⟩,
    ⟨-3539841476476890567539,436727993597624425016320⟩⟩

def packet1030 : StripRowPacket :=
  ⟨⟨⟨5,27,4,5⟩,
    ![347,1171,2407,3898,5432,6783,7752],![381,1243,2494,3978,5491,6817,7765]⟩,
    ⟨-50574438867052286917,5957456380977033687040⟩,
    ⟨-1167349848100172871573,218363996798812212508160⟩⟩

def packet1031 : StripRowPacket :=
  ⟨⟨⟨5,26,4,6⟩,
    ![375,1234,2483,3967,5482,6811,7761],![402,1297,2569,4054,5549,6850,7776]⟩,
    ⟨-17981741730579502896159,3188421786121317026305024⟩,
    ⟨-3983727240393469315211,1568026732334829674885120⟩⟩

def packets042 : List StripRowPacket :=
  [packet1008, packet1009, packet1010, packet1011, packet1012, packet1013,
   packet1014, packet1015, packet1016, packet1017, packet1018, packet1019,
   packet1020, packet1021, packet1022, packet1023, packet1024, packet1025,
   packet1026, packet1027, packet1028, packet1029, packet1030, packet1031]

theorem packet1008_membership : packet1008 ∈ packets042 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1008_shape : checkStripShape packet1008.row = true := by
  decide +kernel

private theorem packet1008_cache : checkStripCache packet1008 = true := by
  decide +kernel

private theorem packet1008_pair (i : Fin 7) : checkEdgePair packet1008 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1008_ok : checkStripPacket packet1008 = true :=
  checkStripPacket_intro packet1008_shape packet1008_cache packet1008_pair

theorem packet1009_membership : packet1009 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1009_shape : checkStripShape packet1009.row = true := by
  decide +kernel

private theorem packet1009_cache : checkStripCache packet1009 = true := by
  decide +kernel

private theorem packet1009_pair (i : Fin 7) : checkEdgePair packet1009 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1009_ok : checkStripPacket packet1009 = true :=
  checkStripPacket_intro packet1009_shape packet1009_cache packet1009_pair

theorem packet1010_membership : packet1010 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1010_shape : checkStripShape packet1010.row = true := by
  decide +kernel

private theorem packet1010_cache : checkStripCache packet1010 = true := by
  decide +kernel

private theorem packet1010_pair (i : Fin 7) : checkEdgePair packet1010 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1010_ok : checkStripPacket packet1010 = true :=
  checkStripPacket_intro packet1010_shape packet1010_cache packet1010_pair

theorem packet1011_membership : packet1011 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1011_shape : checkStripShape packet1011.row = true := by
  decide +kernel

private theorem packet1011_cache : checkStripCache packet1011 = true := by
  decide +kernel

private theorem packet1011_pair (i : Fin 7) : checkEdgePair packet1011 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1011_ok : checkStripPacket packet1011 = true :=
  checkStripPacket_intro packet1011_shape packet1011_cache packet1011_pair

theorem packet1012_membership : packet1012 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1012_shape : checkStripShape packet1012.row = true := by
  decide +kernel

private theorem packet1012_cache : checkStripCache packet1012 = true := by
  decide +kernel

private theorem packet1012_pair (i : Fin 7) : checkEdgePair packet1012 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1012_ok : checkStripPacket packet1012 = true :=
  checkStripPacket_intro packet1012_shape packet1012_cache packet1012_pair

theorem packet1013_membership : packet1013 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1013_shape : checkStripShape packet1013.row = true := by
  decide +kernel

private theorem packet1013_cache : checkStripCache packet1013 = true := by
  decide +kernel

private theorem packet1013_pair (i : Fin 7) : checkEdgePair packet1013 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1013_ok : checkStripPacket packet1013 = true :=
  checkStripPacket_intro packet1013_shape packet1013_cache packet1013_pair

theorem packet1014_membership : packet1014 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1014_shape : checkStripShape packet1014.row = true := by
  decide +kernel

private theorem packet1014_cache : checkStripCache packet1014 = true := by
  decide +kernel

private theorem packet1014_pair (i : Fin 7) : checkEdgePair packet1014 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1014_ok : checkStripPacket packet1014 = true :=
  checkStripPacket_intro packet1014_shape packet1014_cache packet1014_pair

theorem packet1015_membership : packet1015 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1015_shape : checkStripShape packet1015.row = true := by
  decide +kernel

private theorem packet1015_cache : checkStripCache packet1015 = true := by
  decide +kernel

private theorem packet1015_pair (i : Fin 7) : checkEdgePair packet1015 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1015_ok : checkStripPacket packet1015 = true :=
  checkStripPacket_intro packet1015_shape packet1015_cache packet1015_pair

theorem packet1016_membership : packet1016 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1016_shape : checkStripShape packet1016.row = true := by
  decide +kernel

private theorem packet1016_cache : checkStripCache packet1016 = true := by
  decide +kernel

private theorem packet1016_pair (i : Fin 7) : checkEdgePair packet1016 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1016_ok : checkStripPacket packet1016 = true :=
  checkStripPacket_intro packet1016_shape packet1016_cache packet1016_pair

theorem packet1017_membership : packet1017 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1017_shape : checkStripShape packet1017.row = true := by
  decide +kernel

private theorem packet1017_cache : checkStripCache packet1017 = true := by
  decide +kernel

private theorem packet1017_pair (i : Fin 7) : checkEdgePair packet1017 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1017_ok : checkStripPacket packet1017 = true :=
  checkStripPacket_intro packet1017_shape packet1017_cache packet1017_pair

theorem packet1018_membership : packet1018 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1018_shape : checkStripShape packet1018.row = true := by
  decide +kernel

private theorem packet1018_cache : checkStripCache packet1018 = true := by
  decide +kernel

private theorem packet1018_pair (i : Fin 7) : checkEdgePair packet1018 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1018_ok : checkStripPacket packet1018 = true :=
  checkStripPacket_intro packet1018_shape packet1018_cache packet1018_pair

theorem packet1019_membership : packet1019 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1019_shape : checkStripShape packet1019.row = true := by
  decide +kernel

private theorem packet1019_cache : checkStripCache packet1019 = true := by
  decide +kernel

private theorem packet1019_pair (i : Fin 7) : checkEdgePair packet1019 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1019_ok : checkStripPacket packet1019 = true :=
  checkStripPacket_intro packet1019_shape packet1019_cache packet1019_pair

theorem packet1020_membership : packet1020 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1020_shape : checkStripShape packet1020.row = true := by
  decide +kernel

private theorem packet1020_cache : checkStripCache packet1020 = true := by
  decide +kernel

private theorem packet1020_pair (i : Fin 7) : checkEdgePair packet1020 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1020_ok : checkStripPacket packet1020 = true :=
  checkStripPacket_intro packet1020_shape packet1020_cache packet1020_pair

theorem packet1021_membership : packet1021 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1021_shape : checkStripShape packet1021.row = true := by
  decide +kernel

private theorem packet1021_cache : checkStripCache packet1021 = true := by
  decide +kernel

private theorem packet1021_pair (i : Fin 7) : checkEdgePair packet1021 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1021_ok : checkStripPacket packet1021 = true :=
  checkStripPacket_intro packet1021_shape packet1021_cache packet1021_pair

theorem packet1022_membership : packet1022 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1022_shape : checkStripShape packet1022.row = true := by
  decide +kernel

private theorem packet1022_cache : checkStripCache packet1022 = true := by
  decide +kernel

private theorem packet1022_pair (i : Fin 7) : checkEdgePair packet1022 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1022_ok : checkStripPacket packet1022 = true :=
  checkStripPacket_intro packet1022_shape packet1022_cache packet1022_pair

theorem packet1023_membership : packet1023 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1023_shape : checkStripShape packet1023.row = true := by
  decide +kernel

private theorem packet1023_cache : checkStripCache packet1023 = true := by
  decide +kernel

private theorem packet1023_pair (i : Fin 7) : checkEdgePair packet1023 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1023_ok : checkStripPacket packet1023 = true :=
  checkStripPacket_intro packet1023_shape packet1023_cache packet1023_pair

theorem packet1024_membership : packet1024 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1024_shape : checkStripShape packet1024.row = true := by
  decide +kernel

private theorem packet1024_cache : checkStripCache packet1024 = true := by
  decide +kernel

private theorem packet1024_pair (i : Fin 7) : checkEdgePair packet1024 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1024_ok : checkStripPacket packet1024 = true :=
  checkStripPacket_intro packet1024_shape packet1024_cache packet1024_pair

theorem packet1025_membership : packet1025 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1025_shape : checkStripShape packet1025.row = true := by
  decide +kernel

private theorem packet1025_cache : checkStripCache packet1025 = true := by
  decide +kernel

private theorem packet1025_pair (i : Fin 7) : checkEdgePair packet1025 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1025_ok : checkStripPacket packet1025 = true :=
  checkStripPacket_intro packet1025_shape packet1025_cache packet1025_pair

theorem packet1026_membership : packet1026 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1026_shape : checkStripShape packet1026.row = true := by
  decide +kernel

private theorem packet1026_cache : checkStripCache packet1026 = true := by
  decide +kernel

private theorem packet1026_pair (i : Fin 7) : checkEdgePair packet1026 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1026_ok : checkStripPacket packet1026 = true :=
  checkStripPacket_intro packet1026_shape packet1026_cache packet1026_pair

theorem packet1027_membership : packet1027 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1027_shape : checkStripShape packet1027.row = true := by
  decide +kernel

private theorem packet1027_cache : checkStripCache packet1027 = true := by
  decide +kernel

private theorem packet1027_pair (i : Fin 7) : checkEdgePair packet1027 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1027_ok : checkStripPacket packet1027 = true :=
  checkStripPacket_intro packet1027_shape packet1027_cache packet1027_pair

theorem packet1028_membership : packet1028 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1028_shape : checkStripShape packet1028.row = true := by
  decide +kernel

private theorem packet1028_cache : checkStripCache packet1028 = true := by
  decide +kernel

private theorem packet1028_pair (i : Fin 7) : checkEdgePair packet1028 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1028_ok : checkStripPacket packet1028 = true :=
  checkStripPacket_intro packet1028_shape packet1028_cache packet1028_pair

theorem packet1029_membership : packet1029 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1029_shape : checkStripShape packet1029.row = true := by
  decide +kernel

private theorem packet1029_cache : checkStripCache packet1029 = true := by
  decide +kernel

private theorem packet1029_pair (i : Fin 7) : checkEdgePair packet1029 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1029_ok : checkStripPacket packet1029 = true :=
  checkStripPacket_intro packet1029_shape packet1029_cache packet1029_pair

theorem packet1030_membership : packet1030 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1030_shape : checkStripShape packet1030.row = true := by
  decide +kernel

private theorem packet1030_cache : checkStripCache packet1030 = true := by
  decide +kernel

private theorem packet1030_pair (i : Fin 7) : checkEdgePair packet1030 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1030_ok : checkStripPacket packet1030 = true :=
  checkStripPacket_intro packet1030_shape packet1030_cache packet1030_pair

theorem packet1031_membership : packet1031 ∈ packets042 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1031_shape : checkStripShape packet1031.row = true := by
  decide +kernel

private theorem packet1031_cache : checkStripCache packet1031 = true := by
  decide +kernel

private theorem packet1031_pair (i : Fin 7) : checkEdgePair packet1031 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1031_ok : checkStripPacket packet1031 = true :=
  checkStripPacket_intro packet1031_shape packet1031_cache packet1031_pair

theorem packets042_checked : packets042.all checkStripPacket = true := by
  simp only [packets042, List.all_cons, List.all_nil, Bool.true_and, packet1008_ok,
    packet1009_ok, packet1010_ok, packet1011_ok, packet1012_ok, packet1013_ok,
    packet1014_ok, packet1015_ok, packet1016_ok, packet1017_ok, packet1018_ok,
    packet1019_ok, packet1020_ok, packet1021_ok, packet1022_ok, packet1023_ok,
    packet1024_ok, packet1025_ok, packet1026_ok, packet1027_ok, packet1028_ok,
    packet1029_ok, packet1030_ok, packet1031_ok]

theorem packets042_valid : packets042.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
