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

def packet0864 : StripRowPacket :=
  ⟨⟨⟨5,16,4,7⟩,
    ![407,1317,2601,4088,5577,6866,7779],![432,1378,2691,4184,5655,6913,7797]⟩,
    ⟨-4097826069819419,1648370409579046400⟩,
    ⟨2795374259763257,18569732779585461760⟩⟩

def packet0865 : StripRowPacket :=
  ⟨⟨⟨5,17,4,6⟩,
    ![385,1260,2524,4013,5521,6834,7769],![414,1328,2616,4104,5590,6874,7784]⟩,
    ⟨-24132219330359800998993,5046301237197699292436480⟩,
    ⟨-10832037745157912011673,5161396070837113265100800⟩⟩

def packet0866 : StripRowPacket :=
  ⟨⟨⟨5,17,4,7⟩,
    ![406,1312,2595,4082,5572,6863,7778],![430,1373,2684,4177,5650,6910,7796]⟩,
    ⟨-25556827877361198943549,10092602474395398584872960⟩,
    ⟨97981369892314618233,645174508854639158137600⟩⟩

def packet0867 : StripRowPacket :=
  ⟨⟨⟨5,18,4,4⟩,
    ![316,1125,2373,3883,5430,6786,7753],![364,1211,2463,3959,5483,6815,7765]⟩,
    ⟨-6050738577996925474039,637631506749784016504320⟩,
    ⟨-3202480575453948721007,473755352544131472855040⟩⟩

def packet0868 : StripRowPacket :=
  ⟨⟨⟨5,18,4,5⟩,
    ![355,1195,2446,3943,5470,6806,7760],![391,1271,2538,4026,5531,6841,7773]⟩,
    ⟨-3665413732338761399111,510105205399827213203456⟩,
    ⟨-211076442344225152725,47375535254413147285504⟩⟩

def packet0869 : StripRowPacket :=
  ⟨⟨⟨5,19,4,4⟩,
    ![315,1122,2368,3877,5425,6783,7752],![363,1207,2458,3953,5478,6812,7764]⟩,
    ⟨-2113816845097436095,218055063114670093312⟩,
    ⟨-183180144631554242501,26481473535309514861568⟩⟩

def packet0870 : StripRowPacket :=
  ⟨⟨⟨5,19,4,5⟩,
    ![353,1192,2441,3937,5465,6804,7759],![390,1267,2532,4020,5526,6838,7772]⟩,
    ⟨-914222415361818669,124602893208382910464⟩,
    ⟨-60375624765413699347,13240736767654757430784⟩⟩

def packet0871 : StripRowPacket :=
  ⟨⟨⟨5,18,4,6⟩,
    ![383,1256,2519,4007,5516,6831,7768],![412,1324,2610,4097,5585,6871,7783]⟩,
    ⟨-6225591505699956047477,1275263013499568033008640⟩,
    ⟨-145578324490079190499,67679336077733067550720⟩⟩

def packet0872 : StripRowPacket :=
  ⟨⟨⟨5,18,4,7⟩,
    ![404,1309,2590,4076,5568,6860,7777],![428,1368,2678,4171,5645,6907,7795]⟩,
    ⟨-6575297361106017194353,2550526026999136066017280⟩,
    ⟨9083485072642857533,59219419068016434106880⟩⟩

def packet0873 : StripRowPacket :=
  ⟨⟨⟨5,19,4,6⟩,
    ![382,1253,2514,4002,5511,6828,7767],![410,1319,2604,4091,5580,6868,7782]⟩,
    ⟨-2171923217337858493,436110126229340186624⟩,
    ⟨-58322354430100554887,26481473535309514861568⟩⟩

def packet0874 : StripRowPacket :=
  ⟨⟨⟨5,19,4,7⟩,
    ![403,1305,2584,4071,5563,6857,7776],![427,1364,2671,4164,5640,6904,7794]⟩,
    ⟨-2288135961818703289,872220252458680373248⟩,
    ⟨513317583828286115,3310184191913689357696⟩⟩

def packet0875 : StripRowPacket :=
  ⟨⟨⟨4,10,3,0⟩,
    ![0,825,2112,3684,5298,6717,7732],![227,998,2248,3782,5364,6753,7745]⟩,
    ⟨-204978318971,10280321033840⟩,
    ⟨-55730380432459131,3910918511586944000⟩⟩

def packet0876 : StripRowPacket :=
  ⟨⟨⟨5,20,4,2⟩,
    ![192,968,2228,3770,5354,6746,7741],![281,1065,2309,3830,5395,6769,7750]⟩,
    ⟨-291354037554512249179,19800707526449417165312⟩,
    ⟨-112977513146929583995,9500246795864876699648⟩⟩

def packet0877 : StripRowPacket :=
  ⟨⟨⟨5,20,4,3⟩,
    ![262,1044,2293,3818,5385,6762,7746],![327,1137,2379,3885,5431,6787,7756]⟩,
    ⟨-3407689965829278543,276932972397893946368⟩,
    ⟨-22520969266033196201,2375061698966219174912⟩⟩

def packet0878 : StripRowPacket :=
  ⟨⟨⟨5,21,4,2⟩,
    ![192,966,2223,3764,5349,6743,7740],![280,1062,2304,3824,5390,6766,7749]⟩,
    ⟨-97536091823106411953129,6494987830105289183651840⟩,
    ⟨-363696168519169104693,29937799058619282688000⟩⟩

def packet0879 : StripRowPacket :=
  ⟨⟨⟨5,21,4,3⟩,
    ![262,1041,2288,3812,5380,6759,7745],![326,1134,2374,3879,5426,6784,7755]⟩,
    ⟨-163105346254394332428091,12989975660210578367303680⟩,
    ⟨-942518266052833249003,97297846940512668736000⟩⟩

def packet0880 : StripRowPacket :=
  ⟨⟨⟨4,11,3,0⟩,
    ![0,821,2103,3673,5289,6711,7730],![225,992,2238,3770,5354,6747,7743]⟩,
    ⟨-16150617,778831196⟩,
    ⟨-3966985270405661,266899563829832960⟩⟩

def packet0881 : StripRowPacket :=
  ⟨⟨⟨5,22,4,2⟩,
    ![192,963,2219,3758,5344,6740,7739],![279,1059,2299,3818,5385,6763,7748]⟩,
    ⟨-744359908633055195679,48598974802484269696000⟩,
    ⟨-458867692902078373967311,37001144292973039515381760⟩⟩

def packet0882 : StripRowPacket :=
  ⟨⟨⟨5,22,4,3⟩,
    ![262,1039,2283,3807,5375,6756,7744],![325,1131,2369,3874,5422,6782,7754]⟩,
    ⟨-13690228769815409992607,1069177445654653933312000⟩,
    ⟨-18295142706860350303745,1850057214648651975769088⟩⟩

def packet0883 : StripRowPacket :=
  ⟨⟨⟨5,23,4,2⟩,
    ![192,961,2214,3753,5340,6737,7738],![278,1056,2295,3813,5380,6760,7747]⟩,
    ⟨-437640604460233822169,28031853643679972669440⟩,
    ⟨-2652282835376468549,209642866703979554560⟩⟩

def packet0884 : StripRowPacket :=
  ⟨⟨⟨5,23,4,3⟩,
    ![261,1037,2279,3801,5371,6753,7743],![324,1128,2364,3868,5417,6779,7753]⟩,
    ⟨-731625462741031263627,56063707287359945338880⟩,
    ⟨-528745907209552429,52410716675994888640⟩⟩

def packet0885 : StripRowPacket :=
  ⟨⟨⟨5,20,4,4⟩,
    ![314,1119,2363,3871,5420,6780,7751],![362,1203,2452,3947,5473,6809,7763]⟩,
    ⟨-97972813779537291235,9900353763224708582656⟩,
    ⟨-67190240981335985613,9500246795864876699648⟩⟩

def packet0886 : StripRowPacket :=
  ⟨⟨⟨5,20,4,5⟩,
    ![352,1188,2436,3931,5460,6801,7758],![388,1263,2526,4014,5521,6835,7771]⟩,
    ⟨-296482845122711498231,39601415052898834330624⟩,
    ⟨-22148302449269593211,4750123397932438349824⟩⟩

def packet0887 : StripRowPacket :=
  ⟨⟨⟨5,21,4,4⟩,
    ![314,1116,2358,3866,5415,6777,7750],![361,1200,2447,3941,5468,6806,7762]⟩,
    ⟨-32784627215643960237481,3247493915052644591825920⟩,
    ⟨-562419187534693526203,77838277552410134988800⟩⟩

def packets036 : List StripRowPacket :=
  [packet0864, packet0865, packet0866, packet0867, packet0868, packet0869,
   packet0870, packet0871, packet0872, packet0873, packet0874, packet0875,
   packet0876, packet0877, packet0878, packet0879, packet0880, packet0881,
   packet0882, packet0883, packet0884, packet0885, packet0886, packet0887]

theorem packet0864_membership : packet0864 ∈ packets036 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0864_shape : checkStripShape packet0864.row = true := by
  decide +kernel

private theorem packet0864_cache : checkStripCache packet0864 = true := by
  decide +kernel

private theorem packet0864_pair (i : Fin 7) : checkEdgePair packet0864 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0864_ok : checkStripPacket packet0864 = true :=
  checkStripPacket_intro packet0864_shape packet0864_cache packet0864_pair

theorem packet0865_membership : packet0865 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0865_shape : checkStripShape packet0865.row = true := by
  decide +kernel

private theorem packet0865_cache : checkStripCache packet0865 = true := by
  decide +kernel

private theorem packet0865_pair (i : Fin 7) : checkEdgePair packet0865 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0865_ok : checkStripPacket packet0865 = true :=
  checkStripPacket_intro packet0865_shape packet0865_cache packet0865_pair

theorem packet0866_membership : packet0866 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0866_shape : checkStripShape packet0866.row = true := by
  decide +kernel

private theorem packet0866_cache : checkStripCache packet0866 = true := by
  decide +kernel

private theorem packet0866_pair (i : Fin 7) : checkEdgePair packet0866 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0866_ok : checkStripPacket packet0866 = true :=
  checkStripPacket_intro packet0866_shape packet0866_cache packet0866_pair

theorem packet0867_membership : packet0867 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0867_shape : checkStripShape packet0867.row = true := by
  decide +kernel

private theorem packet0867_cache : checkStripCache packet0867 = true := by
  decide +kernel

private theorem packet0867_pair (i : Fin 7) : checkEdgePair packet0867 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0867_ok : checkStripPacket packet0867 = true :=
  checkStripPacket_intro packet0867_shape packet0867_cache packet0867_pair

theorem packet0868_membership : packet0868 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0868_shape : checkStripShape packet0868.row = true := by
  decide +kernel

private theorem packet0868_cache : checkStripCache packet0868 = true := by
  decide +kernel

private theorem packet0868_pair (i : Fin 7) : checkEdgePair packet0868 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0868_ok : checkStripPacket packet0868 = true :=
  checkStripPacket_intro packet0868_shape packet0868_cache packet0868_pair

theorem packet0869_membership : packet0869 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0869_shape : checkStripShape packet0869.row = true := by
  decide +kernel

private theorem packet0869_cache : checkStripCache packet0869 = true := by
  decide +kernel

private theorem packet0869_pair (i : Fin 7) : checkEdgePair packet0869 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0869_ok : checkStripPacket packet0869 = true :=
  checkStripPacket_intro packet0869_shape packet0869_cache packet0869_pair

theorem packet0870_membership : packet0870 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0870_shape : checkStripShape packet0870.row = true := by
  decide +kernel

private theorem packet0870_cache : checkStripCache packet0870 = true := by
  decide +kernel

private theorem packet0870_pair (i : Fin 7) : checkEdgePair packet0870 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0870_ok : checkStripPacket packet0870 = true :=
  checkStripPacket_intro packet0870_shape packet0870_cache packet0870_pair

theorem packet0871_membership : packet0871 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0871_shape : checkStripShape packet0871.row = true := by
  decide +kernel

private theorem packet0871_cache : checkStripCache packet0871 = true := by
  decide +kernel

private theorem packet0871_pair (i : Fin 7) : checkEdgePair packet0871 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0871_ok : checkStripPacket packet0871 = true :=
  checkStripPacket_intro packet0871_shape packet0871_cache packet0871_pair

theorem packet0872_membership : packet0872 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0872_shape : checkStripShape packet0872.row = true := by
  decide +kernel

private theorem packet0872_cache : checkStripCache packet0872 = true := by
  decide +kernel

private theorem packet0872_pair (i : Fin 7) : checkEdgePair packet0872 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0872_ok : checkStripPacket packet0872 = true :=
  checkStripPacket_intro packet0872_shape packet0872_cache packet0872_pair

theorem packet0873_membership : packet0873 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0873_shape : checkStripShape packet0873.row = true := by
  decide +kernel

private theorem packet0873_cache : checkStripCache packet0873 = true := by
  decide +kernel

private theorem packet0873_pair (i : Fin 7) : checkEdgePair packet0873 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0873_ok : checkStripPacket packet0873 = true :=
  checkStripPacket_intro packet0873_shape packet0873_cache packet0873_pair

theorem packet0874_membership : packet0874 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0874_shape : checkStripShape packet0874.row = true := by
  decide +kernel

private theorem packet0874_cache : checkStripCache packet0874 = true := by
  decide +kernel

private theorem packet0874_pair (i : Fin 7) : checkEdgePair packet0874 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0874_ok : checkStripPacket packet0874 = true :=
  checkStripPacket_intro packet0874_shape packet0874_cache packet0874_pair

theorem packet0875_membership : packet0875 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0875_shape : checkStripShape packet0875.row = true := by
  decide +kernel

private theorem packet0875_cache : checkStripCache packet0875 = true := by
  decide +kernel

private theorem packet0875_pair (i : Fin 7) : checkEdgePair packet0875 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0875_ok : checkStripPacket packet0875 = true :=
  checkStripPacket_intro packet0875_shape packet0875_cache packet0875_pair

theorem packet0876_membership : packet0876 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0876_shape : checkStripShape packet0876.row = true := by
  decide +kernel

private theorem packet0876_cache : checkStripCache packet0876 = true := by
  decide +kernel

private theorem packet0876_pair (i : Fin 7) : checkEdgePair packet0876 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0876_ok : checkStripPacket packet0876 = true :=
  checkStripPacket_intro packet0876_shape packet0876_cache packet0876_pair

theorem packet0877_membership : packet0877 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0877_shape : checkStripShape packet0877.row = true := by
  decide +kernel

private theorem packet0877_cache : checkStripCache packet0877 = true := by
  decide +kernel

private theorem packet0877_pair (i : Fin 7) : checkEdgePair packet0877 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0877_ok : checkStripPacket packet0877 = true :=
  checkStripPacket_intro packet0877_shape packet0877_cache packet0877_pair

theorem packet0878_membership : packet0878 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0878_shape : checkStripShape packet0878.row = true := by
  decide +kernel

private theorem packet0878_cache : checkStripCache packet0878 = true := by
  decide +kernel

private theorem packet0878_pair (i : Fin 7) : checkEdgePair packet0878 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0878_ok : checkStripPacket packet0878 = true :=
  checkStripPacket_intro packet0878_shape packet0878_cache packet0878_pair

theorem packet0879_membership : packet0879 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0879_shape : checkStripShape packet0879.row = true := by
  decide +kernel

private theorem packet0879_cache : checkStripCache packet0879 = true := by
  decide +kernel

private theorem packet0879_pair (i : Fin 7) : checkEdgePair packet0879 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0879_ok : checkStripPacket packet0879 = true :=
  checkStripPacket_intro packet0879_shape packet0879_cache packet0879_pair

theorem packet0880_membership : packet0880 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0880_shape : checkStripShape packet0880.row = true := by
  decide +kernel

private theorem packet0880_cache : checkStripCache packet0880 = true := by
  decide +kernel

private theorem packet0880_pair (i : Fin 7) : checkEdgePair packet0880 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0880_ok : checkStripPacket packet0880 = true :=
  checkStripPacket_intro packet0880_shape packet0880_cache packet0880_pair

theorem packet0881_membership : packet0881 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0881_shape : checkStripShape packet0881.row = true := by
  decide +kernel

private theorem packet0881_cache : checkStripCache packet0881 = true := by
  decide +kernel

private theorem packet0881_pair (i : Fin 7) : checkEdgePair packet0881 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0881_ok : checkStripPacket packet0881 = true :=
  checkStripPacket_intro packet0881_shape packet0881_cache packet0881_pair

theorem packet0882_membership : packet0882 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0882_shape : checkStripShape packet0882.row = true := by
  decide +kernel

private theorem packet0882_cache : checkStripCache packet0882 = true := by
  decide +kernel

private theorem packet0882_pair (i : Fin 7) : checkEdgePair packet0882 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0882_ok : checkStripPacket packet0882 = true :=
  checkStripPacket_intro packet0882_shape packet0882_cache packet0882_pair

theorem packet0883_membership : packet0883 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0883_shape : checkStripShape packet0883.row = true := by
  decide +kernel

private theorem packet0883_cache : checkStripCache packet0883 = true := by
  decide +kernel

private theorem packet0883_pair (i : Fin 7) : checkEdgePair packet0883 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0883_ok : checkStripPacket packet0883 = true :=
  checkStripPacket_intro packet0883_shape packet0883_cache packet0883_pair

theorem packet0884_membership : packet0884 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0884_shape : checkStripShape packet0884.row = true := by
  decide +kernel

private theorem packet0884_cache : checkStripCache packet0884 = true := by
  decide +kernel

private theorem packet0884_pair (i : Fin 7) : checkEdgePair packet0884 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0884_ok : checkStripPacket packet0884 = true :=
  checkStripPacket_intro packet0884_shape packet0884_cache packet0884_pair

theorem packet0885_membership : packet0885 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0885_shape : checkStripShape packet0885.row = true := by
  decide +kernel

private theorem packet0885_cache : checkStripCache packet0885 = true := by
  decide +kernel

private theorem packet0885_pair (i : Fin 7) : checkEdgePair packet0885 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0885_ok : checkStripPacket packet0885 = true :=
  checkStripPacket_intro packet0885_shape packet0885_cache packet0885_pair

theorem packet0886_membership : packet0886 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0886_shape : checkStripShape packet0886.row = true := by
  decide +kernel

private theorem packet0886_cache : checkStripCache packet0886 = true := by
  decide +kernel

private theorem packet0886_pair (i : Fin 7) : checkEdgePair packet0886 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0886_ok : checkStripPacket packet0886 = true :=
  checkStripPacket_intro packet0886_shape packet0886_cache packet0886_pair

theorem packet0887_membership : packet0887 ∈ packets036 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0887_shape : checkStripShape packet0887.row = true := by
  decide +kernel

private theorem packet0887_cache : checkStripCache packet0887 = true := by
  decide +kernel

private theorem packet0887_pair (i : Fin 7) : checkEdgePair packet0887 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0887_ok : checkStripPacket packet0887 = true :=
  checkStripPacket_intro packet0887_shape packet0887_cache packet0887_pair

theorem packets036_checked : packets036.all checkStripPacket = true := by
  simp only [packets036, List.all_cons, List.all_nil, Bool.true_and, packet0864_ok,
    packet0865_ok, packet0866_ok, packet0867_ok, packet0868_ok, packet0869_ok,
    packet0870_ok, packet0871_ok, packet0872_ok, packet0873_ok, packet0874_ok,
    packet0875_ok, packet0876_ok, packet0877_ok, packet0878_ok, packet0879_ok,
    packet0880_ok, packet0881_ok, packet0882_ok, packet0883_ok, packet0884_ok,
    packet0885_ok, packet0886_ok, packet0887_ok]

theorem packets036_valid : packets036.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
