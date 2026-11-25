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

def packet0048 : StripRowPacket :=
  ⟨⟨⟨8,4,6,6⟩,
    ![197,1162,2480,4002,5523,6838,7771],![253,1191,2503,4019,5535,6846,7775]⟩,
    ⟨-579652001766363254174192384063,82700145815656397374717167779840⟩,
    ⟨-2229591234558958013358092779,336500288850320199280637378560⟩⟩

def packet0049 : StripRowPacket :=
  ⟨⟨⟨8,4,6,7⟩,
    ![228,1179,2493,4011,5529,6841,7772],![280,1208,2517,4029,5541,6849,7776]⟩,
    ⟨-101573176676734436801027543897,15036390148301163159039485050880⟩,
    ⟨-1875976608375278860254806763,294437752744030174370557706240⟩⟩

def packet0050 : StripRowPacket :=
  ⟨⟨⟨8,5,6,6⟩,
    ![195,1156,2474,3997,5520,6837,7770],![250,1184,2498,4015,5532,6845,7775]⟩,
    ⟨-110289286736599693407061399611,15522011881243801082287035842560⟩,
    ⟨-9752205625363389782048603532199,1450958070828439567023527350435840⟩⟩

def packet0051 : StripRowPacket :=
  ⟨⟨⟨8,5,6,7⟩,
    ![225,1173,2487,4007,5526,6840,7771],![276,1202,2511,4025,5539,6848,7776]⟩,
    ⟨-2763271718814552933403627562579,403572308912338828139462931906560⟩,
    ⟨-1172092259277239943026931586817,181369758853554945877940918804480⟩⟩

def packet0052 : StripRowPacket :=
  ⟨⟨⟨8,6,6,4⟩,
    ![129,1117,2444,3975,5506,6830,7768],![190,1144,2466,3992,5518,6837,7772]⟩,
    ⟨-791819661432524672805144893,102504188715533488547729162240⟩,
    ⟨-408607670021826975663791091387869,55665380832590495470668946370068480⟩⟩

def packet0053 : StripRowPacket :=
  ⟨⟨⟨8,6,6,5⟩,
    ![162,1133,2456,3984,5512,6833,7769],![219,1161,2479,4001,5524,6840,7773]⟩,
    ⟨-611924998863451738111228797,82003350972426790838183329792⟩,
    ⟨-17907710395566983099954156631969,2530244583299567975939497562275840⟩⟩

def packet0054 : StripRowPacket :=
  ⟨⟨⟨8,7,5,2⟩,
    ![128,1111,2439,3971,5504,6829,7768],![216,1155,2473,3997,5521,6839,7773]⟩,
    ⟨-29192469759313961123650520593,3730483481013522515366648971264⟩,
    ⟨-25192134956450803258498375,3512166976006048866496060928⟩⟩

def packet0055 : StripRowPacket :=
  ⟨⟨⟨8,6,6,6⟩,
    ![194,1150,2469,3993,5517,6836,7770],![246,1178,2492,4011,5530,6843,7774]⟩,
    ⟨-1475985671452209344945854199,205008377431066977095458324480⟩,
    ⟨-379331587383120280734191800418767,55665380832590495470668946370068480⟩⟩

def packet0056 : StripRowPacket :=
  ⟨⟨⟨8,6,6,7⟩,
    ![223,1167,2482,4003,5523,6839,7771],![273,1196,2506,4021,5536,6847,7775]⟩,
    ⟨-2844317691491578689227272811,410016754862133954190916648960⟩,
    ⟨-6512384751138695236953431338111,994024657724830276261945470894080⟩⟩

def packet0057 : StripRowPacket :=
  ⟨⟨⟨8,7,6,6⟩,
    ![192,1144,2464,3989,5515,6834,7769],![244,1172,2487,4007,5527,6842,7774]⟩,
    ⟨-1876061559276025515617867407,257274722828518794163217170432⟩,
    ⟨-48508570598630177223178273,7024333952012097732992121856⟩⟩

def packet0058 : StripRowPacket :=
  ⟨⟨⟨8,7,6,7⟩,
    ![221,1161,2477,3999,5521,6837,7770],![269,1190,2501,4017,5533,6845,7775]⟩,
    ⟨-104832416138386297611453423223,14921933924054090061466595885056⟩,
    ⟨-11658217821089686982339949,1756083488003024433248030464⟩⟩

def packet0059 : StripRowPacket :=
  ⟨⟨⟨8,0,6,8⟩,
    ![271,1223,2530,4038,5546,6850,7774],![326,1255,2556,4058,5560,6859,7779]⟩,
    ⟨-2134517217227496327,348033488351769425920⟩,
    ⟨-8310628760530192047,1445432673935107686400⟩⟩

def packet0060 : StripRowPacket :=
  ⟨⟨⟨8,0,6,9⟩,
    ![301,1240,2543,4048,5552,6853,7775],![351,1274,2570,4068,5566,6862,7780]⟩,
    ⟨-298609470986150017,50623052851166461952⟩,
    ⟨-797054185655103223,144543267393510768640⟩⟩

def packet0061 : StripRowPacket :=
  ⟨⟨⟨8,1,6,8⟩,
    ![267,1216,2523,4033,5543,6849,7774],![320,1247,2549,4053,5557,6857,7778]⟩,
    ⟨-2002289036228200845130231250581,321498594114599286030733418905600⟩,
    ⟨-1556566643421659455652366079565,266320381049706856435440599760896⟩⟩

def packet0062 : StripRowPacket :=
  ⟨⟨⟨8,1,6,9⟩,
    ![296,1233,2537,4043,5549,6852,7775],![345,1266,2564,4064,5563,6860,7780]⟩,
    ⟨-169421985357680030175802010604319,28291876282084737170704540863692800⟩,
    ⟨-41045003297145542180924823659071,7323810478866938551974616493424640⟩⟩

def packet0063 : StripRowPacket :=
  ⟨⟨⟨8,0,6,10⟩,
    ![329,1258,2557,4058,5559,6856,7776],![375,1292,2585,4079,5573,6865,7781]⟩,
    ⟨-7885452035328265627,1392133953407077703680⟩,
    ⟨-7630454952571872413,1445432673935107686400⟩⟩

def packet0064 : StripRowPacket :=
  ⟨⟨⟨8,0,6,11⟩,
    ![355,1276,2571,4068,5565,6860,7777],![398,1312,2600,4090,5580,6869,7782]⟩,
    ⟨-15118287237074811573,2784267906814155407360⟩,
    ⟨-1822592012148178149,361358168483776921600⟩⟩

def packet0065 : StripRowPacket :=
  ⟨⟨⟨8,1,6,10⟩,
    ![323,1251,2551,4053,5556,6855,7776],![368,1285,2579,4074,5570,6864,7781]⟩,
    ⟨-16264253552727838598014367115751,2829187628208473717070454086369280⟩,
    ⟨-78568847800390898662819160260209,14647620957733877103949232986849280⟩⟩

def packet0066 : StripRowPacket :=
  ⟨⟨⟨8,1,6,11⟩,
    ![349,1270,2566,4064,5562,6858,7777],![390,1304,2594,4086,5577,6867,7782]⟩,
    ⟨-155863085696876741784485331710701,28291876282084737170704540863692800⟩,
    ⟨-18761922251622678240947168300569,3661905239433469275987308246712320⟩⟩

def packet0067 : StripRowPacket :=
  ⟨⟨⟨8,2,6,8⟩,
    ![263,1209,2518,4029,5540,6847,7773],![314,1240,2543,4048,5554,6855,7778]⟩,
    ⟨-68685006429460302102670758665,10866260590562309031878634938368⟩,
    ⟨-18128449928335861436617945213439,3053170870647725012626542885994496⟩⟩

def packet0068 : StripRowPacket :=
  ⟨⟨⟨8,2,6,9⟩,
    ![291,1227,2531,4039,5546,6850,7774],![339,1259,2557,4059,5560,6859,7779]⟩,
    ⟨-528216731997575290321653296433,86930084724498472255029079506944⟩,
    ⟨-8689803041868887836307083203811,1526585435323862506313271442997248⟩⟩

def packet0069 : StripRowPacket :=
  ⟨⟨⟨8,3,6,8⟩,
    ![260,1202,2512,4025,5537,6846,7773],![309,1233,2537,4044,5551,6854,7778]⟩,
    ⟨-2490203541160939488894104487,388366019697928996669839196160⟩,
    ⟨-4826776947429312376530200739,800687746179523786275634708480⟩⟩

def packet0070 : StripRowPacket :=
  ⟨⟨⟨8,3,6,9⟩,
    ![288,1220,2526,4035,5544,6849,7774],![333,1252,2552,4054,5557,6857,7779]⟩,
    ⟨-294567476441337849146617375,47798894732052799590134054912⟩,
    ⟨-462665181877356798864081163,80068774617952378627563470848⟩⟩

def packet0071 : StripRowPacket :=
  ⟨⟨⟨8,2,6,10⟩,
    ![318,1245,2545,4049,5553,6854,7775],![361,1277,2572,4070,5567,6862,7780]⟩,
    ⟨-253476706279734081910970261773,43465042362249236127514539753472⟩,
    ⟨-16630762239139689908610387601805,3053170870647725012626542885994496⟩⟩

def packets002 : List StripRowPacket :=
  [packet0048, packet0049, packet0050, packet0051, packet0052, packet0053,
   packet0054, packet0055, packet0056, packet0057, packet0058, packet0059,
   packet0060, packet0061, packet0062, packet0063, packet0064, packet0065,
   packet0066, packet0067, packet0068, packet0069, packet0070, packet0071]

theorem packet0048_membership : packet0048 ∈ packets002 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0048_shape : checkStripShape packet0048.row = true := by
  decide +kernel

private theorem packet0048_cache : checkStripCache packet0048 = true := by
  decide +kernel

private theorem packet0048_pair (i : Fin 7) : checkEdgePair packet0048 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0048_ok : checkStripPacket packet0048 = true :=
  checkStripPacket_intro packet0048_shape packet0048_cache packet0048_pair

theorem packet0049_membership : packet0049 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0049_shape : checkStripShape packet0049.row = true := by
  decide +kernel

private theorem packet0049_cache : checkStripCache packet0049 = true := by
  decide +kernel

private theorem packet0049_pair (i : Fin 7) : checkEdgePair packet0049 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0049_ok : checkStripPacket packet0049 = true :=
  checkStripPacket_intro packet0049_shape packet0049_cache packet0049_pair

theorem packet0050_membership : packet0050 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0050_shape : checkStripShape packet0050.row = true := by
  decide +kernel

private theorem packet0050_cache : checkStripCache packet0050 = true := by
  decide +kernel

private theorem packet0050_pair (i : Fin 7) : checkEdgePair packet0050 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0050_ok : checkStripPacket packet0050 = true :=
  checkStripPacket_intro packet0050_shape packet0050_cache packet0050_pair

theorem packet0051_membership : packet0051 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0051_shape : checkStripShape packet0051.row = true := by
  decide +kernel

private theorem packet0051_cache : checkStripCache packet0051 = true := by
  decide +kernel

private theorem packet0051_pair (i : Fin 7) : checkEdgePair packet0051 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0051_ok : checkStripPacket packet0051 = true :=
  checkStripPacket_intro packet0051_shape packet0051_cache packet0051_pair

theorem packet0052_membership : packet0052 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0052_shape : checkStripShape packet0052.row = true := by
  decide +kernel

private theorem packet0052_cache : checkStripCache packet0052 = true := by
  decide +kernel

private theorem packet0052_pair (i : Fin 7) : checkEdgePair packet0052 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0052_ok : checkStripPacket packet0052 = true :=
  checkStripPacket_intro packet0052_shape packet0052_cache packet0052_pair

theorem packet0053_membership : packet0053 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0053_shape : checkStripShape packet0053.row = true := by
  decide +kernel

private theorem packet0053_cache : checkStripCache packet0053 = true := by
  decide +kernel

private theorem packet0053_pair (i : Fin 7) : checkEdgePair packet0053 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0053_ok : checkStripPacket packet0053 = true :=
  checkStripPacket_intro packet0053_shape packet0053_cache packet0053_pair

theorem packet0054_membership : packet0054 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0054_shape : checkStripShape packet0054.row = true := by
  decide +kernel

private theorem packet0054_cache : checkStripCache packet0054 = true := by
  decide +kernel

private theorem packet0054_pair (i : Fin 7) : checkEdgePair packet0054 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0054_ok : checkStripPacket packet0054 = true :=
  checkStripPacket_intro packet0054_shape packet0054_cache packet0054_pair

theorem packet0055_membership : packet0055 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0055_shape : checkStripShape packet0055.row = true := by
  decide +kernel

private theorem packet0055_cache : checkStripCache packet0055 = true := by
  decide +kernel

private theorem packet0055_pair (i : Fin 7) : checkEdgePair packet0055 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0055_ok : checkStripPacket packet0055 = true :=
  checkStripPacket_intro packet0055_shape packet0055_cache packet0055_pair

theorem packet0056_membership : packet0056 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0056_shape : checkStripShape packet0056.row = true := by
  decide +kernel

private theorem packet0056_cache : checkStripCache packet0056 = true := by
  decide +kernel

private theorem packet0056_pair (i : Fin 7) : checkEdgePair packet0056 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0056_ok : checkStripPacket packet0056 = true :=
  checkStripPacket_intro packet0056_shape packet0056_cache packet0056_pair

theorem packet0057_membership : packet0057 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0057_shape : checkStripShape packet0057.row = true := by
  decide +kernel

private theorem packet0057_cache : checkStripCache packet0057 = true := by
  decide +kernel

private theorem packet0057_pair (i : Fin 7) : checkEdgePair packet0057 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0057_ok : checkStripPacket packet0057 = true :=
  checkStripPacket_intro packet0057_shape packet0057_cache packet0057_pair

theorem packet0058_membership : packet0058 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0058_shape : checkStripShape packet0058.row = true := by
  decide +kernel

private theorem packet0058_cache : checkStripCache packet0058 = true := by
  decide +kernel

private theorem packet0058_pair (i : Fin 7) : checkEdgePair packet0058 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0058_ok : checkStripPacket packet0058 = true :=
  checkStripPacket_intro packet0058_shape packet0058_cache packet0058_pair

theorem packet0059_membership : packet0059 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0059_shape : checkStripShape packet0059.row = true := by
  decide +kernel

private theorem packet0059_cache : checkStripCache packet0059 = true := by
  decide +kernel

private theorem packet0059_pair (i : Fin 7) : checkEdgePair packet0059 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0059_ok : checkStripPacket packet0059 = true :=
  checkStripPacket_intro packet0059_shape packet0059_cache packet0059_pair

theorem packet0060_membership : packet0060 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0060_shape : checkStripShape packet0060.row = true := by
  decide +kernel

private theorem packet0060_cache : checkStripCache packet0060 = true := by
  decide +kernel

private theorem packet0060_pair (i : Fin 7) : checkEdgePair packet0060 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0060_ok : checkStripPacket packet0060 = true :=
  checkStripPacket_intro packet0060_shape packet0060_cache packet0060_pair

theorem packet0061_membership : packet0061 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0061_shape : checkStripShape packet0061.row = true := by
  decide +kernel

private theorem packet0061_cache : checkStripCache packet0061 = true := by
  decide +kernel

private theorem packet0061_pair (i : Fin 7) : checkEdgePair packet0061 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0061_ok : checkStripPacket packet0061 = true :=
  checkStripPacket_intro packet0061_shape packet0061_cache packet0061_pair

theorem packet0062_membership : packet0062 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0062_shape : checkStripShape packet0062.row = true := by
  decide +kernel

private theorem packet0062_cache : checkStripCache packet0062 = true := by
  decide +kernel

private theorem packet0062_pair (i : Fin 7) : checkEdgePair packet0062 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0062_ok : checkStripPacket packet0062 = true :=
  checkStripPacket_intro packet0062_shape packet0062_cache packet0062_pair

theorem packet0063_membership : packet0063 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0063_shape : checkStripShape packet0063.row = true := by
  decide +kernel

private theorem packet0063_cache : checkStripCache packet0063 = true := by
  decide +kernel

private theorem packet0063_pair (i : Fin 7) : checkEdgePair packet0063 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0063_ok : checkStripPacket packet0063 = true :=
  checkStripPacket_intro packet0063_shape packet0063_cache packet0063_pair

theorem packet0064_membership : packet0064 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0064_shape : checkStripShape packet0064.row = true := by
  decide +kernel

private theorem packet0064_cache : checkStripCache packet0064 = true := by
  decide +kernel

private theorem packet0064_pair (i : Fin 7) : checkEdgePair packet0064 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0064_ok : checkStripPacket packet0064 = true :=
  checkStripPacket_intro packet0064_shape packet0064_cache packet0064_pair

theorem packet0065_membership : packet0065 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0065_shape : checkStripShape packet0065.row = true := by
  decide +kernel

private theorem packet0065_cache : checkStripCache packet0065 = true := by
  decide +kernel

private theorem packet0065_pair (i : Fin 7) : checkEdgePair packet0065 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0065_ok : checkStripPacket packet0065 = true :=
  checkStripPacket_intro packet0065_shape packet0065_cache packet0065_pair

theorem packet0066_membership : packet0066 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0066_shape : checkStripShape packet0066.row = true := by
  decide +kernel

private theorem packet0066_cache : checkStripCache packet0066 = true := by
  decide +kernel

private theorem packet0066_pair (i : Fin 7) : checkEdgePair packet0066 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0066_ok : checkStripPacket packet0066 = true :=
  checkStripPacket_intro packet0066_shape packet0066_cache packet0066_pair

theorem packet0067_membership : packet0067 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0067_shape : checkStripShape packet0067.row = true := by
  decide +kernel

private theorem packet0067_cache : checkStripCache packet0067 = true := by
  decide +kernel

private theorem packet0067_pair (i : Fin 7) : checkEdgePair packet0067 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0067_ok : checkStripPacket packet0067 = true :=
  checkStripPacket_intro packet0067_shape packet0067_cache packet0067_pair

theorem packet0068_membership : packet0068 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0068_shape : checkStripShape packet0068.row = true := by
  decide +kernel

private theorem packet0068_cache : checkStripCache packet0068 = true := by
  decide +kernel

private theorem packet0068_pair (i : Fin 7) : checkEdgePair packet0068 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0068_ok : checkStripPacket packet0068 = true :=
  checkStripPacket_intro packet0068_shape packet0068_cache packet0068_pair

theorem packet0069_membership : packet0069 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0069_shape : checkStripShape packet0069.row = true := by
  decide +kernel

private theorem packet0069_cache : checkStripCache packet0069 = true := by
  decide +kernel

private theorem packet0069_pair (i : Fin 7) : checkEdgePair packet0069 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0069_ok : checkStripPacket packet0069 = true :=
  checkStripPacket_intro packet0069_shape packet0069_cache packet0069_pair

theorem packet0070_membership : packet0070 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0070_shape : checkStripShape packet0070.row = true := by
  decide +kernel

private theorem packet0070_cache : checkStripCache packet0070 = true := by
  decide +kernel

private theorem packet0070_pair (i : Fin 7) : checkEdgePair packet0070 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0070_ok : checkStripPacket packet0070 = true :=
  checkStripPacket_intro packet0070_shape packet0070_cache packet0070_pair

theorem packet0071_membership : packet0071 ∈ packets002 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0071_shape : checkStripShape packet0071.row = true := by
  decide +kernel

private theorem packet0071_cache : checkStripCache packet0071 = true := by
  decide +kernel

private theorem packet0071_pair (i : Fin 7) : checkEdgePair packet0071 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0071_ok : checkStripPacket packet0071 = true :=
  checkStripPacket_intro packet0071_shape packet0071_cache packet0071_pair

theorem packets002_checked : packets002.all checkStripPacket = true := by
  simp only [packets002, List.all_cons, List.all_nil, Bool.true_and, packet0048_ok,
    packet0049_ok, packet0050_ok, packet0051_ok, packet0052_ok, packet0053_ok,
    packet0054_ok, packet0055_ok, packet0056_ok, packet0057_ok, packet0058_ok,
    packet0059_ok, packet0060_ok, packet0061_ok, packet0062_ok, packet0063_ok,
    packet0064_ok, packet0065_ok, packet0066_ok, packet0067_ok, packet0068_ok,
    packet0069_ok, packet0070_ok, packet0071_ok]

theorem packets002_valid : packets002.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
