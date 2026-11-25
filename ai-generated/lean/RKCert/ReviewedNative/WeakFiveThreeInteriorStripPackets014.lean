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

def packet0336 : StripRowPacket :=
  ⟨⟨⟨7,12,5,2⟩,
    ![113,1037,2366,3914,5466,6809,7762],![198,1086,2404,3943,5485,6820,7767]⟩,
    ⟨-74636233627866860940344287,7952347152620245134508503040⟩,
    ⟨-32815230519336726352722189,3835361726292351782848921600⟩⟩

def packet0337 : StripRowPacket :=
  ⟨⟨⟨7,12,5,3⟩,
    ![171,1071,2393,3933,5478,6815,7763],![245,1122,2432,3963,5498,6827,7769]⟩,
    ⟨-2525984088684953509742315,289176260095281641254854656⟩,
    ⟨-7579860154986577375387823,958840431573087945712230400⟩⟩

def packet0338 : StripRowPacket :=
  ⟨⟨⟨7,13,5,2⟩,
    ![113,1031,2360,3909,5463,6807,7761],![197,1080,2397,3937,5482,6819,7767]⟩,
    ⟨-10389929075057613778998396793,1089463580359376496294204620800⟩,
    ⟨-106711081787464362800981472671,12265897301900464322897675141120⟩⟩

def packet0339 : StripRowPacket :=
  ⟨⟨⟨7,13,5,3⟩,
    ![170,1065,2387,3928,5475,6813,7763],![243,1116,2426,3958,5495,6825,7769]⟩,
    ⟨-212717900934794841914986370969,23968198767906282918472501657600⟩,
    ⟨-24647476948566947218914738773,3066474325475116080724418785280⟩⟩

def packet0340 : StripRowPacket :=
  ⟨⟨⟨7,14,5,0⟩,
    ![0,964,2306,3870,5438,6795,7757],![84,1007,2339,3895,5455,6805,7762]⟩,
    ⟨-12364438773859119,1120904305666946944⟩,
    ⟨-17205060693319552910127401001,1688921652296687959866837794816⟩⟩

def packet0341 : StripRowPacket :=
  ⟨⟨⟨7,14,5,1⟩,
    ![50,994,2330,3887,5448,6800,7759],![143,1039,2364,3913,5466,6811,7764]⟩,
    ⟨-145453626220523852719351224565,14042763237008092242228624736256⟩,
    ⟨-8034044240582130356055458089,844460826148343979933418897408⟩⟩

def packet0342 : StripRowPacket :=
  ⟨⟨⟨7,15,4,0⟩,
    ![0,959,2301,3865,5434,6793,7757],![142,1034,2358,3908,5463,6809,7763]⟩,
    ⟨-49913341,4457318008⟩,
    ⟨-77084429508225157538431,7977556648541669420627968⟩⟩

def packet0343 : StripRowPacket :=
  ⟨⟨⟨7,14,5,2⟩,
    ![113,1026,2354,3904,5459,6806,7760],![195,1074,2391,3932,5478,6817,7766]⟩,
    ⟨-68002373075200936078621462837,7021381618504046121114312368128⟩,
    ⟨-1148547405308382193391879335,129917050176668304605141368832⟩⟩

def packet0344 : StripRowPacket :=
  ⟨⟨⟨7,14,5,3⟩,
    ![170,1060,2381,3923,5471,6812,7762],![241,1111,2420,3953,5491,6823,7768]⟩,
    ⟨-126555866080279891595134626783,14042763237008092242228624736256⟩,
    ⟨-3448536014213419079019486633,422230413074171989966709448704⟩⟩

def packet0345 : StripRowPacket :=
  ⟨⟨⟨7,15,5,2⟩,
    ![113,1021,2349,3900,5456,6804,7760],![194,1069,2385,3927,5475,6815,7765]⟩,
    ⟨-2779958951308765148077,282787410981209719619584⟩,
    ⟨-143254687531528404835725,15955113297083338841255936⟩⟩

def packet0346 : StripRowPacket :=
  ⟨⟨⟨7,15,5,3⟩,
    ![169,1055,2375,3919,5468,6810,7762],![240,1106,2414,3948,5488,6822,7767]⟩,
    ⟨-67251662098381148125019,7352472685511452710109184⟩,
    ⟨-33085129011651623648647,3988778324270834710313984⟩⟩

def packet0347 : StripRowPacket :=
  ⟨⟨⟨7,12,5,4⟩,
    ![222,1107,2421,3953,5491,6822,7765],![286,1160,2462,3985,5512,6834,7771]⟩,
    ⟨-32146445624902791047741519,3976173576310122567254251520⟩,
    ⟨-5564730144111178530076079,767072345258470356569784320⟩⟩

def packet0348 : StripRowPacket :=
  ⟨⟨⟨7,12,5,5⟩,
    ![267,1145,2450,3975,5504,6829,7768],![322,1198,2494,4008,5527,6842,7774]⟩,
    ⟨-118242440121549885346104827,15904694305240490269017006080⟩,
    ⟨-12663930410582737899604749,1917680863146175891424460800⟩⟩

def packet0349 : StripRowPacket :=
  ⟨⟨⟨7,13,5,4⟩,
    ![221,1102,2415,3948,5487,6820,7765],![284,1154,2456,3980,5509,6832,7771]⟩,
    ⟨-49214340554580545173002003123,5992049691976570729618125414400⟩,
    ⟨-90468733801071214950336437513,12265897301900464322897675141120⟩⟩

def packet0350 : StripRowPacket :=
  ⟨⟨⟨7,13,5,5⟩,
    ![265,1139,2445,3970,5501,6827,7767],![319,1192,2488,4003,5523,6840,7773]⟩,
    ⟨-36199364700369903893805930803,4793639753581256583694500331520⟩,
    ⟨-41173779903937320512506959967,6132948650950232161448837570560⟩⟩

def packet0351 : StripRowPacket :=
  ⟨⟨⟨7,12,5,6⟩,
    ![306,1183,2482,3998,5519,6836,7770],![353,1236,2528,4033,5543,6850,7776]⟩,
    ⟨-53949548871744303250621789,7952347152620245134508503040⟩,
    ⟨-3261724417396436992576943,547908818041764540406988800⟩⟩

def packet0352 : StripRowPacket :=
  ⟨⟨⟨7,12,5,7⟩,
    ![340,1222,2514,4022,5534,6844,7772],![380,1274,2562,4060,5560,6858,7779]⟩,
    ⟨-97555755365427327656382329,15904694305240490269017006080⟩,
    ⟨-2542035127798080262108463,479420215786543972856115200⟩⟩

def packet0353 : StripRowPacket :=
  ⟨⟨⟨7,13,5,6⟩,
    ![304,1178,2476,3993,5516,6834,7769],![350,1230,2522,4028,5539,6848,7776]⟩,
    ⟨-82568142392688429123025647769,11984099383953141459236250828800⟩,
    ⟨-14845277162935613419938280471,2453179460380092864579535028224⟩⟩

def packet0354 : StripRowPacket :=
  ⟨⟨⟨7,13,5,7⟩,
    ![337,1217,2509,4017,5531,6842,7772],![377,1269,2556,4055,5557,6857,7778]⟩,
    ⟨-21325106581272028146153276723,3424028395415183274067500236800⟩,
    ⟨-8263151477685186646796110597,1533237162737558040362209392640⟩⟩

def packet0355 : StripRowPacket :=
  ⟨⟨⟨7,14,5,4⟩,
    ![220,1096,2409,3944,5484,6818,7764],![282,1149,2450,3975,5505,6830,7770]⟩,
    ⟨-2252057423272267519865890921,270053139173232543119781244928⟩,
    ⟨-12657171844698384118061461709,1688921652296687959866837794816⟩⟩

def packet0356 : StripRowPacket :=
  ⟨⟨⟨7,14,5,5⟩,
    ![264,1134,2439,3965,5498,6825,7766],![317,1187,2482,3998,5520,6838,7773]⟩,
    ⟨-107658105940035930470918029001,14042763237008092242228624736256⟩,
    ⟨-5760099816271545960022488443,844460826148343979933418897408⟩⟩

def packet0357 : StripRowPacket :=
  ⟨⟨⟨7,15,5,4⟩,
    ![219,1092,2403,3939,5481,6817,7764],![280,1143,2444,3970,5502,6829,7770]⟩,
    ⟨-15556097865683600600009,1838118171377863177527296⟩,
    ⟨-9340488043206506488727,1227316407467949141635072⟩⟩

def packet0358 : StripRowPacket :=
  ⟨⟨⟨7,15,5,5⟩,
    ![262,1129,2433,3961,5495,6824,7766],![315,1182,2476,3994,5517,6836,7772]⟩,
    ⟨-57197120827087656675053,7352472685511452710109184⟩,
    ⟨-55256086538381337056157,7977556648541669420627968⟩⟩

def packet0359 : StripRowPacket :=
  ⟨⟨⟨7,14,5,6⟩,
    ![302,1173,2470,3988,5512,6833,7769],![348,1225,2516,4024,5536,6846,7775]⟩,
    ⟨-49104612934956974954404865055,7021381618504046121114312368128⟩,
    ⟨-10383227420387799722028492063,1688921652296687959866837794816⟩⟩

def packets014 : List StripRowPacket :=
  [packet0336, packet0337, packet0338, packet0339, packet0340, packet0341,
   packet0342, packet0343, packet0344, packet0345, packet0346, packet0347,
   packet0348, packet0349, packet0350, packet0351, packet0352, packet0353,
   packet0354, packet0355, packet0356, packet0357, packet0358, packet0359]

theorem packet0336_membership : packet0336 ∈ packets014 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0336_shape : checkStripShape packet0336.row = true := by
  decide +kernel

private theorem packet0336_cache : checkStripCache packet0336 = true := by
  decide +kernel

private theorem packet0336_pair (i : Fin 7) : checkEdgePair packet0336 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0336_ok : checkStripPacket packet0336 = true :=
  checkStripPacket_intro packet0336_shape packet0336_cache packet0336_pair

theorem packet0337_membership : packet0337 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0337_shape : checkStripShape packet0337.row = true := by
  decide +kernel

private theorem packet0337_cache : checkStripCache packet0337 = true := by
  decide +kernel

private theorem packet0337_pair (i : Fin 7) : checkEdgePair packet0337 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0337_ok : checkStripPacket packet0337 = true :=
  checkStripPacket_intro packet0337_shape packet0337_cache packet0337_pair

theorem packet0338_membership : packet0338 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0338_shape : checkStripShape packet0338.row = true := by
  decide +kernel

private theorem packet0338_cache : checkStripCache packet0338 = true := by
  decide +kernel

private theorem packet0338_pair (i : Fin 7) : checkEdgePair packet0338 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0338_ok : checkStripPacket packet0338 = true :=
  checkStripPacket_intro packet0338_shape packet0338_cache packet0338_pair

theorem packet0339_membership : packet0339 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0339_shape : checkStripShape packet0339.row = true := by
  decide +kernel

private theorem packet0339_cache : checkStripCache packet0339 = true := by
  decide +kernel

private theorem packet0339_pair (i : Fin 7) : checkEdgePair packet0339 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0339_ok : checkStripPacket packet0339 = true :=
  checkStripPacket_intro packet0339_shape packet0339_cache packet0339_pair

theorem packet0340_membership : packet0340 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0340_shape : checkStripShape packet0340.row = true := by
  decide +kernel

private theorem packet0340_cache : checkStripCache packet0340 = true := by
  decide +kernel

private theorem packet0340_pair (i : Fin 7) : checkEdgePair packet0340 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0340_ok : checkStripPacket packet0340 = true :=
  checkStripPacket_intro packet0340_shape packet0340_cache packet0340_pair

theorem packet0341_membership : packet0341 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0341_shape : checkStripShape packet0341.row = true := by
  decide +kernel

private theorem packet0341_cache : checkStripCache packet0341 = true := by
  decide +kernel

private theorem packet0341_pair (i : Fin 7) : checkEdgePair packet0341 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0341_ok : checkStripPacket packet0341 = true :=
  checkStripPacket_intro packet0341_shape packet0341_cache packet0341_pair

theorem packet0342_membership : packet0342 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0342_shape : checkStripShape packet0342.row = true := by
  decide +kernel

private theorem packet0342_cache : checkStripCache packet0342 = true := by
  decide +kernel

private theorem packet0342_pair (i : Fin 7) : checkEdgePair packet0342 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0342_ok : checkStripPacket packet0342 = true :=
  checkStripPacket_intro packet0342_shape packet0342_cache packet0342_pair

theorem packet0343_membership : packet0343 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0343_shape : checkStripShape packet0343.row = true := by
  decide +kernel

private theorem packet0343_cache : checkStripCache packet0343 = true := by
  decide +kernel

private theorem packet0343_pair (i : Fin 7) : checkEdgePair packet0343 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0343_ok : checkStripPacket packet0343 = true :=
  checkStripPacket_intro packet0343_shape packet0343_cache packet0343_pair

theorem packet0344_membership : packet0344 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0344_shape : checkStripShape packet0344.row = true := by
  decide +kernel

private theorem packet0344_cache : checkStripCache packet0344 = true := by
  decide +kernel

private theorem packet0344_pair (i : Fin 7) : checkEdgePair packet0344 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0344_ok : checkStripPacket packet0344 = true :=
  checkStripPacket_intro packet0344_shape packet0344_cache packet0344_pair

theorem packet0345_membership : packet0345 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0345_shape : checkStripShape packet0345.row = true := by
  decide +kernel

private theorem packet0345_cache : checkStripCache packet0345 = true := by
  decide +kernel

private theorem packet0345_pair (i : Fin 7) : checkEdgePair packet0345 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0345_ok : checkStripPacket packet0345 = true :=
  checkStripPacket_intro packet0345_shape packet0345_cache packet0345_pair

theorem packet0346_membership : packet0346 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0346_shape : checkStripShape packet0346.row = true := by
  decide +kernel

private theorem packet0346_cache : checkStripCache packet0346 = true := by
  decide +kernel

private theorem packet0346_pair (i : Fin 7) : checkEdgePair packet0346 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0346_ok : checkStripPacket packet0346 = true :=
  checkStripPacket_intro packet0346_shape packet0346_cache packet0346_pair

theorem packet0347_membership : packet0347 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0347_shape : checkStripShape packet0347.row = true := by
  decide +kernel

private theorem packet0347_cache : checkStripCache packet0347 = true := by
  decide +kernel

private theorem packet0347_pair (i : Fin 7) : checkEdgePair packet0347 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0347_ok : checkStripPacket packet0347 = true :=
  checkStripPacket_intro packet0347_shape packet0347_cache packet0347_pair

theorem packet0348_membership : packet0348 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0348_shape : checkStripShape packet0348.row = true := by
  decide +kernel

private theorem packet0348_cache : checkStripCache packet0348 = true := by
  decide +kernel

private theorem packet0348_pair (i : Fin 7) : checkEdgePair packet0348 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0348_ok : checkStripPacket packet0348 = true :=
  checkStripPacket_intro packet0348_shape packet0348_cache packet0348_pair

theorem packet0349_membership : packet0349 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0349_shape : checkStripShape packet0349.row = true := by
  decide +kernel

private theorem packet0349_cache : checkStripCache packet0349 = true := by
  decide +kernel

private theorem packet0349_pair (i : Fin 7) : checkEdgePair packet0349 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0349_ok : checkStripPacket packet0349 = true :=
  checkStripPacket_intro packet0349_shape packet0349_cache packet0349_pair

theorem packet0350_membership : packet0350 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0350_shape : checkStripShape packet0350.row = true := by
  decide +kernel

private theorem packet0350_cache : checkStripCache packet0350 = true := by
  decide +kernel

private theorem packet0350_pair (i : Fin 7) : checkEdgePair packet0350 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0350_ok : checkStripPacket packet0350 = true :=
  checkStripPacket_intro packet0350_shape packet0350_cache packet0350_pair

theorem packet0351_membership : packet0351 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0351_shape : checkStripShape packet0351.row = true := by
  decide +kernel

private theorem packet0351_cache : checkStripCache packet0351 = true := by
  decide +kernel

private theorem packet0351_pair (i : Fin 7) : checkEdgePair packet0351 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0351_ok : checkStripPacket packet0351 = true :=
  checkStripPacket_intro packet0351_shape packet0351_cache packet0351_pair

theorem packet0352_membership : packet0352 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0352_shape : checkStripShape packet0352.row = true := by
  decide +kernel

private theorem packet0352_cache : checkStripCache packet0352 = true := by
  decide +kernel

private theorem packet0352_pair (i : Fin 7) : checkEdgePair packet0352 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0352_ok : checkStripPacket packet0352 = true :=
  checkStripPacket_intro packet0352_shape packet0352_cache packet0352_pair

theorem packet0353_membership : packet0353 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0353_shape : checkStripShape packet0353.row = true := by
  decide +kernel

private theorem packet0353_cache : checkStripCache packet0353 = true := by
  decide +kernel

private theorem packet0353_pair (i : Fin 7) : checkEdgePair packet0353 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0353_ok : checkStripPacket packet0353 = true :=
  checkStripPacket_intro packet0353_shape packet0353_cache packet0353_pair

theorem packet0354_membership : packet0354 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0354_shape : checkStripShape packet0354.row = true := by
  decide +kernel

private theorem packet0354_cache : checkStripCache packet0354 = true := by
  decide +kernel

private theorem packet0354_pair (i : Fin 7) : checkEdgePair packet0354 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0354_ok : checkStripPacket packet0354 = true :=
  checkStripPacket_intro packet0354_shape packet0354_cache packet0354_pair

theorem packet0355_membership : packet0355 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0355_shape : checkStripShape packet0355.row = true := by
  decide +kernel

private theorem packet0355_cache : checkStripCache packet0355 = true := by
  decide +kernel

private theorem packet0355_pair (i : Fin 7) : checkEdgePair packet0355 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0355_ok : checkStripPacket packet0355 = true :=
  checkStripPacket_intro packet0355_shape packet0355_cache packet0355_pair

theorem packet0356_membership : packet0356 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0356_shape : checkStripShape packet0356.row = true := by
  decide +kernel

private theorem packet0356_cache : checkStripCache packet0356 = true := by
  decide +kernel

private theorem packet0356_pair (i : Fin 7) : checkEdgePair packet0356 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0356_ok : checkStripPacket packet0356 = true :=
  checkStripPacket_intro packet0356_shape packet0356_cache packet0356_pair

theorem packet0357_membership : packet0357 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0357_shape : checkStripShape packet0357.row = true := by
  decide +kernel

private theorem packet0357_cache : checkStripCache packet0357 = true := by
  decide +kernel

private theorem packet0357_pair (i : Fin 7) : checkEdgePair packet0357 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0357_ok : checkStripPacket packet0357 = true :=
  checkStripPacket_intro packet0357_shape packet0357_cache packet0357_pair

theorem packet0358_membership : packet0358 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0358_shape : checkStripShape packet0358.row = true := by
  decide +kernel

private theorem packet0358_cache : checkStripCache packet0358 = true := by
  decide +kernel

private theorem packet0358_pair (i : Fin 7) : checkEdgePair packet0358 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0358_ok : checkStripPacket packet0358 = true :=
  checkStripPacket_intro packet0358_shape packet0358_cache packet0358_pair

theorem packet0359_membership : packet0359 ∈ packets014 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0359_shape : checkStripShape packet0359.row = true := by
  decide +kernel

private theorem packet0359_cache : checkStripCache packet0359 = true := by
  decide +kernel

private theorem packet0359_pair (i : Fin 7) : checkEdgePair packet0359 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0359_ok : checkStripPacket packet0359 = true :=
  checkStripPacket_intro packet0359_shape packet0359_cache packet0359_pair

theorem packets014_checked : packets014.all checkStripPacket = true := by
  simp only [packets014, List.all_cons, List.all_nil, Bool.true_and, packet0336_ok,
    packet0337_ok, packet0338_ok, packet0339_ok, packet0340_ok, packet0341_ok,
    packet0342_ok, packet0343_ok, packet0344_ok, packet0345_ok, packet0346_ok,
    packet0347_ok, packet0348_ok, packet0349_ok, packet0350_ok, packet0351_ok,
    packet0352_ok, packet0353_ok, packet0354_ok, packet0355_ok, packet0356_ok,
    packet0357_ok, packet0358_ok, packet0359_ok]

theorem packets014_valid : packets014.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
