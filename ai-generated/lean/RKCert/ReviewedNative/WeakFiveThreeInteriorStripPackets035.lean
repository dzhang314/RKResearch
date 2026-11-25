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

def packet0840 : StripRowPacket :=
  ⟨⟨⟨5,14,4,13⟩,
    ![477,1515,2932,4500,5987,7179,7922],![490,1549,2989,4580,6084,7285,8012]⟩,
    ⟨105544487856074996406287,10444733930090198714939392⟩,
    ⟨7984097820044782015329,631175542932463019718656⟩⟩

def packet0841 : StripRowPacket :=
  ⟨⟨⟨5,15,4,12⟩,
    ![468,1489,2886,4437,5913,7108,7879],![482,1525,2947,4522,6014,7208,7944]⟩,
    ⟨20297598917299967,2457803298462413824⟩,
    ⟨150432233984775575,13864351885222339072⟩⟩

def packet0842 : StripRowPacket :=
  ⟨⟨⟨5,15,4,13⟩,
    ![474,1509,2924,4494,5983,7177,7922],![487,1542,2980,4572,6079,7282,8011]⟩,
    ⟨1124471233046062459,108143345132346208256⟩,
    ⟨8186563433223367,630197812964651776⟩⟩

def packet0843 : StripRowPacket :=
  ⟨⟨⟨5,14,4,14⟩,
    ![482,1533,2965,4551,6052,7251,7980],![495,1564,3017,4624,6142,7355,8103]⟩,
    ⟨5786331884523757092775,474760633185918123406336⟩,
    ⟨18598315685137629127321,1262351085864926039437312⟩⟩

def packet0844 : StripRowPacket :=
  ⟨⟨⟨5,14,4,15⟩,
    ![487,1548,2995,4596,6111,7322,8059],![499,1577,3043,4662,6193,7416,8192]⟩,
    ⟨149054115062970315675813,10444733930090198714939392⟩,
    ⟨13765607023591,818573219180288⟩⟩

def packet0845 : StripRowPacket :=
  ⟨⟨⟨5,15,4,14⟩,
    ![480,1527,2958,4544,6048,7250,7980],![492,1557,3009,4616,6137,7352,8102]⟩,
    ⟨677924056865463185,54071672566173104128⟩,
    ⟨209776557077052573,13864351885222339072⟩⟩

def packet0846 : StripRowPacket :=
  ⟨⟨⟨5,15,4,15⟩,
    ![485,1542,2987,4589,6107,7320,8060],![496,1570,3034,4654,6187,7413,8192]⟩,
    ⟨1587224994415790281,108143345132346208256⟩,
    ⟨61921,3585296⟩⟩

def packet0847 : StripRowPacket :=
  ⟨⟨⟨5,16,3,0⟩,
    ![0,846,2143,3717,5325,6733,7737],![222,1005,2268,3808,5385,6766,7749]⟩,
    ⟨-12910851801953,723200163743200⟩,
    ⟨-74418302985238051,5713763932180142080⟩⟩

def packet0848 : StripRowPacket :=
  ⟨⟨⟨5,17,3,0⟩,
    ![0,843,2137,3710,5319,6730,7736],![220,1001,2262,3800,5379,6762,7748]⟩,
    ⟨-117320206833,6417351614960⟩,
    ⟨-34455740633320028399679,2580698035418556632550400⟩⟩

def packet0849 : StripRowPacket :=
  ⟨⟨⟨5,16,4,2⟩,
    ![192,980,2251,3795,5375,6758,7745],![285,1080,2333,3857,5417,6781,7754]⟩,
    ⟨-122046896816346807,9066037252684755200⟩,
    ⟨-1608669399000473429,148557862236683694080⟩⟩

def packet0850 : StripRowPacket :=
  ⟨⟨⟨5,16,4,3⟩,
    ![264,1056,2315,3843,5405,6774,7750],![332,1152,2403,3912,5453,6800,7760]⟩,
    ⟨-204290252259757613,18132074505369510400⟩,
    ⟨-320615730096189383,37139465559170923520⟩⟩

def packet0851 : StripRowPacket :=
  ⟨⟨⟨5,17,4,2⟩,
    ![192,976,2244,3788,5369,6755,7744],![284,1075,2327,3849,5411,6778,7753]⟩,
    ⟨-69547440897076607107867,5046301237197699292436480⟩,
    ⟨-57295592562343627841821,5161396070837113265100800⟩⟩

def packet0852 : StripRowPacket :=
  ⟨⟨⟨5,17,4,3⟩,
    ![264,1053,2309,3836,5400,6771,7749],![331,1148,2396,3905,5447,6797,7759]⟩,
    ⟨-116387271010794811161297,10092602474395398584872960⟩,
    ⟨-11419925964511799721071,1290349017709278316275200⟩⟩

def packet0853 : StripRowPacket :=
  ⟨⟨⟨5,18,3,0⟩,
    ![0,840,2131,3703,5314,6726,7735],![219,997,2256,3793,5374,6759,7747]⟩,
    ⟨-1336899780823,71474493142624⟩,
    ⟨-3238814515744520151139,236877676272065736427520⟩⟩

def packet0854 : StripRowPacket :=
  ⟨⟨⟨5,19,3,0⟩,
    ![0,837,2125,3696,5308,6723,7734],![218,994,2250,3787,5368,6756,7746]⟩,
    ⟨-71882617,3759267512⟩,
    ⟨-185233414966867386961,13240736767654757430784⟩⟩

def packet0855 : StripRowPacket :=
  ⟨⟨⟨5,18,4,2⟩,
    ![192,973,2239,3782,5364,6752,7743],![283,1072,2320,3843,5405,6775,7752]⟩,
    ⟨-17977362806287745848679,1275263013499568033008640⟩,
    ⟨-5385912879477343108521,473755352544131472855040⟩⟩

def packet0856 : StripRowPacket :=
  ⟨⟨⟨5,18,4,3⟩,
    ![263,1049,2303,3830,5395,6768,7748],![329,1144,2390,3898,5442,6793,7758]⟩,
    ⟨-30078839962281596796757,2550526026999136066017280⟩,
    ⟨-1073549181866411478691,118438838136032868213760⟩⟩

def packet0857 : StripRowPacket :=
  ⟨⟨⟨5,19,4,2⟩,
    ![192,971,2233,3776,5359,6749,7742],![282,1068,2315,3836,5400,6772,7751]⟩,
    ⟨-6283344163051885887,436110126229340186624⟩,
    ⟨-308037934833007930115,26481473535309514861568⟩⟩

def packet0858 : StripRowPacket :=
  ⟨⟨⟨5,19,4,3⟩,
    ![263,1047,2298,3823,5390,6764,7747],![328,1140,2384,3891,5436,6790,7757]⟩,
    ⟨-10510977853246758077,872220252458680373248⟩,
    ⟨-61402259933070271577,6620368383827378715392⟩⟩

def packet0859 : StripRowPacket :=
  ⟨⟨⟨5,16,4,4⟩,
    ![318,1132,2385,3896,5440,6792,7755],![367,1219,2476,3973,5494,6822,7767]⟩,
    ⟨-41121677721705403,4533018626342377600⟩,
    ⟨-191251288353808327,29711572447336738816⟩⟩

def packet0860 : StripRowPacket :=
  ⟨⟨⟨5,16,4,5⟩,
    ![357,1202,2458,3955,5480,6812,7762],![394,1280,2551,4040,5541,6847,7775]⟩,
    ⟨-124683169513885611,18132074505369510400⟩,
    ⟨-315024981576662869,74278931118341847040⟩⟩

def packet0861 : StripRowPacket :=
  ⟨⟨⟨5,17,4,4⟩,
    ![317,1128,2379,3889,5435,6789,7754],![366,1214,2470,3966,5489,6818,7766]⟩,
    ⟨-4683983011371820405343,504630123719769929243648⟩,
    ⟨-2620293473365443840519,397030466987470251161600⟩⟩

def packet0862 : StripRowPacket :=
  ⟨⟨⟨5,17,4,5⟩,
    ![356,1198,2452,3949,5475,6809,7761],![393,1275,2544,4033,5536,6844,7774]⟩,
    ⟨-586545863174198388863,83409937804920649461760⟩,
    ⟨-2244792644945434096921,516139607083711326510080⟩⟩

def packet0863 : StripRowPacket :=
  ⟨⟨⟨5,16,4,6⟩,
    ![386,1264,2530,4020,5526,6837,7770],![416,1333,2623,4111,5595,6877,7785]⟩,
    ⟨-8487962814094961,1813207450536951040⟩,
    ⟨-27622134957964531,13505260203334881280⟩⟩

def packets035 : List StripRowPacket :=
  [packet0840, packet0841, packet0842, packet0843, packet0844, packet0845,
   packet0846, packet0847, packet0848, packet0849, packet0850, packet0851,
   packet0852, packet0853, packet0854, packet0855, packet0856, packet0857,
   packet0858, packet0859, packet0860, packet0861, packet0862, packet0863]

theorem packet0840_membership : packet0840 ∈ packets035 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0840_shape : checkStripShape packet0840.row = true := by
  decide +kernel

private theorem packet0840_cache : checkStripCache packet0840 = true := by
  decide +kernel

private theorem packet0840_pair (i : Fin 7) : checkEdgePair packet0840 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0840_ok : checkStripPacket packet0840 = true :=
  checkStripPacket_intro packet0840_shape packet0840_cache packet0840_pair

theorem packet0841_membership : packet0841 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0841_shape : checkStripShape packet0841.row = true := by
  decide +kernel

private theorem packet0841_cache : checkStripCache packet0841 = true := by
  decide +kernel

private theorem packet0841_pair (i : Fin 7) : checkEdgePair packet0841 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0841_ok : checkStripPacket packet0841 = true :=
  checkStripPacket_intro packet0841_shape packet0841_cache packet0841_pair

theorem packet0842_membership : packet0842 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0842_shape : checkStripShape packet0842.row = true := by
  decide +kernel

private theorem packet0842_cache : checkStripCache packet0842 = true := by
  decide +kernel

private theorem packet0842_pair (i : Fin 7) : checkEdgePair packet0842 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0842_ok : checkStripPacket packet0842 = true :=
  checkStripPacket_intro packet0842_shape packet0842_cache packet0842_pair

theorem packet0843_membership : packet0843 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0843_shape : checkStripShape packet0843.row = true := by
  decide +kernel

private theorem packet0843_cache : checkStripCache packet0843 = true := by
  decide +kernel

private theorem packet0843_pair (i : Fin 7) : checkEdgePair packet0843 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0843_ok : checkStripPacket packet0843 = true :=
  checkStripPacket_intro packet0843_shape packet0843_cache packet0843_pair

theorem packet0844_membership : packet0844 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0844_shape : checkStripShape packet0844.row = true := by
  decide +kernel

private theorem packet0844_cache : checkStripCache packet0844 = true := by
  decide +kernel

private theorem packet0844_pair (i : Fin 7) : checkEdgePair packet0844 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0844_ok : checkStripPacket packet0844 = true :=
  checkStripPacket_intro packet0844_shape packet0844_cache packet0844_pair

theorem packet0845_membership : packet0845 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0845_shape : checkStripShape packet0845.row = true := by
  decide +kernel

private theorem packet0845_cache : checkStripCache packet0845 = true := by
  decide +kernel

private theorem packet0845_pair (i : Fin 7) : checkEdgePair packet0845 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0845_ok : checkStripPacket packet0845 = true :=
  checkStripPacket_intro packet0845_shape packet0845_cache packet0845_pair

theorem packet0846_membership : packet0846 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0846_shape : checkStripShape packet0846.row = true := by
  decide +kernel

private theorem packet0846_cache : checkStripCache packet0846 = true := by
  decide +kernel

private theorem packet0846_pair (i : Fin 7) : checkEdgePair packet0846 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0846_ok : checkStripPacket packet0846 = true :=
  checkStripPacket_intro packet0846_shape packet0846_cache packet0846_pair

theorem packet0847_membership : packet0847 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0847_shape : checkStripShape packet0847.row = true := by
  decide +kernel

private theorem packet0847_cache : checkStripCache packet0847 = true := by
  decide +kernel

private theorem packet0847_pair (i : Fin 7) : checkEdgePair packet0847 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0847_ok : checkStripPacket packet0847 = true :=
  checkStripPacket_intro packet0847_shape packet0847_cache packet0847_pair

theorem packet0848_membership : packet0848 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0848_shape : checkStripShape packet0848.row = true := by
  decide +kernel

private theorem packet0848_cache : checkStripCache packet0848 = true := by
  decide +kernel

private theorem packet0848_pair (i : Fin 7) : checkEdgePair packet0848 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0848_ok : checkStripPacket packet0848 = true :=
  checkStripPacket_intro packet0848_shape packet0848_cache packet0848_pair

theorem packet0849_membership : packet0849 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0849_shape : checkStripShape packet0849.row = true := by
  decide +kernel

private theorem packet0849_cache : checkStripCache packet0849 = true := by
  decide +kernel

private theorem packet0849_pair (i : Fin 7) : checkEdgePair packet0849 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0849_ok : checkStripPacket packet0849 = true :=
  checkStripPacket_intro packet0849_shape packet0849_cache packet0849_pair

theorem packet0850_membership : packet0850 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0850_shape : checkStripShape packet0850.row = true := by
  decide +kernel

private theorem packet0850_cache : checkStripCache packet0850 = true := by
  decide +kernel

private theorem packet0850_pair (i : Fin 7) : checkEdgePair packet0850 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0850_ok : checkStripPacket packet0850 = true :=
  checkStripPacket_intro packet0850_shape packet0850_cache packet0850_pair

theorem packet0851_membership : packet0851 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0851_shape : checkStripShape packet0851.row = true := by
  decide +kernel

private theorem packet0851_cache : checkStripCache packet0851 = true := by
  decide +kernel

private theorem packet0851_pair (i : Fin 7) : checkEdgePair packet0851 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0851_ok : checkStripPacket packet0851 = true :=
  checkStripPacket_intro packet0851_shape packet0851_cache packet0851_pair

theorem packet0852_membership : packet0852 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0852_shape : checkStripShape packet0852.row = true := by
  decide +kernel

private theorem packet0852_cache : checkStripCache packet0852 = true := by
  decide +kernel

private theorem packet0852_pair (i : Fin 7) : checkEdgePair packet0852 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0852_ok : checkStripPacket packet0852 = true :=
  checkStripPacket_intro packet0852_shape packet0852_cache packet0852_pair

theorem packet0853_membership : packet0853 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0853_shape : checkStripShape packet0853.row = true := by
  decide +kernel

private theorem packet0853_cache : checkStripCache packet0853 = true := by
  decide +kernel

private theorem packet0853_pair (i : Fin 7) : checkEdgePair packet0853 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0853_ok : checkStripPacket packet0853 = true :=
  checkStripPacket_intro packet0853_shape packet0853_cache packet0853_pair

theorem packet0854_membership : packet0854 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0854_shape : checkStripShape packet0854.row = true := by
  decide +kernel

private theorem packet0854_cache : checkStripCache packet0854 = true := by
  decide +kernel

private theorem packet0854_pair (i : Fin 7) : checkEdgePair packet0854 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0854_ok : checkStripPacket packet0854 = true :=
  checkStripPacket_intro packet0854_shape packet0854_cache packet0854_pair

theorem packet0855_membership : packet0855 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0855_shape : checkStripShape packet0855.row = true := by
  decide +kernel

private theorem packet0855_cache : checkStripCache packet0855 = true := by
  decide +kernel

private theorem packet0855_pair (i : Fin 7) : checkEdgePair packet0855 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0855_ok : checkStripPacket packet0855 = true :=
  checkStripPacket_intro packet0855_shape packet0855_cache packet0855_pair

theorem packet0856_membership : packet0856 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0856_shape : checkStripShape packet0856.row = true := by
  decide +kernel

private theorem packet0856_cache : checkStripCache packet0856 = true := by
  decide +kernel

private theorem packet0856_pair (i : Fin 7) : checkEdgePair packet0856 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0856_ok : checkStripPacket packet0856 = true :=
  checkStripPacket_intro packet0856_shape packet0856_cache packet0856_pair

theorem packet0857_membership : packet0857 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0857_shape : checkStripShape packet0857.row = true := by
  decide +kernel

private theorem packet0857_cache : checkStripCache packet0857 = true := by
  decide +kernel

private theorem packet0857_pair (i : Fin 7) : checkEdgePair packet0857 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0857_ok : checkStripPacket packet0857 = true :=
  checkStripPacket_intro packet0857_shape packet0857_cache packet0857_pair

theorem packet0858_membership : packet0858 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0858_shape : checkStripShape packet0858.row = true := by
  decide +kernel

private theorem packet0858_cache : checkStripCache packet0858 = true := by
  decide +kernel

private theorem packet0858_pair (i : Fin 7) : checkEdgePair packet0858 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0858_ok : checkStripPacket packet0858 = true :=
  checkStripPacket_intro packet0858_shape packet0858_cache packet0858_pair

theorem packet0859_membership : packet0859 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0859_shape : checkStripShape packet0859.row = true := by
  decide +kernel

private theorem packet0859_cache : checkStripCache packet0859 = true := by
  decide +kernel

private theorem packet0859_pair (i : Fin 7) : checkEdgePair packet0859 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0859_ok : checkStripPacket packet0859 = true :=
  checkStripPacket_intro packet0859_shape packet0859_cache packet0859_pair

theorem packet0860_membership : packet0860 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0860_shape : checkStripShape packet0860.row = true := by
  decide +kernel

private theorem packet0860_cache : checkStripCache packet0860 = true := by
  decide +kernel

private theorem packet0860_pair (i : Fin 7) : checkEdgePair packet0860 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0860_ok : checkStripPacket packet0860 = true :=
  checkStripPacket_intro packet0860_shape packet0860_cache packet0860_pair

theorem packet0861_membership : packet0861 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0861_shape : checkStripShape packet0861.row = true := by
  decide +kernel

private theorem packet0861_cache : checkStripCache packet0861 = true := by
  decide +kernel

private theorem packet0861_pair (i : Fin 7) : checkEdgePair packet0861 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0861_ok : checkStripPacket packet0861 = true :=
  checkStripPacket_intro packet0861_shape packet0861_cache packet0861_pair

theorem packet0862_membership : packet0862 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0862_shape : checkStripShape packet0862.row = true := by
  decide +kernel

private theorem packet0862_cache : checkStripCache packet0862 = true := by
  decide +kernel

private theorem packet0862_pair (i : Fin 7) : checkEdgePair packet0862 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0862_ok : checkStripPacket packet0862 = true :=
  checkStripPacket_intro packet0862_shape packet0862_cache packet0862_pair

theorem packet0863_membership : packet0863 ∈ packets035 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0863_shape : checkStripShape packet0863.row = true := by
  decide +kernel

private theorem packet0863_cache : checkStripCache packet0863 = true := by
  decide +kernel

private theorem packet0863_pair (i : Fin 7) : checkEdgePair packet0863 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0863_ok : checkStripPacket packet0863 = true :=
  checkStripPacket_intro packet0863_shape packet0863_cache packet0863_pair

theorem packets035_checked : packets035.all checkStripPacket = true := by
  simp only [packets035, List.all_cons, List.all_nil, Bool.true_and, packet0840_ok,
    packet0841_ok, packet0842_ok, packet0843_ok, packet0844_ok, packet0845_ok,
    packet0846_ok, packet0847_ok, packet0848_ok, packet0849_ok, packet0850_ok,
    packet0851_ok, packet0852_ok, packet0853_ok, packet0854_ok, packet0855_ok,
    packet0856_ok, packet0857_ok, packet0858_ok, packet0859_ok, packet0860_ok,
    packet0861_ok, packet0862_ok, packet0863_ok]

theorem packets035_valid : packets035.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
