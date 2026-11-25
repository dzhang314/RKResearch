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

def packet0912 : StripRowPacket :=
  ⟨⟨⟨6,33,4,11⟩,
    ![458,1462,2838,4373,5842,7047,7849],![471,1494,2895,4451,5931,7126,7891]⟩,
    ⟨25565330627499584408241543,3964306857684681270564904960⟩,
    ⟨378413864838776820702994599,42618760592758086796894714880⟩⟩

def packet0913 : StripRowPacket :=
  ⟨⟨⟨6,34,4,10⟩,
    ![448,1432,2786,4303,5768,6989,7824],![463,1468,2848,4385,5855,7058,7856]⟩,
    ⟨4905693363963622171164749,1141462068920062447461849088⟩,
    ⟨530200750409121594609348093,78511655214641850920119132160⟩⟩

def packet0914 : StripRowPacket :=
  ⟨⟨⟨6,35,4,10⟩,
    ![448,1430,2783,4300,5766,6988,7824],![462,1466,2844,4382,5853,7057,7855]⟩,
    ⟨15171125105398873527513343,3483384840353626031815946240⟩,
    ⟨708210676570947786081973,103598345325099757555005440⟩⟩

def packet0915 : StripRowPacket :=
  ⟨⟨⟨6,34,4,11⟩,
    ![457,1459,2835,4370,5840,7046,7849],![470,1492,2891,4447,5928,7124,7890]⟩,
    ⟨74586444858298110906827567,11414620689200624474618490880⟩,
    ⟨882276106830583748468206873,98139569018302313650148915200⟩⟩

def packet0916 : StripRowPacket :=
  ⟨⟨⟨6,35,4,11⟩,
    ![457,1457,2832,4367,5838,7045,7848],![469,1489,2888,4444,5926,7123,7890]⟩,
    ⟨9222585296119885118213693,1393353936141450412726378496⟩,
    ⟨235689369076843769173189,25899586331274939388751360⟩⟩

def packet0917 : StripRowPacket :=
  ⟨⟨⟨6,36,4,8⟩,
    ![423,1357,2662,4154,5631,6897,7790],![441,1404,2736,4240,5708,6948,7810]⟩,
    ⟨-42143997084021187890033,249524260340723564609304320⟩,
    ⟨1109445245955506986448157,474807425247705340004065280⟩⟩

def packet0918 : StripRowPacket :=
  ⟨⟨⟨6,37,4,8⟩,
    ![422,1355,2660,4151,5628,6896,7789],![440,1402,2733,4237,5705,6946,7809]⟩,
    ⟨-54777207461224545077311,330516213074776361473764352⟩,
    ⟨53716088887278784703315219,22713552870233596537849819136⟩⟩

def packet0919 : StripRowPacket :=
  ⟨⟨⟨6,36,4,9⟩,
    ![436,1395,2724,4227,5695,6938,7805],![452,1436,2792,4311,5778,6998,7829]⟩,
    ⟨4235386085698496175276283,1996194082725788516874434560⟩,
    ⟨1098597082811972759449673,237403712623852670002032640⟩⟩

def packet0920 : StripRowPacket :=
  ⟨⟨⟨6,37,4,9⟩,
    ![435,1393,2721,4224,5693,6937,7804],![451,1434,2789,4308,5775,6996,7829]⟩,
    ⟨5689169334229064399790505,2644129704598210891790114816⟩,
    ⟨53179086138322640563548743,11356776435116798268924909568⟩⟩

def packet0921 : StripRowPacket :=
  ⟨⟨⟨6,38,4,8⟩,
    ![421,1353,2657,4148,5626,6895,7789],![439,1400,2730,4234,5703,6945,7809]⟩,
    ⟨-2358627924010859382529,14504104880507541214952960⟩,
    ⟨124001511275376195361357883,51816988841425741943663779840⟩⟩

def packet0922 : StripRowPacket :=
  ⟨⟨⟨6,39,4,8⟩,
    ![420,1352,2654,4146,5624,6894,7789],![438,1398,2727,4231,5701,6944,7809]⟩,
    ⟨-217416713928742826601,1362681385739498505640960⟩,
    ⟨64084027119380979633,26469821128206209585920⟩⟩

def packet0923 : StripRowPacket :=
  ⟨⟨⟨6,38,4,9⟩,
    ![434,1391,2718,4221,5691,6936,7804],![450,1432,2786,4305,5773,6995,7829]⟩,
    ⟨3290287354264965450356451,1508426907572784286355107840⟩,
    ⟨1888230508696724080693103,398592221857121091874336768⟩⟩

def packet0924 : StripRowPacket :=
  ⟨⟨⟨6,39,4,9⟩,
    ![434,1389,2716,4218,5689,6935,7803],![449,1430,2783,4302,5771,6994,7828]⟩,
    ⟨3442811875748299679993,1557350155130855435018240⟩,
    ⟨824404561481100856471,172053837333340362308480⟩⟩

def packet0925 : StripRowPacket :=
  ⟨⟨⟨6,36,4,10⟩,
    ![447,1428,2780,4297,5764,6987,7823],![461,1463,2841,4379,5851,7056,7855]⟩,
    ⟨880792414806916185367283,199619408272578851687443456⟩,
    ⟨656988617058476810270107,94961485049541068000813056⟩⟩

def packet0926 : StripRowPacket :=
  ⟨⟨⟨6,37,4,10⟩,
    ![446,1425,2777,4294,5762,6986,7823],![460,1461,2838,4376,5848,7055,7855]⟩,
    ⟨5908278164073962580099749,1322064852299105445895057408⟩,
    ⟨14454568696910161595534523,2064868442748508776168165376⟩⟩

def packet0927 : StripRowPacket :=
  ⟨⟨⟨6,36,4,11⟩,
    ![456,1455,2829,4364,5836,7044,7848],![468,1487,2884,4441,5923,7122,7890]⟩,
    ⟨13380462210439827532069377,1996194082725788516874434560⟩,
    ⟨1093173001240205645950431,118701856311926335001016320⟩⟩

def packet0928 : StripRowPacket :=
  ⟨⟨⟨6,37,4,11⟩,
    ![455,1453,2826,4361,5834,7043,7848],![467,1484,2881,4438,5921,7121,7889]⟩,
    ⟨1380303332466675840046807,203394592661400837830008832⟩,
    ⟨52910584763844568493665505,5678388217558399134462454784⟩⟩

def packet0929 : StripRowPacket :=
  ⟨⟨⟨6,38,4,10⟩,
    ![445,1423,2774,4291,5760,6985,7823],![459,1459,2835,4373,5846,7053,7854]⟩,
    ⟨3412936006313530138247959,754213453786392143177553920⟩,
    ⟨366938420985772065618848897,51816988841425741943663779840⟩⟩

def packet0930 : StripRowPacket :=
  ⟨⟨⟨6,39,4,10⟩,
    ![444,1421,2771,4289,5758,6984,7822],![458,1457,2832,4370,5844,7052,7854]⟩,
    ⟨4993869997190613813271,1090145108591598804512768⟩,
    ⟨492905178674490138131,68821534933336144923392⟩⟩

def packet0931 : StripRowPacket :=
  ⟨⟨⟨6,38,4,11⟩,
    ![454,1450,2823,4358,5832,7041,7847],![466,1482,2878,4435,5919,7120,7889]⟩,
    ⟨188390121290711910957007,27425943774050623388274688⟩,
    ⟨122101718960242500186898601,12954247210356435485915944960⟩⟩

def packet0932 : StripRowPacket :=
  ⟨⟨⟨6,39,4,11⟩,
    ![453,1448,2820,4356,5830,7040,7847],![465,1480,2875,4431,5917,7118,7889]⟩,
    ⟨75777716813574178505469,10901451085915988045127680⟩,
    ⟨205015166486418729273,21506729666667545288560⟩⟩

def packet0933 : StripRowPacket :=
  ⟨⟨⟨5,16,4,12⟩,
    ![466,1484,2879,4431,5909,7106,7879],![479,1519,2939,4515,6009,7205,7943]⟩,
    ⟨38485405024166599,4533018626342377600⟩,
    ⟨1653395387156685541,148557862236683694080⟩⟩

def packet0934 : StripRowPacket :=
  ⟨⟨⟨5,16,4,13⟩,
    ![472,1504,2917,4487,5979,7175,7922],![485,1536,2972,4564,6073,7279,8010]⟩,
    ⟨193745161469602397,18132074505369510400⟩,
    ⟨989800932886200719,74278931118341847040⟩⟩

def packet0935 : StripRowPacket :=
  ⟨⟨⟨5,17,4,12⟩,
    ![464,1479,2872,4425,5905,7104,7878],![477,1513,2932,4508,6003,7202,7942]⟩,
    ⟨21995306509857704082159,2523150618598849646218240⟩,
    ⟨58863294480620661733549,5161396070837113265100800⟩⟩

def packets038 : List StripRowPacket :=
  [packet0912, packet0913, packet0914, packet0915, packet0916, packet0917,
   packet0918, packet0919, packet0920, packet0921, packet0922, packet0923,
   packet0924, packet0925, packet0926, packet0927, packet0928, packet0929,
   packet0930, packet0931, packet0932, packet0933, packet0934, packet0935]

theorem packet0912_membership : packet0912 ∈ packets038 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0912_shape : checkStripShape packet0912.row = true := by
  decide +kernel

private theorem packet0912_cache : checkStripCache packet0912 = true := by
  decide +kernel

private theorem packet0912_pair (i : Fin 7) : checkEdgePair packet0912 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0912_ok : checkStripPacket packet0912 = true :=
  checkStripPacket_intro packet0912_shape packet0912_cache packet0912_pair

theorem packet0913_membership : packet0913 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0913_shape : checkStripShape packet0913.row = true := by
  decide +kernel

private theorem packet0913_cache : checkStripCache packet0913 = true := by
  decide +kernel

private theorem packet0913_pair (i : Fin 7) : checkEdgePair packet0913 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0913_ok : checkStripPacket packet0913 = true :=
  checkStripPacket_intro packet0913_shape packet0913_cache packet0913_pair

theorem packet0914_membership : packet0914 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0914_shape : checkStripShape packet0914.row = true := by
  decide +kernel

private theorem packet0914_cache : checkStripCache packet0914 = true := by
  decide +kernel

private theorem packet0914_pair (i : Fin 7) : checkEdgePair packet0914 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0914_ok : checkStripPacket packet0914 = true :=
  checkStripPacket_intro packet0914_shape packet0914_cache packet0914_pair

theorem packet0915_membership : packet0915 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0915_shape : checkStripShape packet0915.row = true := by
  decide +kernel

private theorem packet0915_cache : checkStripCache packet0915 = true := by
  decide +kernel

private theorem packet0915_pair (i : Fin 7) : checkEdgePair packet0915 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0915_ok : checkStripPacket packet0915 = true :=
  checkStripPacket_intro packet0915_shape packet0915_cache packet0915_pair

theorem packet0916_membership : packet0916 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0916_shape : checkStripShape packet0916.row = true := by
  decide +kernel

private theorem packet0916_cache : checkStripCache packet0916 = true := by
  decide +kernel

private theorem packet0916_pair (i : Fin 7) : checkEdgePair packet0916 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0916_ok : checkStripPacket packet0916 = true :=
  checkStripPacket_intro packet0916_shape packet0916_cache packet0916_pair

theorem packet0917_membership : packet0917 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0917_shape : checkStripShape packet0917.row = true := by
  decide +kernel

private theorem packet0917_cache : checkStripCache packet0917 = true := by
  decide +kernel

private theorem packet0917_pair (i : Fin 7) : checkEdgePair packet0917 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0917_ok : checkStripPacket packet0917 = true :=
  checkStripPacket_intro packet0917_shape packet0917_cache packet0917_pair

theorem packet0918_membership : packet0918 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0918_shape : checkStripShape packet0918.row = true := by
  decide +kernel

private theorem packet0918_cache : checkStripCache packet0918 = true := by
  decide +kernel

private theorem packet0918_pair (i : Fin 7) : checkEdgePair packet0918 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0918_ok : checkStripPacket packet0918 = true :=
  checkStripPacket_intro packet0918_shape packet0918_cache packet0918_pair

theorem packet0919_membership : packet0919 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0919_shape : checkStripShape packet0919.row = true := by
  decide +kernel

private theorem packet0919_cache : checkStripCache packet0919 = true := by
  decide +kernel

private theorem packet0919_pair (i : Fin 7) : checkEdgePair packet0919 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0919_ok : checkStripPacket packet0919 = true :=
  checkStripPacket_intro packet0919_shape packet0919_cache packet0919_pair

theorem packet0920_membership : packet0920 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0920_shape : checkStripShape packet0920.row = true := by
  decide +kernel

private theorem packet0920_cache : checkStripCache packet0920 = true := by
  decide +kernel

private theorem packet0920_pair (i : Fin 7) : checkEdgePair packet0920 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0920_ok : checkStripPacket packet0920 = true :=
  checkStripPacket_intro packet0920_shape packet0920_cache packet0920_pair

theorem packet0921_membership : packet0921 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0921_shape : checkStripShape packet0921.row = true := by
  decide +kernel

private theorem packet0921_cache : checkStripCache packet0921 = true := by
  decide +kernel

private theorem packet0921_pair (i : Fin 7) : checkEdgePair packet0921 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0921_ok : checkStripPacket packet0921 = true :=
  checkStripPacket_intro packet0921_shape packet0921_cache packet0921_pair

theorem packet0922_membership : packet0922 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0922_shape : checkStripShape packet0922.row = true := by
  decide +kernel

private theorem packet0922_cache : checkStripCache packet0922 = true := by
  decide +kernel

private theorem packet0922_pair (i : Fin 7) : checkEdgePair packet0922 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0922_ok : checkStripPacket packet0922 = true :=
  checkStripPacket_intro packet0922_shape packet0922_cache packet0922_pair

theorem packet0923_membership : packet0923 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0923_shape : checkStripShape packet0923.row = true := by
  decide +kernel

private theorem packet0923_cache : checkStripCache packet0923 = true := by
  decide +kernel

private theorem packet0923_pair (i : Fin 7) : checkEdgePair packet0923 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0923_ok : checkStripPacket packet0923 = true :=
  checkStripPacket_intro packet0923_shape packet0923_cache packet0923_pair

theorem packet0924_membership : packet0924 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0924_shape : checkStripShape packet0924.row = true := by
  decide +kernel

private theorem packet0924_cache : checkStripCache packet0924 = true := by
  decide +kernel

private theorem packet0924_pair (i : Fin 7) : checkEdgePair packet0924 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0924_ok : checkStripPacket packet0924 = true :=
  checkStripPacket_intro packet0924_shape packet0924_cache packet0924_pair

theorem packet0925_membership : packet0925 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0925_shape : checkStripShape packet0925.row = true := by
  decide +kernel

private theorem packet0925_cache : checkStripCache packet0925 = true := by
  decide +kernel

private theorem packet0925_pair (i : Fin 7) : checkEdgePair packet0925 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0925_ok : checkStripPacket packet0925 = true :=
  checkStripPacket_intro packet0925_shape packet0925_cache packet0925_pair

theorem packet0926_membership : packet0926 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0926_shape : checkStripShape packet0926.row = true := by
  decide +kernel

private theorem packet0926_cache : checkStripCache packet0926 = true := by
  decide +kernel

private theorem packet0926_pair (i : Fin 7) : checkEdgePair packet0926 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0926_ok : checkStripPacket packet0926 = true :=
  checkStripPacket_intro packet0926_shape packet0926_cache packet0926_pair

theorem packet0927_membership : packet0927 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0927_shape : checkStripShape packet0927.row = true := by
  decide +kernel

private theorem packet0927_cache : checkStripCache packet0927 = true := by
  decide +kernel

private theorem packet0927_pair (i : Fin 7) : checkEdgePair packet0927 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0927_ok : checkStripPacket packet0927 = true :=
  checkStripPacket_intro packet0927_shape packet0927_cache packet0927_pair

theorem packet0928_membership : packet0928 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0928_shape : checkStripShape packet0928.row = true := by
  decide +kernel

private theorem packet0928_cache : checkStripCache packet0928 = true := by
  decide +kernel

private theorem packet0928_pair (i : Fin 7) : checkEdgePair packet0928 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0928_ok : checkStripPacket packet0928 = true :=
  checkStripPacket_intro packet0928_shape packet0928_cache packet0928_pair

theorem packet0929_membership : packet0929 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0929_shape : checkStripShape packet0929.row = true := by
  decide +kernel

private theorem packet0929_cache : checkStripCache packet0929 = true := by
  decide +kernel

private theorem packet0929_pair (i : Fin 7) : checkEdgePair packet0929 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0929_ok : checkStripPacket packet0929 = true :=
  checkStripPacket_intro packet0929_shape packet0929_cache packet0929_pair

theorem packet0930_membership : packet0930 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0930_shape : checkStripShape packet0930.row = true := by
  decide +kernel

private theorem packet0930_cache : checkStripCache packet0930 = true := by
  decide +kernel

private theorem packet0930_pair (i : Fin 7) : checkEdgePair packet0930 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0930_ok : checkStripPacket packet0930 = true :=
  checkStripPacket_intro packet0930_shape packet0930_cache packet0930_pair

theorem packet0931_membership : packet0931 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0931_shape : checkStripShape packet0931.row = true := by
  decide +kernel

private theorem packet0931_cache : checkStripCache packet0931 = true := by
  decide +kernel

private theorem packet0931_pair (i : Fin 7) : checkEdgePair packet0931 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0931_ok : checkStripPacket packet0931 = true :=
  checkStripPacket_intro packet0931_shape packet0931_cache packet0931_pair

theorem packet0932_membership : packet0932 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0932_shape : checkStripShape packet0932.row = true := by
  decide +kernel

private theorem packet0932_cache : checkStripCache packet0932 = true := by
  decide +kernel

private theorem packet0932_pair (i : Fin 7) : checkEdgePair packet0932 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0932_ok : checkStripPacket packet0932 = true :=
  checkStripPacket_intro packet0932_shape packet0932_cache packet0932_pair

theorem packet0933_membership : packet0933 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0933_shape : checkStripShape packet0933.row = true := by
  decide +kernel

private theorem packet0933_cache : checkStripCache packet0933 = true := by
  decide +kernel

private theorem packet0933_pair (i : Fin 7) : checkEdgePair packet0933 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0933_ok : checkStripPacket packet0933 = true :=
  checkStripPacket_intro packet0933_shape packet0933_cache packet0933_pair

theorem packet0934_membership : packet0934 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0934_shape : checkStripShape packet0934.row = true := by
  decide +kernel

private theorem packet0934_cache : checkStripCache packet0934 = true := by
  decide +kernel

private theorem packet0934_pair (i : Fin 7) : checkEdgePair packet0934 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0934_ok : checkStripPacket packet0934 = true :=
  checkStripPacket_intro packet0934_shape packet0934_cache packet0934_pair

theorem packet0935_membership : packet0935 ∈ packets038 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0935_shape : checkStripShape packet0935.row = true := by
  decide +kernel

private theorem packet0935_cache : checkStripCache packet0935 = true := by
  decide +kernel

private theorem packet0935_pair (i : Fin 7) : checkEdgePair packet0935 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0935_ok : checkStripPacket packet0935 = true :=
  checkStripPacket_intro packet0935_shape packet0935_cache packet0935_pair

theorem packets038_checked : packets038.all checkStripPacket = true := by
  simp only [packets038, List.all_cons, List.all_nil, Bool.true_and, packet0912_ok,
    packet0913_ok, packet0914_ok, packet0915_ok, packet0916_ok, packet0917_ok,
    packet0918_ok, packet0919_ok, packet0920_ok, packet0921_ok, packet0922_ok,
    packet0923_ok, packet0924_ok, packet0925_ok, packet0926_ok, packet0927_ok,
    packet0928_ok, packet0929_ok, packet0930_ok, packet0931_ok, packet0932_ok,
    packet0933_ok, packet0934_ok, packet0935_ok]

theorem packets038_valid : packets038.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
