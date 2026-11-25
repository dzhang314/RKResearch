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

def packet0456 : StripRowPacket :=
  ⟨⟨⟨7,0,4,13⟩,
    ![686,1796,3195,4697,6099,7218,7923],![729,1856,3277,4800,6221,7346,8026]⟩,
    ⟨23815653508044605,5732312687327868928⟩,
    ⟨8429721882347455,1540714115070287872⟩⟩

def packet0457 : StripRowPacket :=
  ⟨⟨⟨7,1,4,13⟩,
    ![665,1778,3183,4690,6098,7220,7925],![702,1833,3258,4786,6211,7340,8022]⟩,
    ⟨271118312810793079220988149,61375640927460152970823843840⟩,
    ⟨1593143409837346528794840379,277765960546753075612394516480⟩⟩

def packet0458 : StripRowPacket :=
  ⟨⟨⟨7,2,4,12⟩,
    ![638,1738,3130,4625,6026,7155,7888],![673,1793,3206,4723,6137,7261,7954]⟩,
    ⟨11171653159642723817969793,3081785140913265385614346240⟩,
    ⟨981338717323198308304783,198366213067240203127341056⟩⟩

def packet0459 : StripRowPacket :=
  ⟨⟨⟨7,3,4,12⟩,
    ![624,1725,3120,4619,6024,7155,7889],![655,1776,3193,4713,6131,7258,7953]⟩,
    ⟨1514068173604821360678137,398587400046695769667563520⟩,
    ⟨36542586485279748696493291,7119207909167399396611420160⟩⟩

def packet0460 : StripRowPacket :=
  ⟨⟨⟨6,1,4,13⟩,
    ![631,1743,3152,4664,6077,7206,7918],![682,1818,3250,4786,6219,7354,8039]⟩,
    ⟨836762360051116319747141,181746043621091865033564160⟩,
    ⟨1421138121616264990839,228308673174398076508160⟩⟩

def packet0461 : StripRowPacket :=
  ⟨⟨⟨7,0,4,14⟩,
    ![694,1817,3233,4751,6166,7289,7974],![736,1874,3308,4846,6280,7418,8121]⟩,
    ⟨14619568287445951,2866156343663934464⟩,
    ⟨19795261555533831,3081428230140575744⟩⟩

def packet0462 : StripRowPacket :=
  ⟨⟨⟨7,1,4,14⟩,
    ![673,1799,3220,4743,6164,7292,7977],![709,1850,3289,4832,6270,7412,8115]⟩,
    ⟨165832074202554122127037503,30687820463730076485411921920⟩,
    ⟨747415770448971010182620647,111106384218701230244957806592⟩⟩

def packet0463 : StripRowPacket :=
  ⟨⟨⟨6,0,4,15⟩,
    ![678,1811,3241,4774,6204,7337,8021],![744,1894,3344,4898,6348,7497,8192]⟩,
    ⟨17588723379439,2916620859243520⟩,
    ⟨13691714488841,1773883742625280⟩⟩

def packet0464 : StripRowPacket :=
  ⟨⟨⟨6,1,4,14⟩,
    ![639,1764,3189,4717,6143,7275,7966],![689,1835,3280,4831,6277,7424,8140]⟩,
    ⟨46611073065085535155949,8261183800958721137889280⟩,
    ⟨43153379428666600632787,5936025502534349989212160⟩⟩

def packet0465 : StripRowPacket :=
  ⟨⟨⟨6,1,4,15⟩,
    ![646,1783,3221,4765,6204,7345,8034],![695,1850,3307,4869,6327,7483,8192]⟩,
    ⟨242824970962529445422923,36349208724218373006712832⟩,
    ⟨154876763401,18626522959616⟩⟩

def packet0466 : StripRowPacket :=
  ⟨⟨⟨6,2,4,12⟩,
    ![598,1697,3094,4597,6007,7144,7884],![641,1765,3187,4714,6138,7269,7962]⟩,
    ⟨142162383646043206416183,36433784598041435554307072⟩,
    ⟨102847323023426735252071,18667663478793908148297728⟩⟩

def packet0467 : StripRowPacket :=
  ⟨⟨⟨6,2,4,13⟩,
    ![607,1721,3135,4655,6075,7209,7921],![648,1785,3222,4765,6203,7344,8032]⟩,
    ⟨729428641909249160652841,145735138392165742217228288⟩,
    ⟨8823385776837084305603,1333404534199564867735552⟩⟩

def packet0468 : StripRowPacket :=
  ⟨⟨⟨6,3,4,12⟩,
    ![580,1678,3079,4588,6004,7144,7885],![616,1739,3165,4697,6127,7262,7959]⟩,
    ⟨429572181628455249017,102597083465225164175360⟩,
    ⟨10872187999259912403563,1873195399284810936924160⟩⟩

def packet0469 : StripRowPacket :=
  ⟨⟨⟨6,3,4,13⟩,
    ![589,1701,3120,4646,6073,7210,7923],![623,1758,3200,4748,6192,7336,8027]⟩,
    ⟨199539551524808956421,37308030350990968791040⟩,
    ⟨6526933910680980173777,936597699642405468462080⟩⟩

def packet0470 : StripRowPacket :=
  ⟨⟨⟨6,2,4,14⟩,
    ![615,1741,3172,4708,6141,7279,7972],![655,1802,3253,4809,6262,7414,8129]⟩,
    ⟨445103874617162747820475,72867569196082871108614144⟩,
    ⟨144207478728011625304813,18667663478793908148297728⟩⟩

def packet0471 : StripRowPacket :=
  ⟨⟨⟨6,2,4,15⟩,
    ![622,1759,3203,4755,6202,7349,8042],![661,1816,3279,4848,6312,7473,8192]⟩,
    ⟨1050986856559401830629059,145735138392165742217228288⟩,
    ⟨1609340980147,182200746151424⟩⟩

def packet0472 : StripRowPacket :=
  ⟨⟨⟨6,3,3,7⟩,
    ![597,1721,3156,4699,6138,7280,7975],![635,1790,3256,4831,6300,7466,8192]⟩,
    ⟨190827243359426860371,29313452418635761192960⟩,
    ⟨2226109577,239414581120⟩⟩

def packet0473 : StripRowPacket :=
  ⟨⟨⟨6,4,4,8⟩,
    ![512,1522,2844,4309,5738,6954,7808],![553,1601,2950,4421,5832,7013,7830]⟩,
    ⟨-7974905639289692281,18960064752021110798080⟩,
    ⟨13213913756331342034909,10967134226914662202531840⟩⟩

def packet0474 : StripRowPacket :=
  ⟨⟨⟨6,4,4,9⟩,
    ![530,1565,2908,4379,5797,6990,7820],![567,1637,3008,4493,5901,7061,7849]⟩,
    ⟨17209848610350559093,21668645430881269483520⟩,
    ⟨13281863110778967119881,5483567113457331101265920⟩⟩

def packet0475 : StripRowPacket :=
  ⟨⟨⟨6,5,4,8⟩,
    ![502,1508,2832,4301,5733,6951,7807],![539,1583,2934,4409,5824,7009,7829]⟩,
    ⟨-2728342955131257176243,6973373308423016444984320⟩,
    ⟨5294337406964246936753,4204915160432627504680960⟩⟩

def packet0476 : StripRowPacket :=
  ⟨⟨⟨6,5,4,9⟩,
    ![519,1551,2896,4371,5792,6988,7820],![553,1619,2993,4481,5893,7057,7848]⟩,
    ⟨48722245940716151520789,55786986467384131559874560⟩,
    ⟨7433888008162847954687,2943440612302839253276672⟩⟩

def packet0477 : StripRowPacket :=
  ⟨⟨⟨7,8,4,10⟩,
    ![552,1614,2979,4462,5872,7040,7839],![578,1665,3055,4554,5965,7111,7871]⟩,
    ⟨15910441266422743861429,7645730168515613440927232⟩,
    ⟨882749515612143284729295,252559901784493354802003968⟩⟩

def packet0478 : StripRowPacket :=
  ⟨⟨⟨7,9,4,10⟩,
    ![546,1606,2973,4457,5869,7039,7839],![570,1656,3047,4548,5961,7110,7870]⟩,
    ⟨380985727873561763500024621,177598281734926887417823944704⟩,
    ⟨1011493252537642118396934281,282718341230878452155415830528⟩⟩

def packet0479 : StripRowPacket :=
  ⟨⟨⟨6,4,4,11⟩,
    ![556,1634,3019,4517,5930,7085,7858],![589,1695,3106,4625,6047,7184,7909]⟩,
    ⟨37615793157384370573,11667732155089914337280⟩,
    ⟨13315837788002779662367,2741783556728665550632960⟩⟩

def packets019 : List StripRowPacket :=
  [packet0456, packet0457, packet0458, packet0459, packet0460, packet0461,
   packet0462, packet0463, packet0464, packet0465, packet0466, packet0467,
   packet0468, packet0469, packet0470, packet0471, packet0472, packet0473,
   packet0474, packet0475, packet0476, packet0477, packet0478, packet0479]

theorem packet0456_membership : packet0456 ∈ packets019 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0456_shape : checkStripShape packet0456.row = true := by
  decide +kernel

private theorem packet0456_cache : checkStripCache packet0456 = true := by
  decide +kernel

private theorem packet0456_pair (i : Fin 7) : checkEdgePair packet0456 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0456_ok : checkStripPacket packet0456 = true :=
  checkStripPacket_intro packet0456_shape packet0456_cache packet0456_pair

theorem packet0457_membership : packet0457 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0457_shape : checkStripShape packet0457.row = true := by
  decide +kernel

private theorem packet0457_cache : checkStripCache packet0457 = true := by
  decide +kernel

private theorem packet0457_pair (i : Fin 7) : checkEdgePair packet0457 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0457_ok : checkStripPacket packet0457 = true :=
  checkStripPacket_intro packet0457_shape packet0457_cache packet0457_pair

theorem packet0458_membership : packet0458 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0458_shape : checkStripShape packet0458.row = true := by
  decide +kernel

private theorem packet0458_cache : checkStripCache packet0458 = true := by
  decide +kernel

private theorem packet0458_pair (i : Fin 7) : checkEdgePair packet0458 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0458_ok : checkStripPacket packet0458 = true :=
  checkStripPacket_intro packet0458_shape packet0458_cache packet0458_pair

theorem packet0459_membership : packet0459 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0459_shape : checkStripShape packet0459.row = true := by
  decide +kernel

private theorem packet0459_cache : checkStripCache packet0459 = true := by
  decide +kernel

private theorem packet0459_pair (i : Fin 7) : checkEdgePair packet0459 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0459_ok : checkStripPacket packet0459 = true :=
  checkStripPacket_intro packet0459_shape packet0459_cache packet0459_pair

theorem packet0460_membership : packet0460 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0460_shape : checkStripShape packet0460.row = true := by
  decide +kernel

private theorem packet0460_cache : checkStripCache packet0460 = true := by
  decide +kernel

private theorem packet0460_pair (i : Fin 7) : checkEdgePair packet0460 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0460_ok : checkStripPacket packet0460 = true :=
  checkStripPacket_intro packet0460_shape packet0460_cache packet0460_pair

theorem packet0461_membership : packet0461 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0461_shape : checkStripShape packet0461.row = true := by
  decide +kernel

private theorem packet0461_cache : checkStripCache packet0461 = true := by
  decide +kernel

private theorem packet0461_pair (i : Fin 7) : checkEdgePair packet0461 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0461_ok : checkStripPacket packet0461 = true :=
  checkStripPacket_intro packet0461_shape packet0461_cache packet0461_pair

theorem packet0462_membership : packet0462 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0462_shape : checkStripShape packet0462.row = true := by
  decide +kernel

private theorem packet0462_cache : checkStripCache packet0462 = true := by
  decide +kernel

private theorem packet0462_pair (i : Fin 7) : checkEdgePair packet0462 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0462_ok : checkStripPacket packet0462 = true :=
  checkStripPacket_intro packet0462_shape packet0462_cache packet0462_pair

theorem packet0463_membership : packet0463 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0463_shape : checkStripShape packet0463.row = true := by
  decide +kernel

private theorem packet0463_cache : checkStripCache packet0463 = true := by
  decide +kernel

private theorem packet0463_pair (i : Fin 7) : checkEdgePair packet0463 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0463_ok : checkStripPacket packet0463 = true :=
  checkStripPacket_intro packet0463_shape packet0463_cache packet0463_pair

theorem packet0464_membership : packet0464 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0464_shape : checkStripShape packet0464.row = true := by
  decide +kernel

private theorem packet0464_cache : checkStripCache packet0464 = true := by
  decide +kernel

private theorem packet0464_pair (i : Fin 7) : checkEdgePair packet0464 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0464_ok : checkStripPacket packet0464 = true :=
  checkStripPacket_intro packet0464_shape packet0464_cache packet0464_pair

theorem packet0465_membership : packet0465 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0465_shape : checkStripShape packet0465.row = true := by
  decide +kernel

private theorem packet0465_cache : checkStripCache packet0465 = true := by
  decide +kernel

private theorem packet0465_pair (i : Fin 7) : checkEdgePair packet0465 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0465_ok : checkStripPacket packet0465 = true :=
  checkStripPacket_intro packet0465_shape packet0465_cache packet0465_pair

theorem packet0466_membership : packet0466 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0466_shape : checkStripShape packet0466.row = true := by
  decide +kernel

private theorem packet0466_cache : checkStripCache packet0466 = true := by
  decide +kernel

private theorem packet0466_pair (i : Fin 7) : checkEdgePair packet0466 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0466_ok : checkStripPacket packet0466 = true :=
  checkStripPacket_intro packet0466_shape packet0466_cache packet0466_pair

theorem packet0467_membership : packet0467 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0467_shape : checkStripShape packet0467.row = true := by
  decide +kernel

private theorem packet0467_cache : checkStripCache packet0467 = true := by
  decide +kernel

private theorem packet0467_pair (i : Fin 7) : checkEdgePair packet0467 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0467_ok : checkStripPacket packet0467 = true :=
  checkStripPacket_intro packet0467_shape packet0467_cache packet0467_pair

theorem packet0468_membership : packet0468 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0468_shape : checkStripShape packet0468.row = true := by
  decide +kernel

private theorem packet0468_cache : checkStripCache packet0468 = true := by
  decide +kernel

private theorem packet0468_pair (i : Fin 7) : checkEdgePair packet0468 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0468_ok : checkStripPacket packet0468 = true :=
  checkStripPacket_intro packet0468_shape packet0468_cache packet0468_pair

theorem packet0469_membership : packet0469 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0469_shape : checkStripShape packet0469.row = true := by
  decide +kernel

private theorem packet0469_cache : checkStripCache packet0469 = true := by
  decide +kernel

private theorem packet0469_pair (i : Fin 7) : checkEdgePair packet0469 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0469_ok : checkStripPacket packet0469 = true :=
  checkStripPacket_intro packet0469_shape packet0469_cache packet0469_pair

theorem packet0470_membership : packet0470 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0470_shape : checkStripShape packet0470.row = true := by
  decide +kernel

private theorem packet0470_cache : checkStripCache packet0470 = true := by
  decide +kernel

private theorem packet0470_pair (i : Fin 7) : checkEdgePair packet0470 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0470_ok : checkStripPacket packet0470 = true :=
  checkStripPacket_intro packet0470_shape packet0470_cache packet0470_pair

theorem packet0471_membership : packet0471 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0471_shape : checkStripShape packet0471.row = true := by
  decide +kernel

private theorem packet0471_cache : checkStripCache packet0471 = true := by
  decide +kernel

private theorem packet0471_pair (i : Fin 7) : checkEdgePair packet0471 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0471_ok : checkStripPacket packet0471 = true :=
  checkStripPacket_intro packet0471_shape packet0471_cache packet0471_pair

theorem packet0472_membership : packet0472 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0472_shape : checkStripShape packet0472.row = true := by
  decide +kernel

private theorem packet0472_cache : checkStripCache packet0472 = true := by
  decide +kernel

private theorem packet0472_pair (i : Fin 7) : checkEdgePair packet0472 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0472_ok : checkStripPacket packet0472 = true :=
  checkStripPacket_intro packet0472_shape packet0472_cache packet0472_pair

theorem packet0473_membership : packet0473 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0473_shape : checkStripShape packet0473.row = true := by
  decide +kernel

private theorem packet0473_cache : checkStripCache packet0473 = true := by
  decide +kernel

private theorem packet0473_pair (i : Fin 7) : checkEdgePair packet0473 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0473_ok : checkStripPacket packet0473 = true :=
  checkStripPacket_intro packet0473_shape packet0473_cache packet0473_pair

theorem packet0474_membership : packet0474 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0474_shape : checkStripShape packet0474.row = true := by
  decide +kernel

private theorem packet0474_cache : checkStripCache packet0474 = true := by
  decide +kernel

private theorem packet0474_pair (i : Fin 7) : checkEdgePair packet0474 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0474_ok : checkStripPacket packet0474 = true :=
  checkStripPacket_intro packet0474_shape packet0474_cache packet0474_pair

theorem packet0475_membership : packet0475 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0475_shape : checkStripShape packet0475.row = true := by
  decide +kernel

private theorem packet0475_cache : checkStripCache packet0475 = true := by
  decide +kernel

private theorem packet0475_pair (i : Fin 7) : checkEdgePair packet0475 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0475_ok : checkStripPacket packet0475 = true :=
  checkStripPacket_intro packet0475_shape packet0475_cache packet0475_pair

theorem packet0476_membership : packet0476 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0476_shape : checkStripShape packet0476.row = true := by
  decide +kernel

private theorem packet0476_cache : checkStripCache packet0476 = true := by
  decide +kernel

private theorem packet0476_pair (i : Fin 7) : checkEdgePair packet0476 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0476_ok : checkStripPacket packet0476 = true :=
  checkStripPacket_intro packet0476_shape packet0476_cache packet0476_pair

theorem packet0477_membership : packet0477 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0477_shape : checkStripShape packet0477.row = true := by
  decide +kernel

private theorem packet0477_cache : checkStripCache packet0477 = true := by
  decide +kernel

private theorem packet0477_pair (i : Fin 7) : checkEdgePair packet0477 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0477_ok : checkStripPacket packet0477 = true :=
  checkStripPacket_intro packet0477_shape packet0477_cache packet0477_pair

theorem packet0478_membership : packet0478 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0478_shape : checkStripShape packet0478.row = true := by
  decide +kernel

private theorem packet0478_cache : checkStripCache packet0478 = true := by
  decide +kernel

private theorem packet0478_pair (i : Fin 7) : checkEdgePair packet0478 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0478_ok : checkStripPacket packet0478 = true :=
  checkStripPacket_intro packet0478_shape packet0478_cache packet0478_pair

theorem packet0479_membership : packet0479 ∈ packets019 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0479_shape : checkStripShape packet0479.row = true := by
  decide +kernel

private theorem packet0479_cache : checkStripCache packet0479 = true := by
  decide +kernel

private theorem packet0479_pair (i : Fin 7) : checkEdgePair packet0479 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0479_ok : checkStripPacket packet0479 = true :=
  checkStripPacket_intro packet0479_shape packet0479_cache packet0479_pair

theorem packets019_checked : packets019.all checkStripPacket = true := by
  simp only [packets019, List.all_cons, List.all_nil, Bool.true_and, packet0456_ok,
    packet0457_ok, packet0458_ok, packet0459_ok, packet0460_ok, packet0461_ok,
    packet0462_ok, packet0463_ok, packet0464_ok, packet0465_ok, packet0466_ok,
    packet0467_ok, packet0468_ok, packet0469_ok, packet0470_ok, packet0471_ok,
    packet0472_ok, packet0473_ok, packet0474_ok, packet0475_ok, packet0476_ok,
    packet0477_ok, packet0478_ok, packet0479_ok]

theorem packets019_valid : packets019.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
