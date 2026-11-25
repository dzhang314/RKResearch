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

def packet0936 : StripRowPacket :=
  ⟨⟨⟨5,17,4,13⟩,
    ![470,1499,2911,4481,5974,7174,7921],![482,1530,2964,4557,6068,7277,8009]⟩,
    ⟨110688836822789219383073,10092602474395398584872960⟩,
    ⟨35239591592458545345543,2580698035418556632550400⟩⟩

def packet0937 : StripRowPacket :=
  ⟨⟨⟨5,16,4,14⟩,
    ![478,1521,2951,4538,6044,7248,7980],![489,1551,3001,4608,6131,7349,8101]⟩,
    ⟨116774351421269199,9066037252684755200⟩,
    ⟨35473974529047959,2285505572872056832⟩⟩

def packet0938 : StripRowPacket :=
  ⟨⟨⟨5,16,4,15⟩,
    ![482,1537,2980,4583,6103,7319,8060],![494,1564,3026,4646,6182,7410,8192]⟩,
    ⟨273352244215474399,18132074505369510400⟩,
    ⟨19922602208761,1124484242435840⟩⟩

def packet0939 : StripRowPacket :=
  ⟨⟨⟨5,17,4,14⟩,
    ![476,1516,2944,4532,6040,7247,7981],![487,1545,2993,4601,6126,7347,8100]⟩,
    ⟨13339644760614762243751,1009260247439539858487296⟩,
    ⟨82095071889213519648623,5161396070837113265100800⟩⟩

def packet0940 : StripRowPacket :=
  ⟨⟨⟨5,17,4,15⟩,
    ![480,1532,2973,4576,6099,7317,8061],![491,1558,3018,4639,6177,7408,8192]⟩,
    ⟨156104058389506025491947,10092602474395398584872960⟩,
    ⟨185296796609,10205744897920⟩⟩

def packet0941 : StripRowPacket :=
  ⟨⟨⟨5,18,4,12⟩,
    ![462,1474,2866,4419,5901,7102,7878],![475,1508,2925,4501,5999,7200,7941]⟩,
    ⟨518275702053714938833,57966500613616728773120⟩,
    ⟨5531248640639628829049,473755352544131472855040⟩⟩

def packet0942 : StripRowPacket :=
  ⟨⟨⟨5,18,4,13⟩,
    ![468,1494,2904,4476,5971,7172,7921],![480,1525,2957,4550,6063,7274,8008]⟩,
    ⟨28680016540657352209253,2550526026999136066017280⟩,
    ⟨473068913760809001629,33839668038866533775360⟩⟩

def packet0943 : StripRowPacket :=
  ⟨⟨⟨5,19,4,12⟩,
    ![460,1470,2860,4414,5897,7100,7878],![473,1503,2918,4494,5994,7197,7940]⟩,
    ⟨285372014373798757,31150723302095727616⟩,
    ⟨316251016174260507955,26481473535309514861568⟩⟩

def packet0944 : StripRowPacket :=
  ⟨⟨⟨5,19,4,13⟩,
    ![466,1490,2898,4470,5967,7171,7921],![478,1520,2950,4544,6059,7272,8007]⟩,
    ⟨10046126875323378893,872220252458680373248⟩,
    ⟨189339955637493675881,13240736767654757430784⟩⟩

def packet0945 : StripRowPacket :=
  ⟨⟨⟨5,18,4,14⟩,
    ![474,1512,2938,4526,6036,7245,7981],![485,1540,2986,4594,6122,7344,8099]⟩,
    ⟨17277951095475623554927,1275263013499568033008640⟩,
    ⟨7714680944663023216563,473755352544131472855040⟩⟩

def packet0946 : StripRowPacket :=
  ⟨⟨⟨5,18,4,15⟩,
    ![478,1527,2967,4570,6095,7316,8061],![489,1553,3011,4632,6172,7406,8192]⟩,
    ⟨8086357568249028402091,510105205399827213203456⟩,
    ⟨2158594925791,116125344887552⟩⟩

def packet0947 : StripRowPacket :=
  ⟨⟨⟨5,19,4,14⟩,
    ![472,1507,2932,4520,6032,7243,7981],![483,1535,2979,4588,6117,7342,8098]⟩,
    ⟨6050918674090196295,436110126229340186624⟩,
    ⟨441108806375714195569,26481473535309514861568⟩⟩

def packet0948 : StripRowPacket :=
  ⟨⟨⟨5,19,4,15⟩,
    ![477,1522,2961,4565,6091,7314,8062],![487,1547,3004,4626,6168,7403,8192]⟩,
    ⟨14157547821037406287,872220252458680373248⟩,
    ⟨2014869589,105963695552⟩⟩

def packet0949 : StripRowPacket :=
  ⟨⟨⟨6,40,4,8⟩,
    ![420,1350,2651,4143,5622,6892,7788],![438,1396,2724,4228,5698,6942,7808]⟩,
    ⟨-9903635949337228111,63271115087146752031840⟩,
    ⟨4375754254790397857111,1786890679093493782814720⟩⟩

def packet0950 : StripRowPacket :=
  ⟨⟨⟨6,41,4,8⟩,
    ![419,1348,2649,4140,5620,6891,7788],![437,1394,2722,4225,5696,6941,7808]⟩,
    ⟨-1706454240500333366263733,11113796879094241592749265920⟩,
    ⟨111149146030972837353965603,44882746083521784461199953920⟩⟩

def packet0951 : StripRowPacket :=
  ⟨⟨⟨6,40,4,9⟩,
    ![433,1387,2713,4215,5686,6934,7803],![448,1428,2780,4299,5769,6993,7828]⟩,
    ⟨29477677833939338523803,13160391938126524422622720⟩,
    ⟨6060869861642948932249,1250823475365445647970304⟩⟩

def packet0952 : StripRowPacket :=
  ⟨⟨⟨6,41,4,9⟩,
    ![432,1386,2710,4213,5684,6932,7803],![448,1426,2777,4297,5767,6991,7827]⟩,
    ⟨201725027516578688056452483,88910375032753932741994127360⟩,
    ⟨8457157503825384460182259,1726259464750837863892305920⟩⟩

def packet0953 : StripRowPacket :=
  ⟨⟨⟨6,42,4,8⟩,
    ![418,1346,2646,4138,5618,6890,7787],![436,1392,2719,4223,5694,6940,7807]⟩,
    ⟨-947151522578197359914493,6289262264431451124081506816⟩,
    ⟨254330966142602662799408049,101573848166502236520946835456⟩⟩

def packet0954 : StripRowPacket :=
  ⟨⟨⟨6,43,4,8⟩,
    ![418,1345,2644,4135,5616,6889,7787],![436,1390,2716,4220,5692,6939,7807]⟩,
    ⟨-32791430217237039189991,222032354935461107852538880⟩,
    ⟨733992238743955555438817,289975701387924561042176000⟩⟩

def packet0955 : StripRowPacket :=
  ⟨⟨⟨6,42,4,9⟩,
    ![431,1384,2708,4210,5682,6931,7802],![447,1424,2774,4294,5764,6990,7827]⟩,
    ⟨115603379633865899166047395,50314098115451608992652054528⟩,
    ⟨251518175295526624412732813,50786924083251118260473417728⟩⟩

def packet0956 : StripRowPacket :=
  ⟨⟨⟨6,43,4,9⟩,
    ![431,1382,2705,4207,5680,6930,7802],![446,1422,2771,4291,5762,6989,7827]⟩,
    ⟨45451544703982628576319083,19538847234320577491023421440⟩,
    ⟨145144609400690130527113,28997570138792456104217600⟩⟩

def packet0957 : StripRowPacket :=
  ⟨⟨⟨6,40,5,20⟩,
    ![443,1419,2768,4286,5756,6982,7822],![453,1442,2805,4334,5805,7021,7840]⟩,
    ⟨30507655972670410247347,6580195969063262211311360⟩,
    ⟨151195816065755682967693,25016469507308912959406080⟩⟩

def packet0958 : StripRowPacket :=
  ⟨⟨⟨6,40,5,21⟩,
    ![448,1433,2793,4320,5791,7010,7834],![457,1454,2829,4367,5842,7051,7854]⟩,
    ⟨153568258002083122960279,26320783876253048845245440⟩,
    ⟨90587117449326193645203,12508234753654456479703040⟩⟩

def packet0959 : StripRowPacket :=
  ⟨⟨⟨6,41,5,20⟩,
    ![443,1417,2765,4283,5754,6981,7822],![452,1439,2802,4331,5803,7020,7839]⟩,
    ⟨3791833535974182209481953,808276136661399388563582976⟩,
    ⟨548509139267407150540250599,89765492167043568922399907840⟩⟩

def packets039 : List StripRowPacket :=
  [packet0936, packet0937, packet0938, packet0939, packet0940, packet0941,
   packet0942, packet0943, packet0944, packet0945, packet0946, packet0947,
   packet0948, packet0949, packet0950, packet0951, packet0952, packet0953,
   packet0954, packet0955, packet0956, packet0957, packet0958, packet0959]

theorem packet0936_membership : packet0936 ∈ packets039 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0936_shape : checkStripShape packet0936.row = true := by
  decide +kernel

private theorem packet0936_cache : checkStripCache packet0936 = true := by
  decide +kernel

private theorem packet0936_pair (i : Fin 7) : checkEdgePair packet0936 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0936_ok : checkStripPacket packet0936 = true :=
  checkStripPacket_intro packet0936_shape packet0936_cache packet0936_pair

theorem packet0937_membership : packet0937 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0937_shape : checkStripShape packet0937.row = true := by
  decide +kernel

private theorem packet0937_cache : checkStripCache packet0937 = true := by
  decide +kernel

private theorem packet0937_pair (i : Fin 7) : checkEdgePair packet0937 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0937_ok : checkStripPacket packet0937 = true :=
  checkStripPacket_intro packet0937_shape packet0937_cache packet0937_pair

theorem packet0938_membership : packet0938 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0938_shape : checkStripShape packet0938.row = true := by
  decide +kernel

private theorem packet0938_cache : checkStripCache packet0938 = true := by
  decide +kernel

private theorem packet0938_pair (i : Fin 7) : checkEdgePair packet0938 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0938_ok : checkStripPacket packet0938 = true :=
  checkStripPacket_intro packet0938_shape packet0938_cache packet0938_pair

theorem packet0939_membership : packet0939 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0939_shape : checkStripShape packet0939.row = true := by
  decide +kernel

private theorem packet0939_cache : checkStripCache packet0939 = true := by
  decide +kernel

private theorem packet0939_pair (i : Fin 7) : checkEdgePair packet0939 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0939_ok : checkStripPacket packet0939 = true :=
  checkStripPacket_intro packet0939_shape packet0939_cache packet0939_pair

theorem packet0940_membership : packet0940 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0940_shape : checkStripShape packet0940.row = true := by
  decide +kernel

private theorem packet0940_cache : checkStripCache packet0940 = true := by
  decide +kernel

private theorem packet0940_pair (i : Fin 7) : checkEdgePair packet0940 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0940_ok : checkStripPacket packet0940 = true :=
  checkStripPacket_intro packet0940_shape packet0940_cache packet0940_pair

theorem packet0941_membership : packet0941 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0941_shape : checkStripShape packet0941.row = true := by
  decide +kernel

private theorem packet0941_cache : checkStripCache packet0941 = true := by
  decide +kernel

private theorem packet0941_pair (i : Fin 7) : checkEdgePair packet0941 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0941_ok : checkStripPacket packet0941 = true :=
  checkStripPacket_intro packet0941_shape packet0941_cache packet0941_pair

theorem packet0942_membership : packet0942 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0942_shape : checkStripShape packet0942.row = true := by
  decide +kernel

private theorem packet0942_cache : checkStripCache packet0942 = true := by
  decide +kernel

private theorem packet0942_pair (i : Fin 7) : checkEdgePair packet0942 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0942_ok : checkStripPacket packet0942 = true :=
  checkStripPacket_intro packet0942_shape packet0942_cache packet0942_pair

theorem packet0943_membership : packet0943 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0943_shape : checkStripShape packet0943.row = true := by
  decide +kernel

private theorem packet0943_cache : checkStripCache packet0943 = true := by
  decide +kernel

private theorem packet0943_pair (i : Fin 7) : checkEdgePair packet0943 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0943_ok : checkStripPacket packet0943 = true :=
  checkStripPacket_intro packet0943_shape packet0943_cache packet0943_pair

theorem packet0944_membership : packet0944 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0944_shape : checkStripShape packet0944.row = true := by
  decide +kernel

private theorem packet0944_cache : checkStripCache packet0944 = true := by
  decide +kernel

private theorem packet0944_pair (i : Fin 7) : checkEdgePair packet0944 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0944_ok : checkStripPacket packet0944 = true :=
  checkStripPacket_intro packet0944_shape packet0944_cache packet0944_pair

theorem packet0945_membership : packet0945 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0945_shape : checkStripShape packet0945.row = true := by
  decide +kernel

private theorem packet0945_cache : checkStripCache packet0945 = true := by
  decide +kernel

private theorem packet0945_pair (i : Fin 7) : checkEdgePair packet0945 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0945_ok : checkStripPacket packet0945 = true :=
  checkStripPacket_intro packet0945_shape packet0945_cache packet0945_pair

theorem packet0946_membership : packet0946 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0946_shape : checkStripShape packet0946.row = true := by
  decide +kernel

private theorem packet0946_cache : checkStripCache packet0946 = true := by
  decide +kernel

private theorem packet0946_pair (i : Fin 7) : checkEdgePair packet0946 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0946_ok : checkStripPacket packet0946 = true :=
  checkStripPacket_intro packet0946_shape packet0946_cache packet0946_pair

theorem packet0947_membership : packet0947 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0947_shape : checkStripShape packet0947.row = true := by
  decide +kernel

private theorem packet0947_cache : checkStripCache packet0947 = true := by
  decide +kernel

private theorem packet0947_pair (i : Fin 7) : checkEdgePair packet0947 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0947_ok : checkStripPacket packet0947 = true :=
  checkStripPacket_intro packet0947_shape packet0947_cache packet0947_pair

theorem packet0948_membership : packet0948 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0948_shape : checkStripShape packet0948.row = true := by
  decide +kernel

private theorem packet0948_cache : checkStripCache packet0948 = true := by
  decide +kernel

private theorem packet0948_pair (i : Fin 7) : checkEdgePair packet0948 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0948_ok : checkStripPacket packet0948 = true :=
  checkStripPacket_intro packet0948_shape packet0948_cache packet0948_pair

theorem packet0949_membership : packet0949 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0949_shape : checkStripShape packet0949.row = true := by
  decide +kernel

private theorem packet0949_cache : checkStripCache packet0949 = true := by
  decide +kernel

private theorem packet0949_pair (i : Fin 7) : checkEdgePair packet0949 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0949_ok : checkStripPacket packet0949 = true :=
  checkStripPacket_intro packet0949_shape packet0949_cache packet0949_pair

theorem packet0950_membership : packet0950 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0950_shape : checkStripShape packet0950.row = true := by
  decide +kernel

private theorem packet0950_cache : checkStripCache packet0950 = true := by
  decide +kernel

private theorem packet0950_pair (i : Fin 7) : checkEdgePair packet0950 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0950_ok : checkStripPacket packet0950 = true :=
  checkStripPacket_intro packet0950_shape packet0950_cache packet0950_pair

theorem packet0951_membership : packet0951 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0951_shape : checkStripShape packet0951.row = true := by
  decide +kernel

private theorem packet0951_cache : checkStripCache packet0951 = true := by
  decide +kernel

private theorem packet0951_pair (i : Fin 7) : checkEdgePair packet0951 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0951_ok : checkStripPacket packet0951 = true :=
  checkStripPacket_intro packet0951_shape packet0951_cache packet0951_pair

theorem packet0952_membership : packet0952 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0952_shape : checkStripShape packet0952.row = true := by
  decide +kernel

private theorem packet0952_cache : checkStripCache packet0952 = true := by
  decide +kernel

private theorem packet0952_pair (i : Fin 7) : checkEdgePair packet0952 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0952_ok : checkStripPacket packet0952 = true :=
  checkStripPacket_intro packet0952_shape packet0952_cache packet0952_pair

theorem packet0953_membership : packet0953 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0953_shape : checkStripShape packet0953.row = true := by
  decide +kernel

private theorem packet0953_cache : checkStripCache packet0953 = true := by
  decide +kernel

private theorem packet0953_pair (i : Fin 7) : checkEdgePair packet0953 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0953_ok : checkStripPacket packet0953 = true :=
  checkStripPacket_intro packet0953_shape packet0953_cache packet0953_pair

theorem packet0954_membership : packet0954 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0954_shape : checkStripShape packet0954.row = true := by
  decide +kernel

private theorem packet0954_cache : checkStripCache packet0954 = true := by
  decide +kernel

private theorem packet0954_pair (i : Fin 7) : checkEdgePair packet0954 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0954_ok : checkStripPacket packet0954 = true :=
  checkStripPacket_intro packet0954_shape packet0954_cache packet0954_pair

theorem packet0955_membership : packet0955 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0955_shape : checkStripShape packet0955.row = true := by
  decide +kernel

private theorem packet0955_cache : checkStripCache packet0955 = true := by
  decide +kernel

private theorem packet0955_pair (i : Fin 7) : checkEdgePair packet0955 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0955_ok : checkStripPacket packet0955 = true :=
  checkStripPacket_intro packet0955_shape packet0955_cache packet0955_pair

theorem packet0956_membership : packet0956 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0956_shape : checkStripShape packet0956.row = true := by
  decide +kernel

private theorem packet0956_cache : checkStripCache packet0956 = true := by
  decide +kernel

private theorem packet0956_pair (i : Fin 7) : checkEdgePair packet0956 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0956_ok : checkStripPacket packet0956 = true :=
  checkStripPacket_intro packet0956_shape packet0956_cache packet0956_pair

theorem packet0957_membership : packet0957 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0957_shape : checkStripShape packet0957.row = true := by
  decide +kernel

private theorem packet0957_cache : checkStripCache packet0957 = true := by
  decide +kernel

private theorem packet0957_pair (i : Fin 7) : checkEdgePair packet0957 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0957_ok : checkStripPacket packet0957 = true :=
  checkStripPacket_intro packet0957_shape packet0957_cache packet0957_pair

theorem packet0958_membership : packet0958 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0958_shape : checkStripShape packet0958.row = true := by
  decide +kernel

private theorem packet0958_cache : checkStripCache packet0958 = true := by
  decide +kernel

private theorem packet0958_pair (i : Fin 7) : checkEdgePair packet0958 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0958_ok : checkStripPacket packet0958 = true :=
  checkStripPacket_intro packet0958_shape packet0958_cache packet0958_pair

theorem packet0959_membership : packet0959 ∈ packets039 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0959_shape : checkStripShape packet0959.row = true := by
  decide +kernel

private theorem packet0959_cache : checkStripCache packet0959 = true := by
  decide +kernel

private theorem packet0959_pair (i : Fin 7) : checkEdgePair packet0959 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0959_ok : checkStripPacket packet0959 = true :=
  checkStripPacket_intro packet0959_shape packet0959_cache packet0959_pair

theorem packets039_checked : packets039.all checkStripPacket = true := by
  simp only [packets039, List.all_cons, List.all_nil, Bool.true_and, packet0936_ok,
    packet0937_ok, packet0938_ok, packet0939_ok, packet0940_ok, packet0941_ok,
    packet0942_ok, packet0943_ok, packet0944_ok, packet0945_ok, packet0946_ok,
    packet0947_ok, packet0948_ok, packet0949_ok, packet0950_ok, packet0951_ok,
    packet0952_ok, packet0953_ok, packet0954_ok, packet0955_ok, packet0956_ok,
    packet0957_ok, packet0958_ok, packet0959_ok]

theorem packets039_valid : packets039.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
