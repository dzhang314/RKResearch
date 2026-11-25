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

def packet0408 : StripRowPacket :=
  ⟨⟨⟨7,12,5,13⟩,
    ![465,1428,2728,4199,5655,6907,7792],![488,1472,2781,4249,5692,6929,7802]⟩,
    ⟨-7099140219411930917442967,3180938861048098053803401216⟩,
    ⟨-382967259003010070703023,273954409020882270203494400⟩⟩

def packet0409 : StripRowPacket :=
  ⟨⟨⟨7,13,5,12⟩,
    ![447,1392,2686,4162,5628,6893,7788],![471,1438,2739,4210,5663,6913,7796]⟩,
    ⟨-17493263121635222727045286169,5992049691976570729618125414400⟩,
    ⟨-25499341855498623547756296881,12265897301900464322897675141120⟩⟩

def packet0410 : StripRowPacket :=
  ⟨⟨⟨7,13,5,13⟩,
    ![461,1422,2722,4194,5652,6906,7792],![484,1466,2775,4244,5689,6928,7801]⟩,
    ⟨-4919319433642566335018435109,2178927160718752992588409241600⟩,
    ⟨-8689083931151024811216889651,6132948650950232161448837570560⟩⟩

def packet0411 : StripRowPacket :=
  ⟨⟨⟨7,12,4,7⟩,
    ![478,1456,2763,4233,5680,6921,7797],![509,1522,2851,4320,5749,6962,7813]⟩,
    ⟨-1143289032681744351925163,722940650238204103137136640⟩,
    ⟨-23122614203831705468783,239710107893271986428057600⟩⟩

def packet0412 : StripRowPacket :=
  ⟨⟨⟨7,13,4,7⟩,
    ![474,1450,2758,4228,5677,6920,7796],![505,1515,2845,4316,5746,6961,7812]⟩,
    ⟨-2732283932399683461587459123,1712014197707591637033750118400⟩,
    ⟨-70988742244306360736796509,766618581368779020181104696320⟩⟩

def packet0413 : StripRowPacket :=
  ⟨⟨⟨7,14,4,6⟩,
    ![444,1387,2681,4157,5625,6891,7787],![480,1459,2769,4240,5686,6926,7801]⟩,
    ⟨-10378986362295516634039984191,3510690809252023060557156184064⟩,
    ⟨-1212210967650377167956549151,844460826148343979933418897408⟩⟩

def packet0414 : StripRowPacket :=
  ⟨⟨⟨7,15,4,6⟩,
    ![441,1382,2676,4153,5623,6890,7787],![476,1454,2764,4235,5683,6925,7800]⟩,
    ⟨-5501556594390109150043,1838118171377863177527296⟩,
    ⟨-11599400598693696091609,7977556648541669420627968⟩⟩

def packet0415 : StripRowPacket :=
  ⟨⟨⟨6,7,4,7⟩,
    ![466,1436,2743,4216,5669,6915,7795],![501,1512,2843,4316,5747,6962,7813]⟩,
    ⟨-761575542023585487031,446732597185649485275136⟩,
    ⟨-2225643961176951,3643519241822302411712⟩⟩

def packet0416 : StripRowPacket :=
  ⟨⟨⟨7,0,5,16⟩,
    ![612,1620,2921,4362,5768,6968,7812],![660,1688,3001,4439,5830,7005,7827]⟩,
    ⟨-412720228273985,716539085915983616⟩,
    ⟨1424891830161689,6162856460281151488⟩⟩

def packet0417 : StripRowPacket :=
  ⟨⟨⟨7,0,5,17⟩,
    ![623,1645,2955,4397,5797,6985,7818],![670,1710,3034,4477,5862,7026,7834]⟩,
    ⟨-1180040585536463,11464625374655737856⟩,
    ⟨2180354810500305,3081428230140575744⟩⟩

def packet0418 : StripRowPacket :=
  ⟨⟨⟨7,1,5,16⟩,
    ![593,1606,2912,4357,5766,6967,7812],![634,1666,2985,4429,5824,7003,7826]⟩,
    ⟨-3951358145097843243055767,7671955115932519121352980480⟩,
    ⟨313861281077604188621714269,1111063842187012302449578065920⟩⟩

def packet0419 : StripRowPacket :=
  ⟨⟨⟨7,1,5,17⟩,
    ![604,1630,2945,4392,5794,6984,7818],![644,1689,3018,4466,5856,7023,7833]⟩,
    ⟨-41167611188466567012391,1888481259306466245256118272⟩,
    ⟨432326656823883090972568373,555531921093506151224789032960⟩⟩

def packet0420 : StripRowPacket :=
  ⟨⟨⟨7,0,5,18⟩,
    ![633,1668,2988,4432,5826,7003,7824],![678,1731,3066,4514,5897,7049,7842]⟩,
    ⟨2121721240655417,5732312687327868928⟩,
    ⟨7296527411839531,6162856460281151488⟩⟩

def packet0421 : StripRowPacket :=
  ⟨⟨⟨7,0,5,19⟩,
    ![642,1688,3019,4468,5858,7023,7831],![686,1750,3096,4551,5932,7074,7852]⟩,
    ⟨878811413468921,1042238670423248896⟩,
    ⟨2558086300669613,1540714115070287872⟩⟩

def packet0422 : StripRowPacket :=
  ⟨⟨⟨7,1,4,9⟩,
    ![613,1652,2978,4427,5824,7003,7824],![660,1728,3079,4539,5925,7071,7851]⟩,
    ⟨28934970433532419088640721,61375640927460152970823843840⟩,
    ⟨8937442630854955311781735,5050290191759146829316263936⟩⟩

def packet0423 : StripRowPacket :=
  ⟨⟨⟨7,2,5,16⟩,
    ![577,1592,2902,4351,5763,6966,7812],![614,1648,2971,4419,5818,7000,7825]⟩,
    ⟨-7938919006601679029412431,16949818275022959620878904320⟩,
    ⟨643843272927817733570983,1983662130672402031273410560⟩⟩

def packet0424 : StripRowPacket :=
  ⟨⟨⟨7,2,5,17⟩,
    ![588,1616,2936,4386,5792,6983,7817],![623,1670,3004,4456,5851,7021,7832]⟩,
    ⟨11743318663646455585893689,271197092400367353934062469120⟩,
    ⟨63949287848950961331691,76294697333553924279746560⟩⟩

def packet0425 : StripRowPacket :=
  ⟨⟨⟨7,3,4,8⟩,
    ![564,1580,2894,4346,5760,6965,7811],![606,1655,2991,4448,5846,7018,7832]⟩,
    ⟨-86020072967989525153901,199293700023347884833781760⟩,
    ⟨905594898118256746108857,1017029701309628485230202880⟩⟩

def packet0426 : StripRowPacket :=
  ⟨⟨⟨7,2,4,9⟩,
    ![597,1638,2968,4422,5822,7002,7824],![639,1709,3064,4529,5920,7068,7850]⟩,
    ⟨10750667245208555403027591,19371220885740525281004462080⟩,
    ⟨84099043326421352652953,45083230242554591619850240⟩⟩

def packet0427 : StripRowPacket :=
  ⟨⟨⟨7,3,4,9⟩,
    ![584,1626,2959,4416,5820,7001,7824],![622,1693,3051,4520,5914,7066,7850]⟩,
    ⟨997947735796884209754731,1594349600186783078670254080⟩,
    ⟨631364538020035685963401,323600359507609063482337280⟩⟩

def packet0428 : StripRowPacket :=
  ⟨⟨⟨7,0,5,20⟩,
    ![650,1708,3049,4503,5890,7045,7839],![693,1767,3124,4587,5969,7101,7863]⟩,
    ⟨3772602153751357,2866156343663934464⟩,
    ⟨13168162993517373,6162856460281151488⟩⟩

def packet0429 : StripRowPacket :=
  ⟨⟨⟨7,0,5,21⟩,
    ![658,1725,3077,4538,5924,7069,7849],![700,1783,3151,4622,6006,7131,7876]⟩,
    ⟨1577991667834825,881894259588902912⟩,
    ⟨8051990392178147,3081428230140575744⟩⟩

def packet0430 : StripRowPacket :=
  ⟨⟨⟨7,1,4,10⟩,
    ![630,1691,3038,4498,5889,7045,7840],![674,1761,3133,4610,5999,7127,7875]⟩,
    ⟨44740403013923792060863789,30687820463730076485411921920⟩,
    ⟨1533910721964207077619413327,555531921093506151224789032960⟩⟩

def packet0431 : StripRowPacket :=
  ⟨⟨⟨7,0,5,22⟩,
    ![664,1742,3104,4572,5958,7095,7859],![706,1798,3176,4656,6044,7163,7892]⟩,
    ⟨12968687374350011,5732312687327868928⟩,
    ⟨19039798575195215,6162856460281151488⟩⟩

def packets017 : List StripRowPacket :=
  [packet0408, packet0409, packet0410, packet0411, packet0412, packet0413,
   packet0414, packet0415, packet0416, packet0417, packet0418, packet0419,
   packet0420, packet0421, packet0422, packet0423, packet0424, packet0425,
   packet0426, packet0427, packet0428, packet0429, packet0430, packet0431]

theorem packet0408_membership : packet0408 ∈ packets017 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0408_shape : checkStripShape packet0408.row = true := by
  decide +kernel

private theorem packet0408_cache : checkStripCache packet0408 = true := by
  decide +kernel

private theorem packet0408_pair (i : Fin 7) : checkEdgePair packet0408 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0408_ok : checkStripPacket packet0408 = true :=
  checkStripPacket_intro packet0408_shape packet0408_cache packet0408_pair

theorem packet0409_membership : packet0409 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0409_shape : checkStripShape packet0409.row = true := by
  decide +kernel

private theorem packet0409_cache : checkStripCache packet0409 = true := by
  decide +kernel

private theorem packet0409_pair (i : Fin 7) : checkEdgePair packet0409 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0409_ok : checkStripPacket packet0409 = true :=
  checkStripPacket_intro packet0409_shape packet0409_cache packet0409_pair

theorem packet0410_membership : packet0410 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0410_shape : checkStripShape packet0410.row = true := by
  decide +kernel

private theorem packet0410_cache : checkStripCache packet0410 = true := by
  decide +kernel

private theorem packet0410_pair (i : Fin 7) : checkEdgePair packet0410 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0410_ok : checkStripPacket packet0410 = true :=
  checkStripPacket_intro packet0410_shape packet0410_cache packet0410_pair

theorem packet0411_membership : packet0411 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0411_shape : checkStripShape packet0411.row = true := by
  decide +kernel

private theorem packet0411_cache : checkStripCache packet0411 = true := by
  decide +kernel

private theorem packet0411_pair (i : Fin 7) : checkEdgePair packet0411 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0411_ok : checkStripPacket packet0411 = true :=
  checkStripPacket_intro packet0411_shape packet0411_cache packet0411_pair

theorem packet0412_membership : packet0412 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0412_shape : checkStripShape packet0412.row = true := by
  decide +kernel

private theorem packet0412_cache : checkStripCache packet0412 = true := by
  decide +kernel

private theorem packet0412_pair (i : Fin 7) : checkEdgePair packet0412 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0412_ok : checkStripPacket packet0412 = true :=
  checkStripPacket_intro packet0412_shape packet0412_cache packet0412_pair

theorem packet0413_membership : packet0413 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0413_shape : checkStripShape packet0413.row = true := by
  decide +kernel

private theorem packet0413_cache : checkStripCache packet0413 = true := by
  decide +kernel

private theorem packet0413_pair (i : Fin 7) : checkEdgePair packet0413 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0413_ok : checkStripPacket packet0413 = true :=
  checkStripPacket_intro packet0413_shape packet0413_cache packet0413_pair

theorem packet0414_membership : packet0414 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0414_shape : checkStripShape packet0414.row = true := by
  decide +kernel

private theorem packet0414_cache : checkStripCache packet0414 = true := by
  decide +kernel

private theorem packet0414_pair (i : Fin 7) : checkEdgePair packet0414 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0414_ok : checkStripPacket packet0414 = true :=
  checkStripPacket_intro packet0414_shape packet0414_cache packet0414_pair

theorem packet0415_membership : packet0415 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0415_shape : checkStripShape packet0415.row = true := by
  decide +kernel

private theorem packet0415_cache : checkStripCache packet0415 = true := by
  decide +kernel

private theorem packet0415_pair (i : Fin 7) : checkEdgePair packet0415 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0415_ok : checkStripPacket packet0415 = true :=
  checkStripPacket_intro packet0415_shape packet0415_cache packet0415_pair

theorem packet0416_membership : packet0416 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0416_shape : checkStripShape packet0416.row = true := by
  decide +kernel

private theorem packet0416_cache : checkStripCache packet0416 = true := by
  decide +kernel

private theorem packet0416_pair (i : Fin 7) : checkEdgePair packet0416 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0416_ok : checkStripPacket packet0416 = true :=
  checkStripPacket_intro packet0416_shape packet0416_cache packet0416_pair

theorem packet0417_membership : packet0417 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0417_shape : checkStripShape packet0417.row = true := by
  decide +kernel

private theorem packet0417_cache : checkStripCache packet0417 = true := by
  decide +kernel

private theorem packet0417_pair (i : Fin 7) : checkEdgePair packet0417 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0417_ok : checkStripPacket packet0417 = true :=
  checkStripPacket_intro packet0417_shape packet0417_cache packet0417_pair

theorem packet0418_membership : packet0418 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0418_shape : checkStripShape packet0418.row = true := by
  decide +kernel

private theorem packet0418_cache : checkStripCache packet0418 = true := by
  decide +kernel

private theorem packet0418_pair (i : Fin 7) : checkEdgePair packet0418 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0418_ok : checkStripPacket packet0418 = true :=
  checkStripPacket_intro packet0418_shape packet0418_cache packet0418_pair

theorem packet0419_membership : packet0419 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0419_shape : checkStripShape packet0419.row = true := by
  decide +kernel

private theorem packet0419_cache : checkStripCache packet0419 = true := by
  decide +kernel

private theorem packet0419_pair (i : Fin 7) : checkEdgePair packet0419 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0419_ok : checkStripPacket packet0419 = true :=
  checkStripPacket_intro packet0419_shape packet0419_cache packet0419_pair

theorem packet0420_membership : packet0420 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0420_shape : checkStripShape packet0420.row = true := by
  decide +kernel

private theorem packet0420_cache : checkStripCache packet0420 = true := by
  decide +kernel

private theorem packet0420_pair (i : Fin 7) : checkEdgePair packet0420 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0420_ok : checkStripPacket packet0420 = true :=
  checkStripPacket_intro packet0420_shape packet0420_cache packet0420_pair

theorem packet0421_membership : packet0421 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0421_shape : checkStripShape packet0421.row = true := by
  decide +kernel

private theorem packet0421_cache : checkStripCache packet0421 = true := by
  decide +kernel

private theorem packet0421_pair (i : Fin 7) : checkEdgePair packet0421 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0421_ok : checkStripPacket packet0421 = true :=
  checkStripPacket_intro packet0421_shape packet0421_cache packet0421_pair

theorem packet0422_membership : packet0422 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0422_shape : checkStripShape packet0422.row = true := by
  decide +kernel

private theorem packet0422_cache : checkStripCache packet0422 = true := by
  decide +kernel

private theorem packet0422_pair (i : Fin 7) : checkEdgePair packet0422 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0422_ok : checkStripPacket packet0422 = true :=
  checkStripPacket_intro packet0422_shape packet0422_cache packet0422_pair

theorem packet0423_membership : packet0423 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0423_shape : checkStripShape packet0423.row = true := by
  decide +kernel

private theorem packet0423_cache : checkStripCache packet0423 = true := by
  decide +kernel

private theorem packet0423_pair (i : Fin 7) : checkEdgePair packet0423 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0423_ok : checkStripPacket packet0423 = true :=
  checkStripPacket_intro packet0423_shape packet0423_cache packet0423_pair

theorem packet0424_membership : packet0424 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0424_shape : checkStripShape packet0424.row = true := by
  decide +kernel

private theorem packet0424_cache : checkStripCache packet0424 = true := by
  decide +kernel

private theorem packet0424_pair (i : Fin 7) : checkEdgePair packet0424 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0424_ok : checkStripPacket packet0424 = true :=
  checkStripPacket_intro packet0424_shape packet0424_cache packet0424_pair

theorem packet0425_membership : packet0425 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0425_shape : checkStripShape packet0425.row = true := by
  decide +kernel

private theorem packet0425_cache : checkStripCache packet0425 = true := by
  decide +kernel

private theorem packet0425_pair (i : Fin 7) : checkEdgePair packet0425 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0425_ok : checkStripPacket packet0425 = true :=
  checkStripPacket_intro packet0425_shape packet0425_cache packet0425_pair

theorem packet0426_membership : packet0426 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0426_shape : checkStripShape packet0426.row = true := by
  decide +kernel

private theorem packet0426_cache : checkStripCache packet0426 = true := by
  decide +kernel

private theorem packet0426_pair (i : Fin 7) : checkEdgePair packet0426 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0426_ok : checkStripPacket packet0426 = true :=
  checkStripPacket_intro packet0426_shape packet0426_cache packet0426_pair

theorem packet0427_membership : packet0427 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0427_shape : checkStripShape packet0427.row = true := by
  decide +kernel

private theorem packet0427_cache : checkStripCache packet0427 = true := by
  decide +kernel

private theorem packet0427_pair (i : Fin 7) : checkEdgePair packet0427 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0427_ok : checkStripPacket packet0427 = true :=
  checkStripPacket_intro packet0427_shape packet0427_cache packet0427_pair

theorem packet0428_membership : packet0428 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0428_shape : checkStripShape packet0428.row = true := by
  decide +kernel

private theorem packet0428_cache : checkStripCache packet0428 = true := by
  decide +kernel

private theorem packet0428_pair (i : Fin 7) : checkEdgePair packet0428 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0428_ok : checkStripPacket packet0428 = true :=
  checkStripPacket_intro packet0428_shape packet0428_cache packet0428_pair

theorem packet0429_membership : packet0429 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0429_shape : checkStripShape packet0429.row = true := by
  decide +kernel

private theorem packet0429_cache : checkStripCache packet0429 = true := by
  decide +kernel

private theorem packet0429_pair (i : Fin 7) : checkEdgePair packet0429 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0429_ok : checkStripPacket packet0429 = true :=
  checkStripPacket_intro packet0429_shape packet0429_cache packet0429_pair

theorem packet0430_membership : packet0430 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0430_shape : checkStripShape packet0430.row = true := by
  decide +kernel

private theorem packet0430_cache : checkStripCache packet0430 = true := by
  decide +kernel

private theorem packet0430_pair (i : Fin 7) : checkEdgePair packet0430 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0430_ok : checkStripPacket packet0430 = true :=
  checkStripPacket_intro packet0430_shape packet0430_cache packet0430_pair

theorem packet0431_membership : packet0431 ∈ packets017 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0431_shape : checkStripShape packet0431.row = true := by
  decide +kernel

private theorem packet0431_cache : checkStripCache packet0431 = true := by
  decide +kernel

private theorem packet0431_pair (i : Fin 7) : checkEdgePair packet0431 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0431_ok : checkStripPacket packet0431 = true :=
  checkStripPacket_intro packet0431_shape packet0431_cache packet0431_pair

theorem packets017_checked : packets017.all checkStripPacket = true := by
  simp only [packets017, List.all_cons, List.all_nil, Bool.true_and, packet0408_ok,
    packet0409_ok, packet0410_ok, packet0411_ok, packet0412_ok, packet0413_ok,
    packet0414_ok, packet0415_ok, packet0416_ok, packet0417_ok, packet0418_ok,
    packet0419_ok, packet0420_ok, packet0421_ok, packet0422_ok, packet0423_ok,
    packet0424_ok, packet0425_ok, packet0426_ok, packet0427_ok, packet0428_ok,
    packet0429_ok, packet0430_ok, packet0431_ok]

theorem packets017_valid : packets017.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
