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

def packet0624 : StripRowPacket :=
  ⟨⟨⟨6,8,4,9⟩,
    ![496,1518,2866,4349,5779,6982,7818],![523,1578,2954,4452,5874,7048,7845]⟩,
    ⟨3659101674385681107,3430821849901467507200⟩,
    ⟨15993667849046961763,5708141316918234681344⟩⟩

def packet0625 : StripRowPacket :=
  ⟨⟨⟨6,9,4,8⟩,
    ![475,1467,2794,4272,5714,6942,7804],![503,1531,2885,4372,5800,6997,7825]⟩,
    ⟨-11917493573111473637877,37420814910543297162941440⟩,
    ⟨13187658241186784807139,9125913341966013847654400⟩⟩

def packet0626 : StripRowPacket :=
  ⟨⟨⟨6,9,4,9⟩,
    ![491,1509,2857,4343,5775,6980,7818],![516,1567,2943,4443,5869,7045,7844]⟩,
    ⟨335761286945892917159747,299366519284346377303531520⟩,
    ⟨13168961085392422583831,4562956670983006923827200⟩⟩

def packet0627 : StripRowPacket :=
  ⟨⟨⟨6,8,4,10⟩,
    ![509,1554,2924,4420,5845,7027,7835],![534,1608,3005,4520,5946,7105,7870]⟩,
    ⟨384479494850790073,155946447722793977600⟩,
    ⟨239850489240733807681,57081413169182346813440⟩⟩

def packet0628 : StripRowPacket :=
  ⟨⟨⟨6,8,4,11⟩,
    ![520,1584,2976,4487,5914,7080,7857],![543,1633,3050,4583,6019,7170,7904]⟩,
    ⟨2651599219809816421,686164369980293501440⟩,
    ⟨79941074997749499433,14270353292295586703360⟩⟩

def packet0629 : StripRowPacket :=
  ⟨⟨⟨6,9,4,10⟩,
    ![504,1545,2915,4413,5841,7025,7835],![527,1597,2994,4511,5941,7102,7869]⟩,
    ⟨76686252247667762342251,29936651928434637730353152⟩,
    ⟨7897637220076581105637,1825182668393202769530880⟩⟩

def packet0630 : StripRowPacket :=
  ⟨⟨⟨6,9,4,11⟩,
    ![514,1575,2966,4480,5911,7078,7857],![536,1622,3039,4574,6013,7167,7903]⟩,
    ⟨1197963758007462329685273,299366519284346377303531520⟩,
    ⟨13159612507495241472177,2281478335491503461913600⟩⟩

def packet0631 : StripRowPacket :=
  ⟨⟨⟨6,10,4,8⟩,
    ![470,1459,2786,4265,5710,6940,7804],![497,1522,2875,4364,5794,6994,7825]⟩,
    ⟨-26057251204829404397,85063206120544675412480⟩,
    ⟨6648315216309720623514139,4471960371468889458688122880⟩⟩

def packet0632 : StripRowPacket :=
  ⟨⟨⟨6,10,4,9⟩,
    ![486,1501,2849,4336,5771,6978,7817],![510,1557,2933,4435,5864,7042,7843]⟩,
    ⟨8783975454940731278641,7485562138607931436298240⟩,
    ⟨1326954869849643347615363,447196037146888945868812288⟩⟩

def packet0633 : StripRowPacket :=
  ⟨⟨⟨6,11,4,8⟩,
    ![466,1452,2778,4259,5706,6938,7803],![492,1513,2866,4356,5790,6991,7824]⟩,
    ⟨-249473873361970184689,844026930073731246402560⟩,
    ⟨156337348540577029741,102387915240565380208640⟩⟩

def packet0634 : StripRowPacket :=
  ⟨⟨⟨6,11,4,9⟩,
    ![481,1493,2841,4330,5767,6976,7816],![504,1547,2924,4428,5859,7040,7843]⟩,
    ⟨1179456903921408099777,964602205798549995888640⟩,
    ⟨155935200306942271049,51193957620282690104320⟩⟩

def packet0635 : StripRowPacket :=
  ⟨⟨⟨6,10,4,10⟩,
    ![498,1536,2906,4407,5837,7024,7834],![520,1586,2984,4503,5936,7099,7868]⟩,
    ⟨9930494507953225072109,3742781069303965718149120⟩,
    ⟨19890782180683146328793121,4471960371468889458688122880⟩⟩

def packet0636 : StripRowPacket :=
  ⟨⟨⟨6,10,4,11⟩,
    ![509,1566,2958,4474,5907,7077,7857],![529,1612,3029,4566,6008,7164,7902]⟩,
    ⟨6187600515374433801959,1497112427721586287259648⟩,
    ⟨6628003915717464795358153,1117990092867222364672030720⟩⟩

def packet0637 : StripRowPacket :=
  ⟨⟨⟨6,11,4,10⟩,
    ![494,1528,2898,4400,5834,7022,7834],![515,1577,2975,4496,5931,7097,7868]⟩,
    ⟨1850818764179547487439,675221544058984997122048⟩,
    ⟨93480690537438410891,20477583048113076041728⟩⟩

def packet0638 : StripRowPacket :=
  ⟨⟨⟨6,11,4,11⟩,
    ![504,1558,2950,4468,5903,7075,7856],![523,1602,3020,4558,6003,7162,7901]⟩,
    ⟨2212321304318545619257,519401187737680767016960⟩,
    ⟨155734126190124891703,25596978810141345052160⟩⟩

def packet0639 : StripRowPacket :=
  ⟨⟨⟨6,8,4,12⟩,
    ![530,1611,3021,4550,5985,7140,7887],![551,1655,3090,4640,6089,7241,7951]⟩,
    ⟨4514360827845195651,857705462475366876800⟩,
    ⟨30744470057020168291,4390877936090949754880⟩⟩

def packet0640 : StripRowPacket :=
  ⟨⟨⟨6,8,4,13⟩,
    ![537,1633,3061,4607,6054,7208,7927],![557,1674,3124,4690,6154,7315,8016]⟩,
    ⟨22856890523712483103,3430821849901467507200⟩,
    ⟨239795960745763188917,28540706584591173406720⟩⟩

def packet0641 : StripRowPacket :=
  ⟨⟨⟨6,9,4,12⟩,
    ![523,1601,3012,4543,5981,7139,7887],![543,1644,3079,4631,6083,7239,7950]⟩,
    ⟨407266248384561758987009,74841629821086594325882880⟩,
    ⟨65788713959579026249231,9125913341966013847654400⟩⟩

def packet0642 : StripRowPacket :=
  ⟨⟨⟨6,9,4,13⟩,
    ![531,1623,3052,4600,6051,7207,7927],![550,1663,3113,4681,6148,7312,8015]⟩,
    ⟨158474325313002441708523,23028193791103567484887040⟩,
    ⟨5638498420655506186411,651850952997572417689600⟩⟩

def packet0643 : StripRowPacket :=
  ⟨⟨⟨6,8,3,7⟩,
    ![544,1652,3097,4659,6119,7279,7983],![568,1705,3180,4773,6262,7445,8192]⟩,
    ⟨13828168868022091801,1715410924950733753600⟩,
    ⟨10256952104803,915645021125120⟩⟩

def packet0644 : StripRowPacket :=
  ⟨⟨⟨6,9,3,7⟩,
    ![538,1642,3087,4652,6116,7278,7983],![560,1693,3169,4764,6257,7442,8192]⟩,
    ⟨1245633732299908224236781,149683259642173188651765760⟩,
    ⟨62437862213,5414340515584⟩⟩

def packet0645 : StripRowPacket :=
  ⟨⟨⟨6,10,4,12⟩,
    ![518,1592,3003,4537,5978,7138,7887],![537,1633,3068,4623,6078,7236,7949]⟩,
    ⟨10503754034459471968843,1871390534651982859074560⟩,
    ⟨33133249145056572034072103,4471960371468889458688122880⟩⟩

def packet0646 : StripRowPacket :=
  ⟨⟨⟨6,10,4,13⟩,
    ![525,1614,3043,4594,6047,7206,7928],![543,1652,3103,4673,6143,7309,8014]⟩,
    ⟨53092029698803606740949,7485562138607931436298240⟩,
    ⟨1807021937601967494850527,203270925975858611758551040⟩⟩

def packet0647 : StripRowPacket :=
  ⟨⟨⟨6,11,4,12⟩,
    ![513,1583,2995,4530,5974,7137,7887],![531,1624,3059,4615,6073,7233,7948]⟩,
    ⟨9753041567621677806573,1688053860147462492805120⟩,
    ⟨778469556833807079169,102387915240565380208640⟩⟩

def packets026 : List StripRowPacket :=
  [packet0624, packet0625, packet0626, packet0627, packet0628, packet0629,
   packet0630, packet0631, packet0632, packet0633, packet0634, packet0635,
   packet0636, packet0637, packet0638, packet0639, packet0640, packet0641,
   packet0642, packet0643, packet0644, packet0645, packet0646, packet0647]

theorem packet0624_membership : packet0624 ∈ packets026 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0624_shape : checkStripShape packet0624.row = true := by
  decide +kernel

private theorem packet0624_cache : checkStripCache packet0624 = true := by
  decide +kernel

private theorem packet0624_pair (i : Fin 7) : checkEdgePair packet0624 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0624_ok : checkStripPacket packet0624 = true :=
  checkStripPacket_intro packet0624_shape packet0624_cache packet0624_pair

theorem packet0625_membership : packet0625 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0625_shape : checkStripShape packet0625.row = true := by
  decide +kernel

private theorem packet0625_cache : checkStripCache packet0625 = true := by
  decide +kernel

private theorem packet0625_pair (i : Fin 7) : checkEdgePair packet0625 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0625_ok : checkStripPacket packet0625 = true :=
  checkStripPacket_intro packet0625_shape packet0625_cache packet0625_pair

theorem packet0626_membership : packet0626 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0626_shape : checkStripShape packet0626.row = true := by
  decide +kernel

private theorem packet0626_cache : checkStripCache packet0626 = true := by
  decide +kernel

private theorem packet0626_pair (i : Fin 7) : checkEdgePair packet0626 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0626_ok : checkStripPacket packet0626 = true :=
  checkStripPacket_intro packet0626_shape packet0626_cache packet0626_pair

theorem packet0627_membership : packet0627 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0627_shape : checkStripShape packet0627.row = true := by
  decide +kernel

private theorem packet0627_cache : checkStripCache packet0627 = true := by
  decide +kernel

private theorem packet0627_pair (i : Fin 7) : checkEdgePair packet0627 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0627_ok : checkStripPacket packet0627 = true :=
  checkStripPacket_intro packet0627_shape packet0627_cache packet0627_pair

theorem packet0628_membership : packet0628 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0628_shape : checkStripShape packet0628.row = true := by
  decide +kernel

private theorem packet0628_cache : checkStripCache packet0628 = true := by
  decide +kernel

private theorem packet0628_pair (i : Fin 7) : checkEdgePair packet0628 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0628_ok : checkStripPacket packet0628 = true :=
  checkStripPacket_intro packet0628_shape packet0628_cache packet0628_pair

theorem packet0629_membership : packet0629 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0629_shape : checkStripShape packet0629.row = true := by
  decide +kernel

private theorem packet0629_cache : checkStripCache packet0629 = true := by
  decide +kernel

private theorem packet0629_pair (i : Fin 7) : checkEdgePair packet0629 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0629_ok : checkStripPacket packet0629 = true :=
  checkStripPacket_intro packet0629_shape packet0629_cache packet0629_pair

theorem packet0630_membership : packet0630 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0630_shape : checkStripShape packet0630.row = true := by
  decide +kernel

private theorem packet0630_cache : checkStripCache packet0630 = true := by
  decide +kernel

private theorem packet0630_pair (i : Fin 7) : checkEdgePair packet0630 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0630_ok : checkStripPacket packet0630 = true :=
  checkStripPacket_intro packet0630_shape packet0630_cache packet0630_pair

theorem packet0631_membership : packet0631 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0631_shape : checkStripShape packet0631.row = true := by
  decide +kernel

private theorem packet0631_cache : checkStripCache packet0631 = true := by
  decide +kernel

private theorem packet0631_pair (i : Fin 7) : checkEdgePair packet0631 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0631_ok : checkStripPacket packet0631 = true :=
  checkStripPacket_intro packet0631_shape packet0631_cache packet0631_pair

theorem packet0632_membership : packet0632 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0632_shape : checkStripShape packet0632.row = true := by
  decide +kernel

private theorem packet0632_cache : checkStripCache packet0632 = true := by
  decide +kernel

private theorem packet0632_pair (i : Fin 7) : checkEdgePair packet0632 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0632_ok : checkStripPacket packet0632 = true :=
  checkStripPacket_intro packet0632_shape packet0632_cache packet0632_pair

theorem packet0633_membership : packet0633 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0633_shape : checkStripShape packet0633.row = true := by
  decide +kernel

private theorem packet0633_cache : checkStripCache packet0633 = true := by
  decide +kernel

private theorem packet0633_pair (i : Fin 7) : checkEdgePair packet0633 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0633_ok : checkStripPacket packet0633 = true :=
  checkStripPacket_intro packet0633_shape packet0633_cache packet0633_pair

theorem packet0634_membership : packet0634 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0634_shape : checkStripShape packet0634.row = true := by
  decide +kernel

private theorem packet0634_cache : checkStripCache packet0634 = true := by
  decide +kernel

private theorem packet0634_pair (i : Fin 7) : checkEdgePair packet0634 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0634_ok : checkStripPacket packet0634 = true :=
  checkStripPacket_intro packet0634_shape packet0634_cache packet0634_pair

theorem packet0635_membership : packet0635 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0635_shape : checkStripShape packet0635.row = true := by
  decide +kernel

private theorem packet0635_cache : checkStripCache packet0635 = true := by
  decide +kernel

private theorem packet0635_pair (i : Fin 7) : checkEdgePair packet0635 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0635_ok : checkStripPacket packet0635 = true :=
  checkStripPacket_intro packet0635_shape packet0635_cache packet0635_pair

theorem packet0636_membership : packet0636 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0636_shape : checkStripShape packet0636.row = true := by
  decide +kernel

private theorem packet0636_cache : checkStripCache packet0636 = true := by
  decide +kernel

private theorem packet0636_pair (i : Fin 7) : checkEdgePair packet0636 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0636_ok : checkStripPacket packet0636 = true :=
  checkStripPacket_intro packet0636_shape packet0636_cache packet0636_pair

theorem packet0637_membership : packet0637 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0637_shape : checkStripShape packet0637.row = true := by
  decide +kernel

private theorem packet0637_cache : checkStripCache packet0637 = true := by
  decide +kernel

private theorem packet0637_pair (i : Fin 7) : checkEdgePair packet0637 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0637_ok : checkStripPacket packet0637 = true :=
  checkStripPacket_intro packet0637_shape packet0637_cache packet0637_pair

theorem packet0638_membership : packet0638 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0638_shape : checkStripShape packet0638.row = true := by
  decide +kernel

private theorem packet0638_cache : checkStripCache packet0638 = true := by
  decide +kernel

private theorem packet0638_pair (i : Fin 7) : checkEdgePair packet0638 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0638_ok : checkStripPacket packet0638 = true :=
  checkStripPacket_intro packet0638_shape packet0638_cache packet0638_pair

theorem packet0639_membership : packet0639 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0639_shape : checkStripShape packet0639.row = true := by
  decide +kernel

private theorem packet0639_cache : checkStripCache packet0639 = true := by
  decide +kernel

private theorem packet0639_pair (i : Fin 7) : checkEdgePair packet0639 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0639_ok : checkStripPacket packet0639 = true :=
  checkStripPacket_intro packet0639_shape packet0639_cache packet0639_pair

theorem packet0640_membership : packet0640 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0640_shape : checkStripShape packet0640.row = true := by
  decide +kernel

private theorem packet0640_cache : checkStripCache packet0640 = true := by
  decide +kernel

private theorem packet0640_pair (i : Fin 7) : checkEdgePair packet0640 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0640_ok : checkStripPacket packet0640 = true :=
  checkStripPacket_intro packet0640_shape packet0640_cache packet0640_pair

theorem packet0641_membership : packet0641 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0641_shape : checkStripShape packet0641.row = true := by
  decide +kernel

private theorem packet0641_cache : checkStripCache packet0641 = true := by
  decide +kernel

private theorem packet0641_pair (i : Fin 7) : checkEdgePair packet0641 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0641_ok : checkStripPacket packet0641 = true :=
  checkStripPacket_intro packet0641_shape packet0641_cache packet0641_pair

theorem packet0642_membership : packet0642 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0642_shape : checkStripShape packet0642.row = true := by
  decide +kernel

private theorem packet0642_cache : checkStripCache packet0642 = true := by
  decide +kernel

private theorem packet0642_pair (i : Fin 7) : checkEdgePair packet0642 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0642_ok : checkStripPacket packet0642 = true :=
  checkStripPacket_intro packet0642_shape packet0642_cache packet0642_pair

theorem packet0643_membership : packet0643 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0643_shape : checkStripShape packet0643.row = true := by
  decide +kernel

private theorem packet0643_cache : checkStripCache packet0643 = true := by
  decide +kernel

private theorem packet0643_pair (i : Fin 7) : checkEdgePair packet0643 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0643_ok : checkStripPacket packet0643 = true :=
  checkStripPacket_intro packet0643_shape packet0643_cache packet0643_pair

theorem packet0644_membership : packet0644 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0644_shape : checkStripShape packet0644.row = true := by
  decide +kernel

private theorem packet0644_cache : checkStripCache packet0644 = true := by
  decide +kernel

private theorem packet0644_pair (i : Fin 7) : checkEdgePair packet0644 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0644_ok : checkStripPacket packet0644 = true :=
  checkStripPacket_intro packet0644_shape packet0644_cache packet0644_pair

theorem packet0645_membership : packet0645 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0645_shape : checkStripShape packet0645.row = true := by
  decide +kernel

private theorem packet0645_cache : checkStripCache packet0645 = true := by
  decide +kernel

private theorem packet0645_pair (i : Fin 7) : checkEdgePair packet0645 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0645_ok : checkStripPacket packet0645 = true :=
  checkStripPacket_intro packet0645_shape packet0645_cache packet0645_pair

theorem packet0646_membership : packet0646 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0646_shape : checkStripShape packet0646.row = true := by
  decide +kernel

private theorem packet0646_cache : checkStripCache packet0646 = true := by
  decide +kernel

private theorem packet0646_pair (i : Fin 7) : checkEdgePair packet0646 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0646_ok : checkStripPacket packet0646 = true :=
  checkStripPacket_intro packet0646_shape packet0646_cache packet0646_pair

theorem packet0647_membership : packet0647 ∈ packets026 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0647_shape : checkStripShape packet0647.row = true := by
  decide +kernel

private theorem packet0647_cache : checkStripCache packet0647 = true := by
  decide +kernel

private theorem packet0647_pair (i : Fin 7) : checkEdgePair packet0647 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0647_ok : checkStripPacket packet0647 = true :=
  checkStripPacket_intro packet0647_shape packet0647_cache packet0647_pair

theorem packets026_checked : packets026.all checkStripPacket = true := by
  simp only [packets026, List.all_cons, List.all_nil, Bool.true_and, packet0624_ok,
    packet0625_ok, packet0626_ok, packet0627_ok, packet0628_ok, packet0629_ok,
    packet0630_ok, packet0631_ok, packet0632_ok, packet0633_ok, packet0634_ok,
    packet0635_ok, packet0636_ok, packet0637_ok, packet0638_ok, packet0639_ok,
    packet0640_ok, packet0641_ok, packet0642_ok, packet0643_ok, packet0644_ok,
    packet0645_ok, packet0646_ok, packet0647_ok]

theorem packets026_valid : packets026.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
