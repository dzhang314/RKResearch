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

def packet0480 : StripRowPacket :=
  ⟨⟨⟨6,5,4,10⟩,
    ![533,1588,2955,4441,5857,7032,7836],![564,1650,3044,4550,5966,7115,7873]⟩,
    ⟨59635617761241180225761,27893493233692065779937280⟩,
    ⟨8585953716500556195113,2264185086386799425597440⟩⟩

def packet0481 : StripRowPacket :=
  ⟨⟨⟨6,5,4,11⟩,
    ![545,1619,3007,4509,5926,7084,7858],![574,1676,3090,4613,6039,7180,7907]⟩,
    ⟨3451276820077246716041,1014308844861529664724992⟩,
    ⟨37223979136846495381517,7358601530757098133191680⟩⟩

def packet0482 : StripRowPacket :=
  ⟨⟨⟨6,6,4,8⟩,
    ![493,1496,2822,4293,5728,6949,7806],![527,1568,2920,4399,5817,7006,7828]⟩,
    ⟨-30589728830359638061929,83162923162410146860879360⟩,
    ⟨107509999515252098553423,82104065746511235970949120⟩⟩

def packet0483 : StripRowPacket :=
  ⟨⟨⟨6,6,4,9⟩,
    ![510,1539,2886,4364,5788,6986,7819],![541,1604,2978,4471,5886,7054,7847]⟩,
    ⟨627858712974103829092679,665303385299281174887034880⟩,
    ⟨8281464842980920117119,3157848682558124460421120⟩⟩

def packet0484 : StripRowPacket :=
  ⟨⟨⟨6,7,4,8⟩,
    ![486,1486,2812,4286,5723,6947,7806],![518,1554,2907,4389,5811,7002,7827]⟩,
    ⟨-19465415218977443921,55841574648206185659392⟩,
    ⟨4943666221129614323,3643519241822302411712⟩⟩

def packet0485 : StripRowPacket :=
  ⟨⟨⟨6,7,4,9⟩,
    ![503,1528,2875,4356,5784,6984,7819],![531,1590,2966,4461,5880,7051,7846]⟩,
    ⟨450128898519946384295,446732597185649485275136⟩,
    ⟨9889558086220405597,3643519241822302411712⟩⟩

def packet0486 : StripRowPacket :=
  ⟨⟨⟨6,6,4,10⟩,
    ![524,1576,2944,4434,5853,7031,7836],![552,1634,3030,4539,5959,7111,7872]⟩,
    ⟨150043525659108476268079,66530338529928117488703488⟩,
    ⟨64625234463951149507353,16420813149302247194189824⟩⟩

def packet0487 : StripRowPacket :=
  ⟨⟨⟨6,6,4,11⟩,
    ![535,1607,2996,4501,5922,7083,7858],![562,1660,3076,4602,6031,7176,7906]⟩,
    ⟨182539369246774284328377,51177183484560090375925760⟩,
    ⟨107733564680501893007109,20526016436627808992737280⟩⟩

def packet0488 : StripRowPacket :=
  ⟨⟨⟨6,7,4,10⟩,
    ![516,1564,2933,4427,5849,7029,7836],![542,1620,3017,4529,5952,7108,7871]⟩,
    ⟨527990559395856159979,223366298592824742637568⟩,
    ⟨14835449951311196871,3643519241822302411712⟩⟩

def packet0489 : StripRowPacket :=
  ⟨⟨⟨6,7,4,11⟩,
    ![527,1595,2985,4494,5918,7081,7858],![551,1646,3062,4592,6025,7173,7905]⟩,
    ⟨1661833339063478255621,446732597185649485275136⟩,
    ⟨19781341816401988145,3643519241822302411712⟩⟩

def packet0490 : StripRowPacket :=
  ⟨⟨⟨6,4,4,12⟩,
    ![566,1661,3066,4580,6000,7144,7886],![597,1717,3146,4683,6117,7257,7957]⟩,
    ⟨168318374108192067337,37920129504042221596160⟩,
    ⟨66613163617237710854321,10967134226914662202531840⟩⟩

def packet0491 : StripRowPacket :=
  ⟨⟨⟨6,4,4,13⟩,
    ![575,1684,3106,4638,6069,7210,7924],![604,1736,3181,4733,6182,7331,8024]⟩,
    ⟨857541681819539721247,151680518016168886384640⟩,
    ⟨39981488041232151529587,5483567113457331101265920⟩⟩

def packet0492 : StripRowPacket :=
  ⟨⟨⟨6,5,4,12⟩,
    ![555,1646,3053,4572,5996,7143,7886],![582,1699,3130,4670,6109,7252,7955]⟩,
    ⟨65092303671503694578247,13946746616846032889968640⟩,
    ⟨186174434780264732515667,29434406123028392532766720⟩⟩

def packet0493 : StripRowPacket :=
  ⟨⟨⟨6,5,4,13⟩,
    ![563,1669,3094,4629,6065,7210,7925],![589,1718,3164,4721,6174,7326,8021]⟩,
    ⟨330918204267780987243721,55786986467384131559874560⟩,
    ⟨111726476506571741752633,14717203061514196266383360⟩⟩

def packet0494 : StripRowPacket :=
  ⟨⟨⟨6,4,3,7⟩,
    ![582,1704,3142,4690,6134,7281,7978],![616,1768,3237,4817,6291,7460,8192]⟩,
    ⟨47354993963923235143,6894569000734949381120⟩,
    ⟨47355160679573,4869095620939264⟩⟩

def packet0495 : StripRowPacket :=
  ⟨⟨⟨6,5,3,7⟩,
    ![570,1689,3129,4681,6131,7281,7979],![600,1749,3221,4804,6282,7456,8192]⟩,
    ⟨200733596924773598087227,27893493233692065779937280⟩,
    ⟨470382997987,46459664725760⟩⟩

def packet0496 : StripRowPacket :=
  ⟨⟨⟨6,6,4,12⟩,
    ![545,1633,3042,4564,5993,7143,7887],![570,1682,3115,4659,6102,7248,7953]⟩,
    ⟨811397085956261657464253,166325846324820293721758720⟩,
    ⟨538742345124259396520107,82104065746511235970949120⟩⟩

def packet0497 : StripRowPacket :=
  ⟨⟨⟨6,6,4,13⟩,
    ![553,1656,3082,4622,6062,7210,7926],![576,1702,3150,4710,6166,7322,8019]⟩,
    ⟨4118164887442027563445123,665303385299281174887034880⟩,
    ⟨323275215763255610505889,41052032873255617985474560⟩⟩

def packet0498 : StripRowPacket :=
  ⟨⟨⟨6,7,4,12⟩,
    ![537,1621,3031,4557,5989,7142,7887],![559,1668,3102,4649,6095,7245,7952]⟩,
    ⟨566921389833811047821,111683149296412371318784⟩,
    ⟨24727233681492779419,3643519241822302411712⟩⟩

def packet0499 : StripRowPacket :=
  ⟨⟨⟨6,7,4,13⟩,
    ![545,1644,3071,4614,6058,7209,7927],![566,1687,3136,4699,6160,7318,8018]⟩,
    ⟨2873537779607010126947,446732597185649485275136⟩,
    ⟨29673125546583570693,3643519241822302411712⟩⟩

def packet0500 : StripRowPacket :=
  ⟨⟨⟨6,6,3,7⟩,
    ![560,1675,3118,4673,6127,7280,7981],![588,1733,3206,4793,6275,7452,8192]⟩,
    ⟨2495370715529504248516617,332651692649640587443517440⟩,
    ⟨75250016240303,7166053811158528⟩⟩

def packet0501 : StripRowPacket :=
  ⟨⟨⟨6,7,3,7⟩,
    ![551,1663,3107,4666,6123,7280,7982],![577,1718,3192,4783,6268,7448,8192]⟩,
    ⟨1739694999939388031305,223366298592824742637568⟩,
    ⟨44206537,4070965184⟩⟩

def packet0502 : StripRowPacket :=
  ⟨⟨⟨7,16,4,0⟩,
    ![0,954,2295,3860,5431,6791,7756],![141,1029,2352,3903,5459,6807,7763]⟩,
    ⟨-14490701562019121,1275329260506421120⟩,
    ⟨-726618237334418741993159,74079134528429212573614080⟩⟩

def packet0503 : StripRowPacket :=
  ⟨⟨⟨7,17,4,0⟩,
    ![0,949,2290,3856,5428,6790,7755],![140,1024,2347,3899,5456,6806,7762]⟩,
    ⟨-11110165314219,964110479675200⟩,
    ⟨-2031731751805331313809166397,204151903440189796176889323520⟩⟩

def packets020 : List StripRowPacket :=
  [packet0480, packet0481, packet0482, packet0483, packet0484, packet0485,
   packet0486, packet0487, packet0488, packet0489, packet0490, packet0491,
   packet0492, packet0493, packet0494, packet0495, packet0496, packet0497,
   packet0498, packet0499, packet0500, packet0501, packet0502, packet0503]

theorem packet0480_membership : packet0480 ∈ packets020 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0480_shape : checkStripShape packet0480.row = true := by
  decide +kernel

private theorem packet0480_cache : checkStripCache packet0480 = true := by
  decide +kernel

private theorem packet0480_pair (i : Fin 7) : checkEdgePair packet0480 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0480_ok : checkStripPacket packet0480 = true :=
  checkStripPacket_intro packet0480_shape packet0480_cache packet0480_pair

theorem packet0481_membership : packet0481 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0481_shape : checkStripShape packet0481.row = true := by
  decide +kernel

private theorem packet0481_cache : checkStripCache packet0481 = true := by
  decide +kernel

private theorem packet0481_pair (i : Fin 7) : checkEdgePair packet0481 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0481_ok : checkStripPacket packet0481 = true :=
  checkStripPacket_intro packet0481_shape packet0481_cache packet0481_pair

theorem packet0482_membership : packet0482 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0482_shape : checkStripShape packet0482.row = true := by
  decide +kernel

private theorem packet0482_cache : checkStripCache packet0482 = true := by
  decide +kernel

private theorem packet0482_pair (i : Fin 7) : checkEdgePair packet0482 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0482_ok : checkStripPacket packet0482 = true :=
  checkStripPacket_intro packet0482_shape packet0482_cache packet0482_pair

theorem packet0483_membership : packet0483 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0483_shape : checkStripShape packet0483.row = true := by
  decide +kernel

private theorem packet0483_cache : checkStripCache packet0483 = true := by
  decide +kernel

private theorem packet0483_pair (i : Fin 7) : checkEdgePair packet0483 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0483_ok : checkStripPacket packet0483 = true :=
  checkStripPacket_intro packet0483_shape packet0483_cache packet0483_pair

theorem packet0484_membership : packet0484 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0484_shape : checkStripShape packet0484.row = true := by
  decide +kernel

private theorem packet0484_cache : checkStripCache packet0484 = true := by
  decide +kernel

private theorem packet0484_pair (i : Fin 7) : checkEdgePair packet0484 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0484_ok : checkStripPacket packet0484 = true :=
  checkStripPacket_intro packet0484_shape packet0484_cache packet0484_pair

theorem packet0485_membership : packet0485 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0485_shape : checkStripShape packet0485.row = true := by
  decide +kernel

private theorem packet0485_cache : checkStripCache packet0485 = true := by
  decide +kernel

private theorem packet0485_pair (i : Fin 7) : checkEdgePair packet0485 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0485_ok : checkStripPacket packet0485 = true :=
  checkStripPacket_intro packet0485_shape packet0485_cache packet0485_pair

theorem packet0486_membership : packet0486 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0486_shape : checkStripShape packet0486.row = true := by
  decide +kernel

private theorem packet0486_cache : checkStripCache packet0486 = true := by
  decide +kernel

private theorem packet0486_pair (i : Fin 7) : checkEdgePair packet0486 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0486_ok : checkStripPacket packet0486 = true :=
  checkStripPacket_intro packet0486_shape packet0486_cache packet0486_pair

theorem packet0487_membership : packet0487 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0487_shape : checkStripShape packet0487.row = true := by
  decide +kernel

private theorem packet0487_cache : checkStripCache packet0487 = true := by
  decide +kernel

private theorem packet0487_pair (i : Fin 7) : checkEdgePair packet0487 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0487_ok : checkStripPacket packet0487 = true :=
  checkStripPacket_intro packet0487_shape packet0487_cache packet0487_pair

theorem packet0488_membership : packet0488 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0488_shape : checkStripShape packet0488.row = true := by
  decide +kernel

private theorem packet0488_cache : checkStripCache packet0488 = true := by
  decide +kernel

private theorem packet0488_pair (i : Fin 7) : checkEdgePair packet0488 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0488_ok : checkStripPacket packet0488 = true :=
  checkStripPacket_intro packet0488_shape packet0488_cache packet0488_pair

theorem packet0489_membership : packet0489 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0489_shape : checkStripShape packet0489.row = true := by
  decide +kernel

private theorem packet0489_cache : checkStripCache packet0489 = true := by
  decide +kernel

private theorem packet0489_pair (i : Fin 7) : checkEdgePair packet0489 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0489_ok : checkStripPacket packet0489 = true :=
  checkStripPacket_intro packet0489_shape packet0489_cache packet0489_pair

theorem packet0490_membership : packet0490 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0490_shape : checkStripShape packet0490.row = true := by
  decide +kernel

private theorem packet0490_cache : checkStripCache packet0490 = true := by
  decide +kernel

private theorem packet0490_pair (i : Fin 7) : checkEdgePair packet0490 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0490_ok : checkStripPacket packet0490 = true :=
  checkStripPacket_intro packet0490_shape packet0490_cache packet0490_pair

theorem packet0491_membership : packet0491 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0491_shape : checkStripShape packet0491.row = true := by
  decide +kernel

private theorem packet0491_cache : checkStripCache packet0491 = true := by
  decide +kernel

private theorem packet0491_pair (i : Fin 7) : checkEdgePair packet0491 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0491_ok : checkStripPacket packet0491 = true :=
  checkStripPacket_intro packet0491_shape packet0491_cache packet0491_pair

theorem packet0492_membership : packet0492 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0492_shape : checkStripShape packet0492.row = true := by
  decide +kernel

private theorem packet0492_cache : checkStripCache packet0492 = true := by
  decide +kernel

private theorem packet0492_pair (i : Fin 7) : checkEdgePair packet0492 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0492_ok : checkStripPacket packet0492 = true :=
  checkStripPacket_intro packet0492_shape packet0492_cache packet0492_pair

theorem packet0493_membership : packet0493 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0493_shape : checkStripShape packet0493.row = true := by
  decide +kernel

private theorem packet0493_cache : checkStripCache packet0493 = true := by
  decide +kernel

private theorem packet0493_pair (i : Fin 7) : checkEdgePair packet0493 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0493_ok : checkStripPacket packet0493 = true :=
  checkStripPacket_intro packet0493_shape packet0493_cache packet0493_pair

theorem packet0494_membership : packet0494 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0494_shape : checkStripShape packet0494.row = true := by
  decide +kernel

private theorem packet0494_cache : checkStripCache packet0494 = true := by
  decide +kernel

private theorem packet0494_pair (i : Fin 7) : checkEdgePair packet0494 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0494_ok : checkStripPacket packet0494 = true :=
  checkStripPacket_intro packet0494_shape packet0494_cache packet0494_pair

theorem packet0495_membership : packet0495 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0495_shape : checkStripShape packet0495.row = true := by
  decide +kernel

private theorem packet0495_cache : checkStripCache packet0495 = true := by
  decide +kernel

private theorem packet0495_pair (i : Fin 7) : checkEdgePair packet0495 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0495_ok : checkStripPacket packet0495 = true :=
  checkStripPacket_intro packet0495_shape packet0495_cache packet0495_pair

theorem packet0496_membership : packet0496 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0496_shape : checkStripShape packet0496.row = true := by
  decide +kernel

private theorem packet0496_cache : checkStripCache packet0496 = true := by
  decide +kernel

private theorem packet0496_pair (i : Fin 7) : checkEdgePair packet0496 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0496_ok : checkStripPacket packet0496 = true :=
  checkStripPacket_intro packet0496_shape packet0496_cache packet0496_pair

theorem packet0497_membership : packet0497 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0497_shape : checkStripShape packet0497.row = true := by
  decide +kernel

private theorem packet0497_cache : checkStripCache packet0497 = true := by
  decide +kernel

private theorem packet0497_pair (i : Fin 7) : checkEdgePair packet0497 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0497_ok : checkStripPacket packet0497 = true :=
  checkStripPacket_intro packet0497_shape packet0497_cache packet0497_pair

theorem packet0498_membership : packet0498 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0498_shape : checkStripShape packet0498.row = true := by
  decide +kernel

private theorem packet0498_cache : checkStripCache packet0498 = true := by
  decide +kernel

private theorem packet0498_pair (i : Fin 7) : checkEdgePair packet0498 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0498_ok : checkStripPacket packet0498 = true :=
  checkStripPacket_intro packet0498_shape packet0498_cache packet0498_pair

theorem packet0499_membership : packet0499 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0499_shape : checkStripShape packet0499.row = true := by
  decide +kernel

private theorem packet0499_cache : checkStripCache packet0499 = true := by
  decide +kernel

private theorem packet0499_pair (i : Fin 7) : checkEdgePair packet0499 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0499_ok : checkStripPacket packet0499 = true :=
  checkStripPacket_intro packet0499_shape packet0499_cache packet0499_pair

theorem packet0500_membership : packet0500 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0500_shape : checkStripShape packet0500.row = true := by
  decide +kernel

private theorem packet0500_cache : checkStripCache packet0500 = true := by
  decide +kernel

private theorem packet0500_pair (i : Fin 7) : checkEdgePair packet0500 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0500_ok : checkStripPacket packet0500 = true :=
  checkStripPacket_intro packet0500_shape packet0500_cache packet0500_pair

theorem packet0501_membership : packet0501 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0501_shape : checkStripShape packet0501.row = true := by
  decide +kernel

private theorem packet0501_cache : checkStripCache packet0501 = true := by
  decide +kernel

private theorem packet0501_pair (i : Fin 7) : checkEdgePair packet0501 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0501_ok : checkStripPacket packet0501 = true :=
  checkStripPacket_intro packet0501_shape packet0501_cache packet0501_pair

theorem packet0502_membership : packet0502 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0502_shape : checkStripShape packet0502.row = true := by
  decide +kernel

private theorem packet0502_cache : checkStripCache packet0502 = true := by
  decide +kernel

private theorem packet0502_pair (i : Fin 7) : checkEdgePair packet0502 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0502_ok : checkStripPacket packet0502 = true :=
  checkStripPacket_intro packet0502_shape packet0502_cache packet0502_pair

theorem packet0503_membership : packet0503 ∈ packets020 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0503_shape : checkStripShape packet0503.row = true := by
  decide +kernel

private theorem packet0503_cache : checkStripCache packet0503 = true := by
  decide +kernel

private theorem packet0503_pair (i : Fin 7) : checkEdgePair packet0503 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0503_ok : checkStripPacket packet0503 = true :=
  checkStripPacket_intro packet0503_shape packet0503_cache packet0503_pair

theorem packets020_checked : packets020.all checkStripPacket = true := by
  simp only [packets020, List.all_cons, List.all_nil, Bool.true_and, packet0480_ok,
    packet0481_ok, packet0482_ok, packet0483_ok, packet0484_ok, packet0485_ok,
    packet0486_ok, packet0487_ok, packet0488_ok, packet0489_ok, packet0490_ok,
    packet0491_ok, packet0492_ok, packet0493_ok, packet0494_ok, packet0495_ok,
    packet0496_ok, packet0497_ok, packet0498_ok, packet0499_ok, packet0500_ok,
    packet0501_ok, packet0502_ok, packet0503_ok]

theorem packets020_valid : packets020.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
