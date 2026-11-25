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

def packet0744 : StripRowPacket :=
  ⟨⟨⟨5,9,4,15⟩,
    ![505,1587,3041,4635,6135,7329,8054],![520,1623,3097,4710,6225,7432,8192]⟩,
    ⟨3986189145046479335621,329803888774313199161344⟩,
    ⟨194332271,13502988928⟩⟩

def packet0745 : StripRowPacket :=
  ⟨⟨⟨6,20,4,8⟩,
    ![442,1403,2723,4212,5674,6921,7798],![463,1456,2803,4303,5753,6972,7818]⟩,
    ⟨-24351176841770163703,105025674251924227493120⟩,
    ⟨107671505185104187241791,58203219895069207870545920⟩⟩

def packet0746 : StripRowPacket :=
  ⟨⟨⟨6,21,4,8⟩,
    ![440,1399,2718,4208,5670,6919,7797],![461,1451,2798,4298,5750,6971,7817]⟩,
    ⟨-565666176075460211613,2494101169086687268766720⟩,
    ⟨46481508379739398627487583,24687167549825921816268369920⟩⟩

def packet0747 : StripRowPacket :=
  ⟨⟨⟨6,20,4,9⟩,
    ![456,1443,2785,4284,5736,6961,7812],![474,1489,2860,4374,5823,7021,7837]⟩,
    ⟨1341049910378428590669,840205394015393819944960⟩,
    ⟨21408861563122682081287,5820321989506920787054592⟩⟩

def packet0748 : StripRowPacket :=
  ⟨⟨⟨6,21,4,9⟩,
    ![454,1439,2781,4280,5733,6959,7811],![472,1485,2854,4369,5819,7020,7836]⟩,
    ⟨4658259067658489231813909,2853251737435170235469127680⟩,
    ⟨46197537610101270712037987,12343583774912960908134184960⟩⟩

def packet0749 : StripRowPacket :=
  ⟨⟨⟨5,11,4,8⟩,
    ![436,1389,2705,4195,5661,6914,7795],![460,1450,2797,4299,5751,6972,7818]⟩,
    ⟨-5141317257289210493,15027978741391585615360⟩,
    ⟨3754499350353940681,1828062295313275141120⟩⟩

def packet0750 : StripRowPacket :=
  ⟨⟨⟨6,22,4,9⟩,
    ![452,1435,2776,4275,5731,6958,7811],![470,1480,2849,4365,5816,7018,7836]⟩,
    ⟨2856683596549322908168175,1712165139414935090505478144⟩,
    ⟨6628665304685080280978579,1741585514224669444017516544⟩⟩

def packet0751 : StripRowPacket :=
  ⟨⟨⟨6,23,4,9⟩,
    ![451,1431,2771,4271,5728,6956,7810],![468,1476,2844,4360,5813,7016,7835]⟩,
    ⟨28928759483642506807167,16979989993946667216855040⟩,
    ⟨2231820916143678455,576880730165594493184⟩⟩

def packet0752 : StripRowPacket :=
  ⟨⟨⟨6,20,4,10⟩,
    ![468,1476,2842,4354,5804,7008,7830],![484,1518,2910,4442,5895,7079,7862]⟩,
    ⟨1438454617745509245481,420102697007696909972480⟩,
    ⟨320505726077349454383949,58203219895069207870545920⟩⟩

def packet0753 : StripRowPacket :=
  ⟨⟨⟨6,21,4,10⟩,
    ![466,1472,2837,4350,5801,7006,7829],![482,1513,2904,4437,5892,7077,7862]⟩,
    ⟨996364024074730494571309,285325173743517023546912768⟩,
    ⟨27661728412133136844132873,4937433509965184363253673984⟩⟩

def packet0754 : StripRowPacket :=
  ⟨⟨⟨6,20,4,11⟩,
    ![477,1505,2892,4422,5875,7063,7853],![492,1542,2954,4504,5968,7144,7896]⟩,
    ⟨882553712120721678251,168041078803078763988992⟩,
    ⟨106730709130868021988757,14550804973767301967636480⟩⟩

def packet0755 : StripRowPacket :=
  ⟨⟨⟨6,21,4,11⟩,
    ![475,1501,2887,4417,5872,7061,7853],![490,1537,2948,4499,5964,7142,7896]⟩,
    ⟨15269021413836120659612271,2853251737435170235469127680⟩,
    ⟨46055552225282206754313189,6171791887456480454067092480⟩⟩

def packet0756 : StripRowPacket :=
  ⟨⟨⟨6,22,4,10⟩,
    ![464,1468,2832,4346,5798,7005,7829],![480,1509,2899,4432,5888,7075,7861]⟩,
    ⟨3046712529761879793288691,856082569707467545252739072⟩,
    ⟨19843392963238433541136989,3483171028449338888035033088⟩⟩

def packet0757 : StripRowPacket :=
  ⟨⟨⟨6,23,4,10⟩,
    ![462,1464,2828,4342,5796,7003,7828],![478,1504,2894,4428,5885,7074,7861]⟩,
    ⟨30774090365607359156323,8489994996973333608427520⟩,
    ⟨367427936158983757003,63456880318215394250240⟩⟩

def packet0758 : StripRowPacket :=
  ⟨⟨⟨6,22,4,11⟩,
    ![473,1497,2883,4413,5869,7060,7853],![488,1533,2943,4495,5961,7141,7895]⟩,
    ⟨9330166522498196264986589,1712165139414935090505478144⟩,
    ⟨6607363829276676630079205,870792757112334722008758272⟩⟩

def packet0759 : StripRowPacket :=
  ⟨⟨⟨6,23,4,11⟩,
    ![472,1493,2878,4409,5867,7059,7852],![486,1528,2938,4490,5958,7139,7895]⟩,
    ⟨18833520395757385963625,3395997998789333443371008⟩,
    ⟨122338892885540720989,15864220079553848562560⟩⟩

def packet0760 : StripRowPacket :=
  ⟨⟨⟨5,10,4,12⟩,
    ![482,1523,2927,4474,5936,7117,7881],![499,1565,2997,4567,6045,7224,7949]⟩,
    ⟨10298619097893487,1467391842550572544⟩,
    ⟨362563033359517431785,38698265239003793133568⟩⟩

def packet0761 : StripRowPacket :=
  ⟨⟨⟨5,10,4,13⟩,
    ![489,1544,2966,4530,6006,7186,7922],![505,1583,3030,4617,6110,7298,8017]⟩,
    ⟨7438039511360905567,839348133938927495168⟩,
    ⟨2820543447681776019679,251538724053524655368192⟩⟩

def packet0762 : StripRowPacket :=
  ⟨⟨⟨5,11,4,12⟩,
    ![479,1515,2918,4466,5931,7115,7880],![495,1555,2985,4557,6038,7220,7948]⟩,
    ⟨218798503039232159817,30055957482783171230720⟩,
    ⟨17693223433750437197,1828062295313275141120⟩⟩

def packet0763 : StripRowPacket :=
  ⟨⟨⟨5,11,4,13⟩,
    ![486,1536,2957,4522,6001,7184,7922],![501,1573,3018,4607,6103,7294,8015]⟩,
    ⟨7722203844131043497,840726083434494300160⟩,
    ⟨1512707461042825809,130575878236662510080⟩⟩

def packet0764 : StripRowPacket :=
  ⟨⟨⟨5,10,4,14⟩,
    ![495,1562,3001,4581,6071,7257,7978],![510,1598,3059,4661,6168,7368,8109]⟩,
    ⟨4492634449363368285,419674066969463747584⟩,
    ⟨6568854357053377465511,503077448107049310736384⟩⟩

def packet0765 : StripRowPacket :=
  ⟨⟨⟨5,10,4,15⟩,
    ![500,1578,3031,4627,6130,7328,8055],![515,1612,3084,4699,6218,7428,8192]⟩,
    ⟨10532498286092567573,839348133938927495168⟩,
    ⟨5912163884251,396748881241856⟩⟩

def packet0766 : StripRowPacket :=
  ⟨⟨⟨5,11,4,14⟩,
    ![491,1554,2991,4573,6066,7256,7979],![506,1588,3047,4650,6161,7364,8107]⟩,
    ⟨666678143632274900437,60111914965566342461440⟩,
    ⟨4932517095089737091,365612459062655028224⟩⟩

def packet0767 : StripRowPacket :=
  ⟨⟨⟨5,11,4,15⟩,
    ![496,1569,3021,4618,6125,7326,8056],![510,1602,3073,4689,6211,7425,8192]⟩,
    ⟨1562437424818360381677,120223829931132684922880⟩,
    ⟨452818339,29408899520⟩⟩

def packets031 : List StripRowPacket :=
  [packet0744, packet0745, packet0746, packet0747, packet0748, packet0749,
   packet0750, packet0751, packet0752, packet0753, packet0754, packet0755,
   packet0756, packet0757, packet0758, packet0759, packet0760, packet0761,
   packet0762, packet0763, packet0764, packet0765, packet0766, packet0767]

theorem packet0744_membership : packet0744 ∈ packets031 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0744_shape : checkStripShape packet0744.row = true := by
  decide +kernel

private theorem packet0744_cache : checkStripCache packet0744 = true := by
  decide +kernel

private theorem packet0744_pair (i : Fin 7) : checkEdgePair packet0744 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0744_ok : checkStripPacket packet0744 = true :=
  checkStripPacket_intro packet0744_shape packet0744_cache packet0744_pair

theorem packet0745_membership : packet0745 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0745_shape : checkStripShape packet0745.row = true := by
  decide +kernel

private theorem packet0745_cache : checkStripCache packet0745 = true := by
  decide +kernel

private theorem packet0745_pair (i : Fin 7) : checkEdgePair packet0745 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0745_ok : checkStripPacket packet0745 = true :=
  checkStripPacket_intro packet0745_shape packet0745_cache packet0745_pair

theorem packet0746_membership : packet0746 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0746_shape : checkStripShape packet0746.row = true := by
  decide +kernel

private theorem packet0746_cache : checkStripCache packet0746 = true := by
  decide +kernel

private theorem packet0746_pair (i : Fin 7) : checkEdgePair packet0746 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0746_ok : checkStripPacket packet0746 = true :=
  checkStripPacket_intro packet0746_shape packet0746_cache packet0746_pair

theorem packet0747_membership : packet0747 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0747_shape : checkStripShape packet0747.row = true := by
  decide +kernel

private theorem packet0747_cache : checkStripCache packet0747 = true := by
  decide +kernel

private theorem packet0747_pair (i : Fin 7) : checkEdgePair packet0747 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0747_ok : checkStripPacket packet0747 = true :=
  checkStripPacket_intro packet0747_shape packet0747_cache packet0747_pair

theorem packet0748_membership : packet0748 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0748_shape : checkStripShape packet0748.row = true := by
  decide +kernel

private theorem packet0748_cache : checkStripCache packet0748 = true := by
  decide +kernel

private theorem packet0748_pair (i : Fin 7) : checkEdgePair packet0748 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0748_ok : checkStripPacket packet0748 = true :=
  checkStripPacket_intro packet0748_shape packet0748_cache packet0748_pair

theorem packet0749_membership : packet0749 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0749_shape : checkStripShape packet0749.row = true := by
  decide +kernel

private theorem packet0749_cache : checkStripCache packet0749 = true := by
  decide +kernel

private theorem packet0749_pair (i : Fin 7) : checkEdgePair packet0749 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0749_ok : checkStripPacket packet0749 = true :=
  checkStripPacket_intro packet0749_shape packet0749_cache packet0749_pair

theorem packet0750_membership : packet0750 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0750_shape : checkStripShape packet0750.row = true := by
  decide +kernel

private theorem packet0750_cache : checkStripCache packet0750 = true := by
  decide +kernel

private theorem packet0750_pair (i : Fin 7) : checkEdgePair packet0750 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0750_ok : checkStripPacket packet0750 = true :=
  checkStripPacket_intro packet0750_shape packet0750_cache packet0750_pair

theorem packet0751_membership : packet0751 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0751_shape : checkStripShape packet0751.row = true := by
  decide +kernel

private theorem packet0751_cache : checkStripCache packet0751 = true := by
  decide +kernel

private theorem packet0751_pair (i : Fin 7) : checkEdgePair packet0751 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0751_ok : checkStripPacket packet0751 = true :=
  checkStripPacket_intro packet0751_shape packet0751_cache packet0751_pair

theorem packet0752_membership : packet0752 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0752_shape : checkStripShape packet0752.row = true := by
  decide +kernel

private theorem packet0752_cache : checkStripCache packet0752 = true := by
  decide +kernel

private theorem packet0752_pair (i : Fin 7) : checkEdgePair packet0752 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0752_ok : checkStripPacket packet0752 = true :=
  checkStripPacket_intro packet0752_shape packet0752_cache packet0752_pair

theorem packet0753_membership : packet0753 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0753_shape : checkStripShape packet0753.row = true := by
  decide +kernel

private theorem packet0753_cache : checkStripCache packet0753 = true := by
  decide +kernel

private theorem packet0753_pair (i : Fin 7) : checkEdgePair packet0753 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0753_ok : checkStripPacket packet0753 = true :=
  checkStripPacket_intro packet0753_shape packet0753_cache packet0753_pair

theorem packet0754_membership : packet0754 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0754_shape : checkStripShape packet0754.row = true := by
  decide +kernel

private theorem packet0754_cache : checkStripCache packet0754 = true := by
  decide +kernel

private theorem packet0754_pair (i : Fin 7) : checkEdgePair packet0754 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0754_ok : checkStripPacket packet0754 = true :=
  checkStripPacket_intro packet0754_shape packet0754_cache packet0754_pair

theorem packet0755_membership : packet0755 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0755_shape : checkStripShape packet0755.row = true := by
  decide +kernel

private theorem packet0755_cache : checkStripCache packet0755 = true := by
  decide +kernel

private theorem packet0755_pair (i : Fin 7) : checkEdgePair packet0755 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0755_ok : checkStripPacket packet0755 = true :=
  checkStripPacket_intro packet0755_shape packet0755_cache packet0755_pair

theorem packet0756_membership : packet0756 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0756_shape : checkStripShape packet0756.row = true := by
  decide +kernel

private theorem packet0756_cache : checkStripCache packet0756 = true := by
  decide +kernel

private theorem packet0756_pair (i : Fin 7) : checkEdgePair packet0756 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0756_ok : checkStripPacket packet0756 = true :=
  checkStripPacket_intro packet0756_shape packet0756_cache packet0756_pair

theorem packet0757_membership : packet0757 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0757_shape : checkStripShape packet0757.row = true := by
  decide +kernel

private theorem packet0757_cache : checkStripCache packet0757 = true := by
  decide +kernel

private theorem packet0757_pair (i : Fin 7) : checkEdgePair packet0757 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0757_ok : checkStripPacket packet0757 = true :=
  checkStripPacket_intro packet0757_shape packet0757_cache packet0757_pair

theorem packet0758_membership : packet0758 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0758_shape : checkStripShape packet0758.row = true := by
  decide +kernel

private theorem packet0758_cache : checkStripCache packet0758 = true := by
  decide +kernel

private theorem packet0758_pair (i : Fin 7) : checkEdgePair packet0758 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0758_ok : checkStripPacket packet0758 = true :=
  checkStripPacket_intro packet0758_shape packet0758_cache packet0758_pair

theorem packet0759_membership : packet0759 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0759_shape : checkStripShape packet0759.row = true := by
  decide +kernel

private theorem packet0759_cache : checkStripCache packet0759 = true := by
  decide +kernel

private theorem packet0759_pair (i : Fin 7) : checkEdgePair packet0759 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0759_ok : checkStripPacket packet0759 = true :=
  checkStripPacket_intro packet0759_shape packet0759_cache packet0759_pair

theorem packet0760_membership : packet0760 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0760_shape : checkStripShape packet0760.row = true := by
  decide +kernel

private theorem packet0760_cache : checkStripCache packet0760 = true := by
  decide +kernel

private theorem packet0760_pair (i : Fin 7) : checkEdgePair packet0760 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0760_ok : checkStripPacket packet0760 = true :=
  checkStripPacket_intro packet0760_shape packet0760_cache packet0760_pair

theorem packet0761_membership : packet0761 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0761_shape : checkStripShape packet0761.row = true := by
  decide +kernel

private theorem packet0761_cache : checkStripCache packet0761 = true := by
  decide +kernel

private theorem packet0761_pair (i : Fin 7) : checkEdgePair packet0761 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0761_ok : checkStripPacket packet0761 = true :=
  checkStripPacket_intro packet0761_shape packet0761_cache packet0761_pair

theorem packet0762_membership : packet0762 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0762_shape : checkStripShape packet0762.row = true := by
  decide +kernel

private theorem packet0762_cache : checkStripCache packet0762 = true := by
  decide +kernel

private theorem packet0762_pair (i : Fin 7) : checkEdgePair packet0762 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0762_ok : checkStripPacket packet0762 = true :=
  checkStripPacket_intro packet0762_shape packet0762_cache packet0762_pair

theorem packet0763_membership : packet0763 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0763_shape : checkStripShape packet0763.row = true := by
  decide +kernel

private theorem packet0763_cache : checkStripCache packet0763 = true := by
  decide +kernel

private theorem packet0763_pair (i : Fin 7) : checkEdgePair packet0763 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0763_ok : checkStripPacket packet0763 = true :=
  checkStripPacket_intro packet0763_shape packet0763_cache packet0763_pair

theorem packet0764_membership : packet0764 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0764_shape : checkStripShape packet0764.row = true := by
  decide +kernel

private theorem packet0764_cache : checkStripCache packet0764 = true := by
  decide +kernel

private theorem packet0764_pair (i : Fin 7) : checkEdgePair packet0764 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0764_ok : checkStripPacket packet0764 = true :=
  checkStripPacket_intro packet0764_shape packet0764_cache packet0764_pair

theorem packet0765_membership : packet0765 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0765_shape : checkStripShape packet0765.row = true := by
  decide +kernel

private theorem packet0765_cache : checkStripCache packet0765 = true := by
  decide +kernel

private theorem packet0765_pair (i : Fin 7) : checkEdgePair packet0765 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0765_ok : checkStripPacket packet0765 = true :=
  checkStripPacket_intro packet0765_shape packet0765_cache packet0765_pair

theorem packet0766_membership : packet0766 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0766_shape : checkStripShape packet0766.row = true := by
  decide +kernel

private theorem packet0766_cache : checkStripCache packet0766 = true := by
  decide +kernel

private theorem packet0766_pair (i : Fin 7) : checkEdgePair packet0766 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0766_ok : checkStripPacket packet0766 = true :=
  checkStripPacket_intro packet0766_shape packet0766_cache packet0766_pair

theorem packet0767_membership : packet0767 ∈ packets031 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0767_shape : checkStripShape packet0767.row = true := by
  decide +kernel

private theorem packet0767_cache : checkStripCache packet0767 = true := by
  decide +kernel

private theorem packet0767_pair (i : Fin 7) : checkEdgePair packet0767 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0767_ok : checkStripPacket packet0767 = true :=
  checkStripPacket_intro packet0767_shape packet0767_cache packet0767_pair

theorem packets031_checked : packets031.all checkStripPacket = true := by
  simp only [packets031, List.all_cons, List.all_nil, Bool.true_and, packet0744_ok,
    packet0745_ok, packet0746_ok, packet0747_ok, packet0748_ok, packet0749_ok,
    packet0750_ok, packet0751_ok, packet0752_ok, packet0753_ok, packet0754_ok,
    packet0755_ok, packet0756_ok, packet0757_ok, packet0758_ok, packet0759_ok,
    packet0760_ok, packet0761_ok, packet0762_ok, packet0763_ok, packet0764_ok,
    packet0765_ok, packet0766_ok, packet0767_ok]

theorem packets031_valid : packets031.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
