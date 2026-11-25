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

def packet0768 : StripRowPacket :=
  ⟨⟨⟨5,12,4,0⟩,
    ![0,863,2173,3749,5351,6748,7742],![142,953,2242,3799,5385,6767,7750]⟩,
    ⟨-6648421916629,414030090554080⟩,
    ⟨-36802427184437928091,2702266978021346897920⟩⟩

def packet0769 : StripRowPacket :=
  ⟨⟨⟨5,12,4,1⟩,
    ![92,925,2223,3785,5374,6759,7746],![228,1025,2300,3841,5411,6780,7754]⟩,
    ⟨-17141365907779115113,1216400532603540444160⟩,
    ⟨-3721305842733841561,319358824675250087936⟩⟩

def packet0770 : StripRowPacket :=
  ⟨⟨⟨5,13,4,0⟩,
    ![0,858,2165,3740,5344,6744,7741],![141,947,2233,3789,5377,6763,7749]⟩,
    ⟨-3642983039,220525422832⟩,
    ⟨-21946822660698139015793,1564043000747685585999872⟩⟩

def packet0771 : StripRowPacket :=
  ⟨⟨⟨5,13,4,1⟩,
    ![93,920,2215,3777,5367,6756,7744],![226,1019,2291,3832,5404,6776,7753]⟩,
    ⟨-12956676072779060856067,893900928846041652490240⟩,
    ⟨-6706614153196026058883,558586785981316280714240⟩⟩

def packet0772 : StripRowPacket :=
  ⟨⟨⟨5,12,4,2⟩,
    ![192,996,2280,3826,5400,6773,7750],![292,1100,2364,3890,5442,6796,7759]⟩,
    ⟨-7374993674377113209,608200266301770222080⟩,
    ⟨-340255732003752078237,35129470714277509672960⟩⟩

def packet0773 : StripRowPacket :=
  ⟨⟨⟨5,12,4,3⟩,
    ![267,1073,2344,3873,5430,6788,7754],![339,1173,2434,3944,5478,6814,7765]⟩,
    ⟨-1765515541389905389,173771504657648634880⟩,
    ⟨-67791955326695396191,8782367678569377418240⟩⟩

def packet0774 : StripRowPacket :=
  ⟨⟨⟨5,13,4,2⟩,
    ![192,991,2272,3818,5393,6769,7748],![290,1094,2356,3881,5436,6792,7758]⟩,
    ⟨-5573250886438285885827,446950464423020826245120⟩,
    ⟨-78051082985998034569759,7820215003738427929999360⟩⟩

def packet0775 : StripRowPacket :=
  ⟨⟨⟨5,13,4,3⟩,
    ![266,1068,2336,3865,5423,6784,7753],![337,1167,2425,3936,5471,6811,7763]⟩,
    ⟨-9336327472974082687241,893900928846041652490240⟩,
    ⟨-15552391956812926078789,1955053750934606982499840⟩⟩

def packet0776 : StripRowPacket :=
  ⟨⟨⟨5,14,4,0⟩,
    ![0,854,2157,3732,5337,6740,7739],![139,942,2224,3781,5371,6759,7747]⟩,
    ⟨-9385205253471,552981488721376⟩,
    ⟨-18223364945535282225961,1262351085864926039437312⟩⟩

def packet0777 : StripRowPacket :=
  ⟨⟨⟨5,14,4,1⟩,
    ![94,916,2207,3768,5361,6752,7743],![224,1014,2283,3824,5398,6773,7752]⟩,
    ⟨-155513275385296919210869,10444733930090198714939392⟩,
    ⟨-708783859113055324059,57379594812042092701696⟩⟩

def packet0778 : StripRowPacket :=
  ⟨⟨⟨5,15,4,0⟩,
    ![0,850,2150,3724,5331,6737,7738],![138,937,2217,3772,5364,6755,7746]⟩,
    ⟨-20564,1180751⟩,
    ⟨-205633704568886413,13864351885222339072⟩⟩

def packet0779 : StripRowPacket :=
  ⟨⟨⟨5,15,4,1⟩,
    ![95,912,2200,3761,5354,6748,7742],![223,1009,2275,3815,5391,6769,7750]⟩,
    ⟨-150186485015664043,9831213193849655296⟩,
    ⟨-87980771511373957,6932175942611169536⟩⟩

def packet0780 : StripRowPacket :=
  ⟨⟨⟨5,14,4,2⟩,
    ![192,987,2264,3810,5387,6765,7747],![288,1089,2348,3872,5429,6788,7757]⟩,
    ⟨-66879230890924629788053,5222366965045099357469696⟩,
    ⟨-12963124855439152032635,1262351085864926039437312⟩⟩

def packet0781 : StripRowPacket :=
  ⟨⟨⟨5,14,4,3⟩,
    ![265,1064,2328,3857,5417,6781,7752],![335,1161,2417,3927,5465,6807,7762]⟩,
    ⟨-10182149834400145449213,949521266371836246812672⟩,
    ⟨-2583251202597771733993,315587771466231509859328⟩⟩

def packet0782 : StripRowPacket :=
  ⟨⟨⟨5,15,4,2⟩,
    ![192,983,2257,3802,5381,6762,7746],![287,1084,2340,3864,5423,6785,7755]⟩,
    ⟨-710337227243720281,54071672566173104128⟩,
    ⟨-13299034679691765,1260395625929303552⟩⟩

def packet0783 : StripRowPacket :=
  ⟨⟨⟨5,15,4,3⟩,
    ![265,1060,2321,3850,5411,6777,7751],![334,1157,2410,3919,5459,6803,7761]⟩,
    ⟨-1189297573802576651,108143345132346208256⟩,
    ⟨-29154304982617729,3466087971305584768⟩⟩

def packet0784 : StripRowPacket :=
  ⟨⟨⟨5,12,4,4⟩,
    ![322,1149,2414,3926,5464,6805,7760],![375,1240,2508,4005,5519,6836,7771]⟩,
    ⟨-2491807557676112257,304100133150885111040⟩,
    ⟨-202079910609811091291,35129470714277509672960⟩⟩

def packet0785 : StripRowPacket :=
  ⟨⟨⟨5,12,4,5⟩,
    ![363,1221,2485,3984,5503,6826,7766],![403,1303,2583,4072,5566,6861,7780]⟩,
    ⟨-7575851671679560333,1216400532603540444160⟩,
    ⟨-66495999956420298909,17564735357138754836480⟩⟩

def packet0786 : StripRowPacket :=
  ⟨⟨⟨5,13,4,4⟩,
    ![321,1144,2406,3918,5458,6802,7759],![373,1234,2499,3997,5512,6832,7770]⟩,
    ⟨-13157610442432855949,1562763861618953937920⟩,
    ⟨-3566773282192721081581,601555000287571379230720⟩⟩

def packet0787 : StripRowPacket :=
  ⟨⟨⟨5,13,4,5⟩,
    ![361,1216,2478,3976,5497,6822,7765],![401,1296,2574,4063,5559,6857,7778]⟩,
    ⟨-1143195774633820903683,178780185769208330498048⟩,
    ⟨-3052653750975904380595,782021500373842792999936⟩⟩

def packet0788 : StripRowPacket :=
  ⟨⟨⟨5,12,4,6⟩,
    ![393,1283,2558,4048,5548,6849,7774],![425,1357,2656,4143,5619,6891,7789]⟩,
    ⟨-235657868757030529,55290933300160929280⟩,
    ⟨-12780817843174020869,7025894142855501934592⟩⟩

def packet0789 : StripRowPacket :=
  ⟨⟨⟨5,12,4,7⟩,
    ![415,1337,2629,4116,5598,6877,7783],![443,1403,2724,4216,5679,6926,7801]⟩,
    ⟨-2793094553629782943,1216400532603540444160⟩,
    ⟨647977685137548641,4391183839284688709120⟩⟩

def packet0790 : StripRowPacket :=
  ⟨⟨⟨5,13,4,6⟩,
    ![391,1277,2550,4040,5542,6846,7773],![422,1350,2647,4134,5613,6887,7788]⟩,
    ⟨-1952902286633307717001,446950464423020826245120⟩,
    ⟨-14685022351012713551347,7820215003738427929999360⟩⟩

def packet0791 : StripRowPacket :=
  ⟨⟨⟨5,13,4,7⟩,
    ![413,1331,2621,4109,5593,6874,7782],![440,1396,2715,4207,5673,6923,7800]⟩,
    ⟨-2095630273364126349589,893900928846041652490240⟩,
    ⟨144561600966702087907,977526875467303491249920⟩⟩

def packets032 : List StripRowPacket :=
  [packet0768, packet0769, packet0770, packet0771, packet0772, packet0773,
   packet0774, packet0775, packet0776, packet0777, packet0778, packet0779,
   packet0780, packet0781, packet0782, packet0783, packet0784, packet0785,
   packet0786, packet0787, packet0788, packet0789, packet0790, packet0791]

theorem packet0768_membership : packet0768 ∈ packets032 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0768_shape : checkStripShape packet0768.row = true := by
  decide +kernel

private theorem packet0768_cache : checkStripCache packet0768 = true := by
  decide +kernel

private theorem packet0768_pair (i : Fin 7) : checkEdgePair packet0768 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0768_ok : checkStripPacket packet0768 = true :=
  checkStripPacket_intro packet0768_shape packet0768_cache packet0768_pair

theorem packet0769_membership : packet0769 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0769_shape : checkStripShape packet0769.row = true := by
  decide +kernel

private theorem packet0769_cache : checkStripCache packet0769 = true := by
  decide +kernel

private theorem packet0769_pair (i : Fin 7) : checkEdgePair packet0769 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0769_ok : checkStripPacket packet0769 = true :=
  checkStripPacket_intro packet0769_shape packet0769_cache packet0769_pair

theorem packet0770_membership : packet0770 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0770_shape : checkStripShape packet0770.row = true := by
  decide +kernel

private theorem packet0770_cache : checkStripCache packet0770 = true := by
  decide +kernel

private theorem packet0770_pair (i : Fin 7) : checkEdgePair packet0770 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0770_ok : checkStripPacket packet0770 = true :=
  checkStripPacket_intro packet0770_shape packet0770_cache packet0770_pair

theorem packet0771_membership : packet0771 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0771_shape : checkStripShape packet0771.row = true := by
  decide +kernel

private theorem packet0771_cache : checkStripCache packet0771 = true := by
  decide +kernel

private theorem packet0771_pair (i : Fin 7) : checkEdgePair packet0771 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0771_ok : checkStripPacket packet0771 = true :=
  checkStripPacket_intro packet0771_shape packet0771_cache packet0771_pair

theorem packet0772_membership : packet0772 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0772_shape : checkStripShape packet0772.row = true := by
  decide +kernel

private theorem packet0772_cache : checkStripCache packet0772 = true := by
  decide +kernel

private theorem packet0772_pair (i : Fin 7) : checkEdgePair packet0772 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0772_ok : checkStripPacket packet0772 = true :=
  checkStripPacket_intro packet0772_shape packet0772_cache packet0772_pair

theorem packet0773_membership : packet0773 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0773_shape : checkStripShape packet0773.row = true := by
  decide +kernel

private theorem packet0773_cache : checkStripCache packet0773 = true := by
  decide +kernel

private theorem packet0773_pair (i : Fin 7) : checkEdgePair packet0773 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0773_ok : checkStripPacket packet0773 = true :=
  checkStripPacket_intro packet0773_shape packet0773_cache packet0773_pair

theorem packet0774_membership : packet0774 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0774_shape : checkStripShape packet0774.row = true := by
  decide +kernel

private theorem packet0774_cache : checkStripCache packet0774 = true := by
  decide +kernel

private theorem packet0774_pair (i : Fin 7) : checkEdgePair packet0774 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0774_ok : checkStripPacket packet0774 = true :=
  checkStripPacket_intro packet0774_shape packet0774_cache packet0774_pair

theorem packet0775_membership : packet0775 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0775_shape : checkStripShape packet0775.row = true := by
  decide +kernel

private theorem packet0775_cache : checkStripCache packet0775 = true := by
  decide +kernel

private theorem packet0775_pair (i : Fin 7) : checkEdgePair packet0775 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0775_ok : checkStripPacket packet0775 = true :=
  checkStripPacket_intro packet0775_shape packet0775_cache packet0775_pair

theorem packet0776_membership : packet0776 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0776_shape : checkStripShape packet0776.row = true := by
  decide +kernel

private theorem packet0776_cache : checkStripCache packet0776 = true := by
  decide +kernel

private theorem packet0776_pair (i : Fin 7) : checkEdgePair packet0776 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0776_ok : checkStripPacket packet0776 = true :=
  checkStripPacket_intro packet0776_shape packet0776_cache packet0776_pair

theorem packet0777_membership : packet0777 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0777_shape : checkStripShape packet0777.row = true := by
  decide +kernel

private theorem packet0777_cache : checkStripCache packet0777 = true := by
  decide +kernel

private theorem packet0777_pair (i : Fin 7) : checkEdgePair packet0777 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0777_ok : checkStripPacket packet0777 = true :=
  checkStripPacket_intro packet0777_shape packet0777_cache packet0777_pair

theorem packet0778_membership : packet0778 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0778_shape : checkStripShape packet0778.row = true := by
  decide +kernel

private theorem packet0778_cache : checkStripCache packet0778 = true := by
  decide +kernel

private theorem packet0778_pair (i : Fin 7) : checkEdgePair packet0778 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0778_ok : checkStripPacket packet0778 = true :=
  checkStripPacket_intro packet0778_shape packet0778_cache packet0778_pair

theorem packet0779_membership : packet0779 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0779_shape : checkStripShape packet0779.row = true := by
  decide +kernel

private theorem packet0779_cache : checkStripCache packet0779 = true := by
  decide +kernel

private theorem packet0779_pair (i : Fin 7) : checkEdgePair packet0779 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0779_ok : checkStripPacket packet0779 = true :=
  checkStripPacket_intro packet0779_shape packet0779_cache packet0779_pair

theorem packet0780_membership : packet0780 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0780_shape : checkStripShape packet0780.row = true := by
  decide +kernel

private theorem packet0780_cache : checkStripCache packet0780 = true := by
  decide +kernel

private theorem packet0780_pair (i : Fin 7) : checkEdgePair packet0780 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0780_ok : checkStripPacket packet0780 = true :=
  checkStripPacket_intro packet0780_shape packet0780_cache packet0780_pair

theorem packet0781_membership : packet0781 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0781_shape : checkStripShape packet0781.row = true := by
  decide +kernel

private theorem packet0781_cache : checkStripCache packet0781 = true := by
  decide +kernel

private theorem packet0781_pair (i : Fin 7) : checkEdgePair packet0781 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0781_ok : checkStripPacket packet0781 = true :=
  checkStripPacket_intro packet0781_shape packet0781_cache packet0781_pair

theorem packet0782_membership : packet0782 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0782_shape : checkStripShape packet0782.row = true := by
  decide +kernel

private theorem packet0782_cache : checkStripCache packet0782 = true := by
  decide +kernel

private theorem packet0782_pair (i : Fin 7) : checkEdgePair packet0782 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0782_ok : checkStripPacket packet0782 = true :=
  checkStripPacket_intro packet0782_shape packet0782_cache packet0782_pair

theorem packet0783_membership : packet0783 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0783_shape : checkStripShape packet0783.row = true := by
  decide +kernel

private theorem packet0783_cache : checkStripCache packet0783 = true := by
  decide +kernel

private theorem packet0783_pair (i : Fin 7) : checkEdgePair packet0783 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0783_ok : checkStripPacket packet0783 = true :=
  checkStripPacket_intro packet0783_shape packet0783_cache packet0783_pair

theorem packet0784_membership : packet0784 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0784_shape : checkStripShape packet0784.row = true := by
  decide +kernel

private theorem packet0784_cache : checkStripCache packet0784 = true := by
  decide +kernel

private theorem packet0784_pair (i : Fin 7) : checkEdgePair packet0784 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0784_ok : checkStripPacket packet0784 = true :=
  checkStripPacket_intro packet0784_shape packet0784_cache packet0784_pair

theorem packet0785_membership : packet0785 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0785_shape : checkStripShape packet0785.row = true := by
  decide +kernel

private theorem packet0785_cache : checkStripCache packet0785 = true := by
  decide +kernel

private theorem packet0785_pair (i : Fin 7) : checkEdgePair packet0785 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0785_ok : checkStripPacket packet0785 = true :=
  checkStripPacket_intro packet0785_shape packet0785_cache packet0785_pair

theorem packet0786_membership : packet0786 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0786_shape : checkStripShape packet0786.row = true := by
  decide +kernel

private theorem packet0786_cache : checkStripCache packet0786 = true := by
  decide +kernel

private theorem packet0786_pair (i : Fin 7) : checkEdgePair packet0786 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0786_ok : checkStripPacket packet0786 = true :=
  checkStripPacket_intro packet0786_shape packet0786_cache packet0786_pair

theorem packet0787_membership : packet0787 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0787_shape : checkStripShape packet0787.row = true := by
  decide +kernel

private theorem packet0787_cache : checkStripCache packet0787 = true := by
  decide +kernel

private theorem packet0787_pair (i : Fin 7) : checkEdgePair packet0787 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0787_ok : checkStripPacket packet0787 = true :=
  checkStripPacket_intro packet0787_shape packet0787_cache packet0787_pair

theorem packet0788_membership : packet0788 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0788_shape : checkStripShape packet0788.row = true := by
  decide +kernel

private theorem packet0788_cache : checkStripCache packet0788 = true := by
  decide +kernel

private theorem packet0788_pair (i : Fin 7) : checkEdgePair packet0788 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0788_ok : checkStripPacket packet0788 = true :=
  checkStripPacket_intro packet0788_shape packet0788_cache packet0788_pair

theorem packet0789_membership : packet0789 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0789_shape : checkStripShape packet0789.row = true := by
  decide +kernel

private theorem packet0789_cache : checkStripCache packet0789 = true := by
  decide +kernel

private theorem packet0789_pair (i : Fin 7) : checkEdgePair packet0789 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0789_ok : checkStripPacket packet0789 = true :=
  checkStripPacket_intro packet0789_shape packet0789_cache packet0789_pair

theorem packet0790_membership : packet0790 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0790_shape : checkStripShape packet0790.row = true := by
  decide +kernel

private theorem packet0790_cache : checkStripCache packet0790 = true := by
  decide +kernel

private theorem packet0790_pair (i : Fin 7) : checkEdgePair packet0790 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0790_ok : checkStripPacket packet0790 = true :=
  checkStripPacket_intro packet0790_shape packet0790_cache packet0790_pair

theorem packet0791_membership : packet0791 ∈ packets032 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0791_shape : checkStripShape packet0791.row = true := by
  decide +kernel

private theorem packet0791_cache : checkStripCache packet0791 = true := by
  decide +kernel

private theorem packet0791_pair (i : Fin 7) : checkEdgePair packet0791 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0791_ok : checkStripPacket packet0791 = true :=
  checkStripPacket_intro packet0791_shape packet0791_cache packet0791_pair

theorem packets032_checked : packets032.all checkStripPacket = true := by
  simp only [packets032, List.all_cons, List.all_nil, Bool.true_and, packet0768_ok,
    packet0769_ok, packet0770_ok, packet0771_ok, packet0772_ok, packet0773_ok,
    packet0774_ok, packet0775_ok, packet0776_ok, packet0777_ok, packet0778_ok,
    packet0779_ok, packet0780_ok, packet0781_ok, packet0782_ok, packet0783_ok,
    packet0784_ok, packet0785_ok, packet0786_ok, packet0787_ok, packet0788_ok,
    packet0789_ok, packet0790_ok, packet0791_ok]

theorem packets032_valid : packets032.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
