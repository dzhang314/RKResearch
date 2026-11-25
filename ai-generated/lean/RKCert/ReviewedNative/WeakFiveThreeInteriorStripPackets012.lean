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

def packet0288 : StripRowPacket :=
  ⟨⟨⟨7,4,5,14⟩,
    ![528,1517,2816,4271,5704,6933,7801],![561,1571,2879,4331,5749,6960,7811]⟩,
    ⟨-750389948541966326661571,503083407422267883644612608⟩,
    ⟨-50164794718728861321487717,71536268064913828126814076928⟩⟩

def packet0289 : StripRowPacket :=
  ⟨⟨⟨7,4,5,15⟩,
    ![541,1544,2851,4305,5730,6948,7805],![572,1596,2914,4367,5778,6977,7817]⟩,
    ⟨-952618393626845846506891,1006166814844535767289225216⟩,
    ⟨-693887736848367362675083,4471016754057114257925879808⟩⟩

def packet0290 : StripRowPacket :=
  ⟨⟨⟨7,5,5,14⟩,
    ![519,1508,2808,4266,5701,6932,7800],![549,1559,2870,4324,5745,6958,7811]⟩,
    ⟨-314634202446716263451340713,210109459476978054498401042432⟩,
    ⟨-6928805726184604228178239,9842113034995312190044749824⟩⟩

def packet0291 : StripRowPacket :=
  ⟨⟨⟨7,5,5,15⟩,
    ![532,1534,2844,4300,5727,6946,7805],![560,1584,2904,4360,5774,6975,7817]⟩,
    ⟨-30305089677263724150999141,32324532227227392999754006528⟩,
    ⟨-87969011911950978667641,615132064687207011877796864⟩⟩

def packet0292 : StripRowPacket :=
  ⟨⟨⟨7,6,5,12⟩,
    ![482,1439,2729,4195,5650,6904,7791],![513,1492,2789,4247,5688,6926,7800]⟩,
    ⟨-2394118353105603040455445,901870474356383196487094272⟩,
    ⟨-1182980632590951028151719183,636471434711302648841175203840⟩⟩

def packet0293 : StripRowPacket :=
  ⟨⟨⟨7,6,5,13⟩,
    ![497,1470,2765,4227,5673,6916,7795],![527,1521,2825,4282,5713,6940,7805]⟩,
    ⟨-37522215946659299116433639,18037409487127663929741885440⟩,
    ⟨-408427797840204794594506957,318235717355651324420587601920⟩⟩

def packet0294 : StripRowPacket :=
  ⟨⟨⟨7,7,5,12⟩,
    ![475,1431,2722,4190,5647,6902,7791],![505,1483,2780,4241,5684,6924,7800]⟩,
    ⟨-24666330694883017015397,9161388304690266960240640⟩,
    ⟨-560301013966155653933,296267916574667719235840⟩⟩

def packet0295 : StripRowPacket :=
  ⟨⟨⟨7,7,5,13⟩,
    ![490,1462,2758,4222,5670,6915,7795],![519,1511,2817,4276,5710,6938,7804]⟩,
    ⟨-77111573402428172627211,36645553218761067840962560⟩,
    ⟨-19291259399904229741,14813395828733385961792⟩⟩

def packet0296 : StripRowPacket :=
  ⟨⟨⟨7,6,5,14⟩,
    ![511,1499,2801,4261,5698,6930,7800],![539,1548,2861,4317,5741,6956,7810]⟩,
    ⟨-1940147487943324101697027,1288386391937690280695848960⟩,
    ⟨-90146111753973630045261729,127294286942260529768235040768⟩⟩

def packet0297 : StripRowPacket :=
  ⟨⟨⟨7,6,5,15⟩,
    ![523,1525,2836,4295,5724,6945,7805],![550,1573,2895,4353,5770,6973,7816]⟩,
    ⟨-1292454901211828902391009,1387493037471358763826298880⟩,
    ⟨-5287845116207919453975211,39779464669456415552573450240⟩⟩

def packet0298 : StripRowPacket :=
  ⟨⟨⟨7,7,5,14⟩,
    ![504,1490,2794,4256,5694,6928,7799],![531,1538,2852,4311,5737,6954,7810]⟩,
    ⟨-27778912012662138596417,18322776609380533920481280⟩,
    ⟨-211349362030013535707,296267916574667719235840⟩⟩

def packet0299 : StripRowPacket :=
  ⟨⟨⟨7,7,5,15⟩,
    ![516,1517,2829,4290,5721,6943,7804],![541,1563,2887,4347,5766,6971,7815]⟩,
    ⟨-34004074648220381758457,36645553218761067840962560⟩,
    ⟨-18436768030971238297,148133958287333859617920⟩⟩

def packet0300 : StripRowPacket :=
  ⟨⟨⟨7,8,5,0⟩,
    ![0,1004,2348,3903,5460,6806,7761],![92,1047,2382,3929,5477,6817,7766]⟩,
    ⟨-7268519376326457,730675238898487168⟩,
    ⟨-23105104947908219688097023,2525599017844933548020039680⟩⟩

def packet0301 : StripRowPacket :=
  ⟨⟨⟨7,8,5,1⟩,
    ![47,1032,2370,3920,5470,6811,7762],![153,1079,2406,3947,5489,6822,7768]⟩,
    ⟨-1429177011315318715646663,152914603370312268818544640⟩,
    ⟨-2158450494295442671022131,252559901784493354802003968⟩⟩

def packet0302 : StripRowPacket :=
  ⟨⟨⟨7,9,5,0⟩,
    ![0,996,2340,3897,5456,6804,7760],![90,1039,2374,3923,5473,6815,7765]⟩,
    ⟨-3674397692989,362389190747584⟩,
    ⟨-58048696924325849863356792631,6219803507079325947419148271616⟩⟩

def packet0303 : StripRowPacket :=
  ⟨⟨⟨7,9,5,1⟩,
    ![48,1025,2363,3913,5466,6809,7762],![151,1071,2398,3941,5484,6820,7767]⟩,
    ⟨-615144903498183782152729285,64581193358155231788299616256⟩,
    ⟨-27112406831683068349104840439,3109901753539662973709574135808⟩⟩

def packet0304 : StripRowPacket :=
  ⟨⟨⟨7,8,5,2⟩,
    ![114,1064,2394,3937,5481,6817,7764],![207,1113,2433,3966,5501,6828,7770]⟩,
    ⟨-668604667851244263273983,76457301685156134409272320⟩,
    ⟨-20063904938000633732345597,2525599017844933548020039680⟩⟩

def packet0305 : StripRowPacket :=
  ⟨⟨⟨7,8,5,3⟩,
    ![174,1097,2420,3955,5493,6823,7766],![256,1149,2461,3986,5513,6835,7772]⟩,
    ⟨-1245241660089658337449269,152914603370312268818544640⟩,
    ⟨-4635826233261710188617471,631399754461233387005009920⟩⟩

def packet0306 : StripRowPacket :=
  ⟨⟨⟨7,9,5,2⟩,
    ![114,1056,2387,3931,5477,6815,7763],![205,1106,2425,3960,5496,6826,7769]⟩,
    ⟨-3165124946872266889795797367,355196563469853774835647889408⟩,
    ⟨-50400930402406423533062569125,6219803507079325947419148271616⟩⟩

def packet0307 : StripRowPacket :=
  ⟨⟨⟨7,9,5,3⟩,
    ![173,1090,2413,3950,5489,6821,7765],![253,1142,2453,3980,5509,6833,7771]⟩,
    ⟨-203238132724449860534591977,24496314722058881023148130304⟩,
    ⟨-895712445027821353229143411,119611605905371652834983620608⟩⟩

def packet0308 : StripRowPacket :=
  ⟨⟨⟨7,10,5,0⟩,
    ![0,989,2333,3891,5452,6802,7759],![89,1031,2366,3917,5469,6813,7765]⟩,
    ⟨-674531327863247,65323281244414336⟩,
    ⟨-2894883018250772066937493,304331909895515453250568192⟩⟩

def packet0309 : StripRowPacket :=
  ⟨⟨⟨7,10,5,1⟩,
    ![48,1018,2355,3908,5462,6807,7761],![149,1064,2391,3935,5481,6818,7766]⟩,
    ⟨-5393448923502927902179670355,556058221420562586219513823232⟩,
    ⟨-17576211456852111807226001,1978157414320850446128693248⟩⟩

def packet0310 : StripRowPacket :=
  ⟨⟨⟨7,11,5,0⟩,
    ![0,982,2326,3886,5448,6800,7759],![88,1025,2359,3911,5465,6811,7764]⟩,
    ⟨-34433198667,3276805257440⟩,
    ⟨-51396772216777593366723147,5305765289164364551204986880⟩⟩

def packet0311 : StripRowPacket :=
  ⟨⟨⟨7,11,5,1⟩,
    ![49,1011,2348,3902,5459,6806,7760],![147,1057,2384,3929,5477,6816,7766]⟩,
    ⟨-706142630216208680685713,71547792051065131889950720⟩,
    ⟨-24002979087801937703228267,2652882644582182275602493440⟩⟩

def packets012 : List StripRowPacket :=
  [packet0288, packet0289, packet0290, packet0291, packet0292, packet0293,
   packet0294, packet0295, packet0296, packet0297, packet0298, packet0299,
   packet0300, packet0301, packet0302, packet0303, packet0304, packet0305,
   packet0306, packet0307, packet0308, packet0309, packet0310, packet0311]

theorem packet0288_membership : packet0288 ∈ packets012 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0288_shape : checkStripShape packet0288.row = true := by
  decide +kernel

private theorem packet0288_cache : checkStripCache packet0288 = true := by
  decide +kernel

private theorem packet0288_pair (i : Fin 7) : checkEdgePair packet0288 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0288_ok : checkStripPacket packet0288 = true :=
  checkStripPacket_intro packet0288_shape packet0288_cache packet0288_pair

theorem packet0289_membership : packet0289 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0289_shape : checkStripShape packet0289.row = true := by
  decide +kernel

private theorem packet0289_cache : checkStripCache packet0289 = true := by
  decide +kernel

private theorem packet0289_pair (i : Fin 7) : checkEdgePair packet0289 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0289_ok : checkStripPacket packet0289 = true :=
  checkStripPacket_intro packet0289_shape packet0289_cache packet0289_pair

theorem packet0290_membership : packet0290 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0290_shape : checkStripShape packet0290.row = true := by
  decide +kernel

private theorem packet0290_cache : checkStripCache packet0290 = true := by
  decide +kernel

private theorem packet0290_pair (i : Fin 7) : checkEdgePair packet0290 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0290_ok : checkStripPacket packet0290 = true :=
  checkStripPacket_intro packet0290_shape packet0290_cache packet0290_pair

theorem packet0291_membership : packet0291 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0291_shape : checkStripShape packet0291.row = true := by
  decide +kernel

private theorem packet0291_cache : checkStripCache packet0291 = true := by
  decide +kernel

private theorem packet0291_pair (i : Fin 7) : checkEdgePair packet0291 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0291_ok : checkStripPacket packet0291 = true :=
  checkStripPacket_intro packet0291_shape packet0291_cache packet0291_pair

theorem packet0292_membership : packet0292 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0292_shape : checkStripShape packet0292.row = true := by
  decide +kernel

private theorem packet0292_cache : checkStripCache packet0292 = true := by
  decide +kernel

private theorem packet0292_pair (i : Fin 7) : checkEdgePair packet0292 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0292_ok : checkStripPacket packet0292 = true :=
  checkStripPacket_intro packet0292_shape packet0292_cache packet0292_pair

theorem packet0293_membership : packet0293 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0293_shape : checkStripShape packet0293.row = true := by
  decide +kernel

private theorem packet0293_cache : checkStripCache packet0293 = true := by
  decide +kernel

private theorem packet0293_pair (i : Fin 7) : checkEdgePair packet0293 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0293_ok : checkStripPacket packet0293 = true :=
  checkStripPacket_intro packet0293_shape packet0293_cache packet0293_pair

theorem packet0294_membership : packet0294 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0294_shape : checkStripShape packet0294.row = true := by
  decide +kernel

private theorem packet0294_cache : checkStripCache packet0294 = true := by
  decide +kernel

private theorem packet0294_pair (i : Fin 7) : checkEdgePair packet0294 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0294_ok : checkStripPacket packet0294 = true :=
  checkStripPacket_intro packet0294_shape packet0294_cache packet0294_pair

theorem packet0295_membership : packet0295 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0295_shape : checkStripShape packet0295.row = true := by
  decide +kernel

private theorem packet0295_cache : checkStripCache packet0295 = true := by
  decide +kernel

private theorem packet0295_pair (i : Fin 7) : checkEdgePair packet0295 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0295_ok : checkStripPacket packet0295 = true :=
  checkStripPacket_intro packet0295_shape packet0295_cache packet0295_pair

theorem packet0296_membership : packet0296 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0296_shape : checkStripShape packet0296.row = true := by
  decide +kernel

private theorem packet0296_cache : checkStripCache packet0296 = true := by
  decide +kernel

private theorem packet0296_pair (i : Fin 7) : checkEdgePair packet0296 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0296_ok : checkStripPacket packet0296 = true :=
  checkStripPacket_intro packet0296_shape packet0296_cache packet0296_pair

theorem packet0297_membership : packet0297 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0297_shape : checkStripShape packet0297.row = true := by
  decide +kernel

private theorem packet0297_cache : checkStripCache packet0297 = true := by
  decide +kernel

private theorem packet0297_pair (i : Fin 7) : checkEdgePair packet0297 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0297_ok : checkStripPacket packet0297 = true :=
  checkStripPacket_intro packet0297_shape packet0297_cache packet0297_pair

theorem packet0298_membership : packet0298 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0298_shape : checkStripShape packet0298.row = true := by
  decide +kernel

private theorem packet0298_cache : checkStripCache packet0298 = true := by
  decide +kernel

private theorem packet0298_pair (i : Fin 7) : checkEdgePair packet0298 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0298_ok : checkStripPacket packet0298 = true :=
  checkStripPacket_intro packet0298_shape packet0298_cache packet0298_pair

theorem packet0299_membership : packet0299 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0299_shape : checkStripShape packet0299.row = true := by
  decide +kernel

private theorem packet0299_cache : checkStripCache packet0299 = true := by
  decide +kernel

private theorem packet0299_pair (i : Fin 7) : checkEdgePair packet0299 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0299_ok : checkStripPacket packet0299 = true :=
  checkStripPacket_intro packet0299_shape packet0299_cache packet0299_pair

theorem packet0300_membership : packet0300 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0300_shape : checkStripShape packet0300.row = true := by
  decide +kernel

private theorem packet0300_cache : checkStripCache packet0300 = true := by
  decide +kernel

private theorem packet0300_pair (i : Fin 7) : checkEdgePair packet0300 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0300_ok : checkStripPacket packet0300 = true :=
  checkStripPacket_intro packet0300_shape packet0300_cache packet0300_pair

theorem packet0301_membership : packet0301 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0301_shape : checkStripShape packet0301.row = true := by
  decide +kernel

private theorem packet0301_cache : checkStripCache packet0301 = true := by
  decide +kernel

private theorem packet0301_pair (i : Fin 7) : checkEdgePair packet0301 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0301_ok : checkStripPacket packet0301 = true :=
  checkStripPacket_intro packet0301_shape packet0301_cache packet0301_pair

theorem packet0302_membership : packet0302 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0302_shape : checkStripShape packet0302.row = true := by
  decide +kernel

private theorem packet0302_cache : checkStripCache packet0302 = true := by
  decide +kernel

private theorem packet0302_pair (i : Fin 7) : checkEdgePair packet0302 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0302_ok : checkStripPacket packet0302 = true :=
  checkStripPacket_intro packet0302_shape packet0302_cache packet0302_pair

theorem packet0303_membership : packet0303 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0303_shape : checkStripShape packet0303.row = true := by
  decide +kernel

private theorem packet0303_cache : checkStripCache packet0303 = true := by
  decide +kernel

private theorem packet0303_pair (i : Fin 7) : checkEdgePair packet0303 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0303_ok : checkStripPacket packet0303 = true :=
  checkStripPacket_intro packet0303_shape packet0303_cache packet0303_pair

theorem packet0304_membership : packet0304 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0304_shape : checkStripShape packet0304.row = true := by
  decide +kernel

private theorem packet0304_cache : checkStripCache packet0304 = true := by
  decide +kernel

private theorem packet0304_pair (i : Fin 7) : checkEdgePair packet0304 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0304_ok : checkStripPacket packet0304 = true :=
  checkStripPacket_intro packet0304_shape packet0304_cache packet0304_pair

theorem packet0305_membership : packet0305 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0305_shape : checkStripShape packet0305.row = true := by
  decide +kernel

private theorem packet0305_cache : checkStripCache packet0305 = true := by
  decide +kernel

private theorem packet0305_pair (i : Fin 7) : checkEdgePair packet0305 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0305_ok : checkStripPacket packet0305 = true :=
  checkStripPacket_intro packet0305_shape packet0305_cache packet0305_pair

theorem packet0306_membership : packet0306 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0306_shape : checkStripShape packet0306.row = true := by
  decide +kernel

private theorem packet0306_cache : checkStripCache packet0306 = true := by
  decide +kernel

private theorem packet0306_pair (i : Fin 7) : checkEdgePair packet0306 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0306_ok : checkStripPacket packet0306 = true :=
  checkStripPacket_intro packet0306_shape packet0306_cache packet0306_pair

theorem packet0307_membership : packet0307 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0307_shape : checkStripShape packet0307.row = true := by
  decide +kernel

private theorem packet0307_cache : checkStripCache packet0307 = true := by
  decide +kernel

private theorem packet0307_pair (i : Fin 7) : checkEdgePair packet0307 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0307_ok : checkStripPacket packet0307 = true :=
  checkStripPacket_intro packet0307_shape packet0307_cache packet0307_pair

theorem packet0308_membership : packet0308 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0308_shape : checkStripShape packet0308.row = true := by
  decide +kernel

private theorem packet0308_cache : checkStripCache packet0308 = true := by
  decide +kernel

private theorem packet0308_pair (i : Fin 7) : checkEdgePair packet0308 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0308_ok : checkStripPacket packet0308 = true :=
  checkStripPacket_intro packet0308_shape packet0308_cache packet0308_pair

theorem packet0309_membership : packet0309 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0309_shape : checkStripShape packet0309.row = true := by
  decide +kernel

private theorem packet0309_cache : checkStripCache packet0309 = true := by
  decide +kernel

private theorem packet0309_pair (i : Fin 7) : checkEdgePair packet0309 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0309_ok : checkStripPacket packet0309 = true :=
  checkStripPacket_intro packet0309_shape packet0309_cache packet0309_pair

theorem packet0310_membership : packet0310 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0310_shape : checkStripShape packet0310.row = true := by
  decide +kernel

private theorem packet0310_cache : checkStripCache packet0310 = true := by
  decide +kernel

private theorem packet0310_pair (i : Fin 7) : checkEdgePair packet0310 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0310_ok : checkStripPacket packet0310 = true :=
  checkStripPacket_intro packet0310_shape packet0310_cache packet0310_pair

theorem packet0311_membership : packet0311 ∈ packets012 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0311_shape : checkStripShape packet0311.row = true := by
  decide +kernel

private theorem packet0311_cache : checkStripCache packet0311 = true := by
  decide +kernel

private theorem packet0311_pair (i : Fin 7) : checkEdgePair packet0311 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0311_ok : checkStripPacket packet0311 = true :=
  checkStripPacket_intro packet0311_shape packet0311_cache packet0311_pair

theorem packets012_checked : packets012.all checkStripPacket = true := by
  simp only [packets012, List.all_cons, List.all_nil, Bool.true_and, packet0288_ok,
    packet0289_ok, packet0290_ok, packet0291_ok, packet0292_ok, packet0293_ok,
    packet0294_ok, packet0295_ok, packet0296_ok, packet0297_ok, packet0298_ok,
    packet0299_ok, packet0300_ok, packet0301_ok, packet0302_ok, packet0303_ok,
    packet0304_ok, packet0305_ok, packet0306_ok, packet0307_ok, packet0308_ok,
    packet0309_ok, packet0310_ok, packet0311_ok]

theorem packets012_valid : packets012.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
