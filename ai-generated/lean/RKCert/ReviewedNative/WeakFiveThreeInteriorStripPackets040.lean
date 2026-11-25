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

def packet0960 : StripRowPacket :=
  ⟨⟨⟨6,41,5,21⟩,
    ![447,1431,2791,4317,5790,7009,7833],![456,1452,2826,4364,5839,7050,7853]⟩,
    ⟨1049580039354901441072592007,177820750065507865483988254720⟩,
    ⟨65724608833589430915102373,8976549216704356892239990784⟩⟩

def packet0961 : StripRowPacket :=
  ⟨⟨⟨6,40,4,11⟩,
    ![452,1446,2817,4353,5828,7039,7847],![464,1477,2872,4429,5914,7117,7888]⟩,
    ⟨18510589211348460493117,2632078387625304884524544⟩,
    ⟨30141384070555724491979,3127058688413614119925760⟩⟩

def packet0962 : StripRowPacket :=
  ⟨⟨⟨6,41,4,11⟩,
    ![452,1444,2814,4350,5826,7038,7846],![464,1475,2869,4426,5912,7116,7888]⟩,
    ⟨632478350397741398029577177,88910375032753932741994127360⟩,
    ⟨109339998309108578296571249,11220686520880446115299988480⟩⟩

def packet0963 : StripRowPacket :=
  ⟨⟨⟨6,42,5,20⟩,
    ![442,1416,2763,4281,5752,6980,7821],![451,1438,2799,4328,5801,7018,7839]⟩,
    ⟨119391985724178688605705367,25157049057725804496326027264⟩,
    ⟨1254778085630557083676988829,203147696333004473041893670912⟩⟩

def packet0964 : StripRowPacket :=
  ⟨⟨⟨6,42,5,21⟩,
    ![447,1430,2788,4315,5788,7008,7833],![456,1450,2823,4361,5837,7049,7853]⟩,
    ⟨600748534711206232468184807,100628196230903217985304109056⟩,
    ⟨751741735039503834851523203,101573848166502236520946835456⟩⟩

def packet0965 : StripRowPacket :=
  ⟨⟨⟨6,43,5,20⟩,
    ![441,1414,2760,4278,5750,6979,7821],![451,1436,2797,4325,5799,7017,7839]⟩,
    ⟨46894367633541058300678687,9769423617160288745511710720⟩,
    ⟨3620346043276748360374573,579951402775849122084352000⟩⟩

def packet0966 : StripRowPacket :=
  ⟨⟨⟨6,43,5,21⟩,
    ![446,1428,2786,4312,5786,7007,7833],![455,1448,2820,4358,5835,7048,7853]⟩,
    ⟨235914661097263721227753039,39077694468641154982046842880⟩,
    ⟨2168899949269847055103443,289975701387924561042176000⟩⟩

def packet0967 : StripRowPacket :=
  ⟨⟨⟨6,42,4,11⟩,
    ![451,1443,2812,4348,5824,7037,7846],![463,1473,2866,4423,5910,7115,7888]⟩,
    ⟨27843427943296065788982621,3870315239650123768665542656⟩,
    ⟨250111779871988605219395195,25393462041625559130236708864⟩⟩

def packet0968 : StripRowPacket :=
  ⟨⟨⟨6,43,4,11⟩,
    ![450,1441,2809,4345,5822,7036,7846],![462,1471,2863,4420,5908,7114,7887]⟩,
    ⟨2186552705079716994252241,300597649758778115246514176⟩,
    ⟨721588451133198201233939,72493925346981140260544000⟩⟩

def packet0969 : StripRowPacket :=
  ⟨⟨⟨6,44,4,8⟩,
    ![417,1343,2642,4132,5614,6887,7787],![435,1388,2714,4217,5690,6937,7806]⟩,
    ⟨-345017659289391211063,2382559943421693477728000⟩,
    ⟨56877907889903065987077629,22231893962234530197821317120⟩⟩

def packet0970 : StripRowPacket :=
  ⟨⟨⟨6,45,4,8⟩,
    ![417,1341,2639,4130,5612,6886,7786],![434,1387,2711,4215,5688,6936,7806]⟩,
    ⟨-28170740476262019034537491,198438536699269177305667312640⟩,
    ⟨121778505477727966317094371,47101932956157300656953323520⟩⟩

def packet0971 : StripRowPacket :=
  ⟨⟨⟨6,44,4,9⟩,
    ![430,1380,2703,4205,5678,6929,7801],![445,1420,2769,4288,5760,6988,7826]⟩,
    ⟨44879936484122240340933,19060479547373547821824000⟩,
    ⟨56225480302966651846079401,11115946981117265098910658560⟩⟩

def packet0972 : StripRowPacket :=
  ⟨⟨⟨6,45,5,18⟩,
    ![430,1379,2700,4202,5676,6928,7801],![440,1403,2739,4250,5722,6960,7815]⟩,
    ⟨3782745337642705863667754293,1587508293594153418445338501120⟩,
    ⟨362492357666743850050333841,94203865912314601313906647040⟩⟩

def packet0973 : StripRowPacket :=
  ⟨⟨⟨6,45,5,19⟩,
    ![435,1395,2729,4238,5711,6952,7810],![445,1418,2766,4286,5758,6987,7826]⟩,
    ⟨11573601936738213743279562807,3175016587188306836890677002240⟩,
    ⟨168331365167143974638629,32938414654655455004862464⟩⟩

def packet0974 : StripRowPacket :=
  ⟨⟨⟨6,46,4,8⟩,
    ![416,1340,2637,4128,5610,6885,7786],![434,1385,2709,4212,5686,6935,7806]⟩,
    ⟨-15515895873203978620739389,111510611598168215084968476160⟩,
    ⟨4700940398918710156737305791,1799525720690467512988867747840⟩⟩

def packet0975 : StripRowPacket :=
  ⟨⟨⟨6,47,4,8⟩,
    ![415,1338,2635,4125,5608,6884,7785],![433,1383,2706,4209,5684,6934,7805]⟩,
    ⟨-10012367684546601013,73431403967052470045696⟩,
    ⟨21348994108561975043,8089534392718474888192⟩⟩

def packet0976 : StripRowPacket :=
  ⟨⟨⟨6,46,5,18⟩,
    ![429,1377,2698,4200,5675,6927,7801],![439,1401,2737,4248,5720,6959,7815]⟩,
    ⟨307241463124287400881297877,127440698969335102954249687040⟩,
    ⟨13991178123646759195012681989,3599051441380935025977735495680⟩⟩

def packet0977 : StripRowPacket :=
  ⟨⟨⟨6,46,5,19⟩,
    ![434,1394,2726,4236,5709,6950,7810],![444,1416,2764,4283,5756,6986,7826]⟩,
    ⟨6576197892595667247473170529,1784169785570691441359495618560⟩,
    ⟨4645118862364024519137688099,899762860345233756494433873920⟩⟩

def packet0978 : StripRowPacket :=
  ⟨⟨⟨6,47,5,18⟩,
    ![428,1376,2696,4198,5673,6926,7800],![438,1400,2735,4245,5718,6958,7815]⟩,
    ⟨18624257538399714738375,7636866012573456884752384⟩,
    ⟨444720155882675840455,113253481498058648434688⟩⟩

def packet0979 : StripRowPacket :=
  ⟨⟨⟨6,47,5,19⟩,
    ![434,1392,2724,4233,5707,6949,7809],![443,1415,2761,4280,5754,6984,7825]⟩,
    ⟨56914058854391990720477,15273732025146913769504768⟩,
    ⟨147638598561371007577,28313370374514662108672⟩⟩

def packet0980 : StripRowPacket :=
  ⟨⟨⟨6,44,5,20⟩,
    ![441,1412,2758,4276,5748,6978,7821],![450,1434,2794,4322,5797,7016,7838]⟩,
    ⟨9252001424255961037037,1906047954737354782182400⟩,
    ⟨40067853418270977869914111,6351969703495580056520376320⟩⟩

def packet0981 : StripRowPacket :=
  ⟨⟨⟨6,44,5,21⟩,
    ![445,1426,2783,4310,5784,7006,7832],![454,1447,2817,4355,5833,7046,7852]⟩,
    ⟨17898469711042814674629,2932381468826699664896000⟩,
    ⟨2584984820337900636880615,342029137880531233812635648⟩⟩

def packet0982 : StripRowPacket :=
  ⟨⟨⟨6,45,5,20⟩,
    ![440,1410,2755,4273,5746,6977,7820],![449,1432,2791,4320,5794,7015,7838]⟩,
    ⟨3895428299547753939805904257,793754146797076709222669250560⟩,
    ⟨600363051089319684882624039,94203865912314601313906647040⟩⟩

def packet0983 : StripRowPacket :=
  ⟨⟨⟨6,45,5,21⟩,
    ![445,1424,2781,4307,5782,7005,7832],![453,1445,2815,4353,5831,7045,7852]⟩,
    ⟨2798546351377688253595381607,453573798169758119555811000320⟩,
    ⟨359649198900303801149384569,47101932956157300656953323520⟩⟩

def packets040 : List StripRowPacket :=
  [packet0960, packet0961, packet0962, packet0963, packet0964, packet0965,
   packet0966, packet0967, packet0968, packet0969, packet0970, packet0971,
   packet0972, packet0973, packet0974, packet0975, packet0976, packet0977,
   packet0978, packet0979, packet0980, packet0981, packet0982, packet0983]

theorem packet0960_membership : packet0960 ∈ packets040 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0960_shape : checkStripShape packet0960.row = true := by
  decide +kernel

private theorem packet0960_cache : checkStripCache packet0960 = true := by
  decide +kernel

private theorem packet0960_pair (i : Fin 7) : checkEdgePair packet0960 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0960_ok : checkStripPacket packet0960 = true :=
  checkStripPacket_intro packet0960_shape packet0960_cache packet0960_pair

theorem packet0961_membership : packet0961 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0961_shape : checkStripShape packet0961.row = true := by
  decide +kernel

private theorem packet0961_cache : checkStripCache packet0961 = true := by
  decide +kernel

private theorem packet0961_pair (i : Fin 7) : checkEdgePair packet0961 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0961_ok : checkStripPacket packet0961 = true :=
  checkStripPacket_intro packet0961_shape packet0961_cache packet0961_pair

theorem packet0962_membership : packet0962 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0962_shape : checkStripShape packet0962.row = true := by
  decide +kernel

private theorem packet0962_cache : checkStripCache packet0962 = true := by
  decide +kernel

private theorem packet0962_pair (i : Fin 7) : checkEdgePair packet0962 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0962_ok : checkStripPacket packet0962 = true :=
  checkStripPacket_intro packet0962_shape packet0962_cache packet0962_pair

theorem packet0963_membership : packet0963 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0963_shape : checkStripShape packet0963.row = true := by
  decide +kernel

private theorem packet0963_cache : checkStripCache packet0963 = true := by
  decide +kernel

private theorem packet0963_pair (i : Fin 7) : checkEdgePair packet0963 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0963_ok : checkStripPacket packet0963 = true :=
  checkStripPacket_intro packet0963_shape packet0963_cache packet0963_pair

theorem packet0964_membership : packet0964 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0964_shape : checkStripShape packet0964.row = true := by
  decide +kernel

private theorem packet0964_cache : checkStripCache packet0964 = true := by
  decide +kernel

private theorem packet0964_pair (i : Fin 7) : checkEdgePair packet0964 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0964_ok : checkStripPacket packet0964 = true :=
  checkStripPacket_intro packet0964_shape packet0964_cache packet0964_pair

theorem packet0965_membership : packet0965 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0965_shape : checkStripShape packet0965.row = true := by
  decide +kernel

private theorem packet0965_cache : checkStripCache packet0965 = true := by
  decide +kernel

private theorem packet0965_pair (i : Fin 7) : checkEdgePair packet0965 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0965_ok : checkStripPacket packet0965 = true :=
  checkStripPacket_intro packet0965_shape packet0965_cache packet0965_pair

theorem packet0966_membership : packet0966 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0966_shape : checkStripShape packet0966.row = true := by
  decide +kernel

private theorem packet0966_cache : checkStripCache packet0966 = true := by
  decide +kernel

private theorem packet0966_pair (i : Fin 7) : checkEdgePair packet0966 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0966_ok : checkStripPacket packet0966 = true :=
  checkStripPacket_intro packet0966_shape packet0966_cache packet0966_pair

theorem packet0967_membership : packet0967 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0967_shape : checkStripShape packet0967.row = true := by
  decide +kernel

private theorem packet0967_cache : checkStripCache packet0967 = true := by
  decide +kernel

private theorem packet0967_pair (i : Fin 7) : checkEdgePair packet0967 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0967_ok : checkStripPacket packet0967 = true :=
  checkStripPacket_intro packet0967_shape packet0967_cache packet0967_pair

theorem packet0968_membership : packet0968 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0968_shape : checkStripShape packet0968.row = true := by
  decide +kernel

private theorem packet0968_cache : checkStripCache packet0968 = true := by
  decide +kernel

private theorem packet0968_pair (i : Fin 7) : checkEdgePair packet0968 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0968_ok : checkStripPacket packet0968 = true :=
  checkStripPacket_intro packet0968_shape packet0968_cache packet0968_pair

theorem packet0969_membership : packet0969 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0969_shape : checkStripShape packet0969.row = true := by
  decide +kernel

private theorem packet0969_cache : checkStripCache packet0969 = true := by
  decide +kernel

private theorem packet0969_pair (i : Fin 7) : checkEdgePair packet0969 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0969_ok : checkStripPacket packet0969 = true :=
  checkStripPacket_intro packet0969_shape packet0969_cache packet0969_pair

theorem packet0970_membership : packet0970 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0970_shape : checkStripShape packet0970.row = true := by
  decide +kernel

private theorem packet0970_cache : checkStripCache packet0970 = true := by
  decide +kernel

private theorem packet0970_pair (i : Fin 7) : checkEdgePair packet0970 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0970_ok : checkStripPacket packet0970 = true :=
  checkStripPacket_intro packet0970_shape packet0970_cache packet0970_pair

theorem packet0971_membership : packet0971 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0971_shape : checkStripShape packet0971.row = true := by
  decide +kernel

private theorem packet0971_cache : checkStripCache packet0971 = true := by
  decide +kernel

private theorem packet0971_pair (i : Fin 7) : checkEdgePair packet0971 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0971_ok : checkStripPacket packet0971 = true :=
  checkStripPacket_intro packet0971_shape packet0971_cache packet0971_pair

theorem packet0972_membership : packet0972 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0972_shape : checkStripShape packet0972.row = true := by
  decide +kernel

private theorem packet0972_cache : checkStripCache packet0972 = true := by
  decide +kernel

private theorem packet0972_pair (i : Fin 7) : checkEdgePair packet0972 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0972_ok : checkStripPacket packet0972 = true :=
  checkStripPacket_intro packet0972_shape packet0972_cache packet0972_pair

theorem packet0973_membership : packet0973 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0973_shape : checkStripShape packet0973.row = true := by
  decide +kernel

private theorem packet0973_cache : checkStripCache packet0973 = true := by
  decide +kernel

private theorem packet0973_pair (i : Fin 7) : checkEdgePair packet0973 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0973_ok : checkStripPacket packet0973 = true :=
  checkStripPacket_intro packet0973_shape packet0973_cache packet0973_pair

theorem packet0974_membership : packet0974 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0974_shape : checkStripShape packet0974.row = true := by
  decide +kernel

private theorem packet0974_cache : checkStripCache packet0974 = true := by
  decide +kernel

private theorem packet0974_pair (i : Fin 7) : checkEdgePair packet0974 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0974_ok : checkStripPacket packet0974 = true :=
  checkStripPacket_intro packet0974_shape packet0974_cache packet0974_pair

theorem packet0975_membership : packet0975 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0975_shape : checkStripShape packet0975.row = true := by
  decide +kernel

private theorem packet0975_cache : checkStripCache packet0975 = true := by
  decide +kernel

private theorem packet0975_pair (i : Fin 7) : checkEdgePair packet0975 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0975_ok : checkStripPacket packet0975 = true :=
  checkStripPacket_intro packet0975_shape packet0975_cache packet0975_pair

theorem packet0976_membership : packet0976 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0976_shape : checkStripShape packet0976.row = true := by
  decide +kernel

private theorem packet0976_cache : checkStripCache packet0976 = true := by
  decide +kernel

private theorem packet0976_pair (i : Fin 7) : checkEdgePair packet0976 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0976_ok : checkStripPacket packet0976 = true :=
  checkStripPacket_intro packet0976_shape packet0976_cache packet0976_pair

theorem packet0977_membership : packet0977 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0977_shape : checkStripShape packet0977.row = true := by
  decide +kernel

private theorem packet0977_cache : checkStripCache packet0977 = true := by
  decide +kernel

private theorem packet0977_pair (i : Fin 7) : checkEdgePair packet0977 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0977_ok : checkStripPacket packet0977 = true :=
  checkStripPacket_intro packet0977_shape packet0977_cache packet0977_pair

theorem packet0978_membership : packet0978 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0978_shape : checkStripShape packet0978.row = true := by
  decide +kernel

private theorem packet0978_cache : checkStripCache packet0978 = true := by
  decide +kernel

private theorem packet0978_pair (i : Fin 7) : checkEdgePair packet0978 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0978_ok : checkStripPacket packet0978 = true :=
  checkStripPacket_intro packet0978_shape packet0978_cache packet0978_pair

theorem packet0979_membership : packet0979 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0979_shape : checkStripShape packet0979.row = true := by
  decide +kernel

private theorem packet0979_cache : checkStripCache packet0979 = true := by
  decide +kernel

private theorem packet0979_pair (i : Fin 7) : checkEdgePair packet0979 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0979_ok : checkStripPacket packet0979 = true :=
  checkStripPacket_intro packet0979_shape packet0979_cache packet0979_pair

theorem packet0980_membership : packet0980 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0980_shape : checkStripShape packet0980.row = true := by
  decide +kernel

private theorem packet0980_cache : checkStripCache packet0980 = true := by
  decide +kernel

private theorem packet0980_pair (i : Fin 7) : checkEdgePair packet0980 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0980_ok : checkStripPacket packet0980 = true :=
  checkStripPacket_intro packet0980_shape packet0980_cache packet0980_pair

theorem packet0981_membership : packet0981 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0981_shape : checkStripShape packet0981.row = true := by
  decide +kernel

private theorem packet0981_cache : checkStripCache packet0981 = true := by
  decide +kernel

private theorem packet0981_pair (i : Fin 7) : checkEdgePair packet0981 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0981_ok : checkStripPacket packet0981 = true :=
  checkStripPacket_intro packet0981_shape packet0981_cache packet0981_pair

theorem packet0982_membership : packet0982 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0982_shape : checkStripShape packet0982.row = true := by
  decide +kernel

private theorem packet0982_cache : checkStripCache packet0982 = true := by
  decide +kernel

private theorem packet0982_pair (i : Fin 7) : checkEdgePair packet0982 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0982_ok : checkStripPacket packet0982 = true :=
  checkStripPacket_intro packet0982_shape packet0982_cache packet0982_pair

theorem packet0983_membership : packet0983 ∈ packets040 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0983_shape : checkStripShape packet0983.row = true := by
  decide +kernel

private theorem packet0983_cache : checkStripCache packet0983 = true := by
  decide +kernel

private theorem packet0983_pair (i : Fin 7) : checkEdgePair packet0983 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0983_ok : checkStripPacket packet0983 = true :=
  checkStripPacket_intro packet0983_shape packet0983_cache packet0983_pair

theorem packets040_checked : packets040.all checkStripPacket = true := by
  simp only [packets040, List.all_cons, List.all_nil, Bool.true_and, packet0960_ok,
    packet0961_ok, packet0962_ok, packet0963_ok, packet0964_ok, packet0965_ok,
    packet0966_ok, packet0967_ok, packet0968_ok, packet0969_ok, packet0970_ok,
    packet0971_ok, packet0972_ok, packet0973_ok, packet0974_ok, packet0975_ok,
    packet0976_ok, packet0977_ok, packet0978_ok, packet0979_ok, packet0980_ok,
    packet0981_ok, packet0982_ok, packet0983_ok]

theorem packets040_valid : packets040.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
