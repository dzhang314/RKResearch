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

def packet0672 : StripRowPacket :=
  ⟨⟨⟨6,13,3,7⟩,
    ![518,1609,3054,4627,6102,7274,7985],![537,1655,3131,4735,6238,7433,8192]⟩,
    ⟨42594798993308365798165531,4591647870223233062678589440⟩,
    ⟨120835660223,9473965346560⟩⟩

def packet0673 : StripRowPacket :=
  ⟨⟨⟨6,14,4,12⟩,
    ![501,1562,2973,4513,5964,7133,7886],![517,1599,3033,4595,6060,7227,7946]⟩,
    ⟨531685267276968526595361,85170143774583946144168960⟩,
    ⟨96874735175371515756421019,11878586471125139346398371840⟩⟩

def packet0674 : StripRowPacket :=
  ⟨⟨⟨6,14,4,13⟩,
    ![508,1583,3012,4570,6034,7201,7928],![523,1617,3067,4645,6125,7300,8011]⟩,
    ⟨243759829437004820306941,30970961372575980416061440⟩,
    ⟨4469980499910025079457781,456868710427889974861475840⟩⟩

def packet0675 : StripRowPacket :=
  ⟨⟨⟨6,15,4,12⟩,
    ![498,1556,2966,4508,5961,7132,7886],![513,1592,3026,4588,6056,7225,7945]⟩,
    ⟨88317860773383413461,13822210011724280657920⟩,
    ⟨3468417081159783917,416315055438384593920⟩⟩

def packet0676 : StripRowPacket :=
  ⟨⟨⟨6,15,4,13⟩,
    ![505,1577,3006,4565,6031,7200,7928],![519,1610,3059,4639,6121,7298,8010]⟩,
    ⟨445209444864561639323,55288840046897122631680⟩,
    ⟨2080458120715449983,208157527719192296960⟩⟩

def packet0677 : StripRowPacket :=
  ⟨⟨⟨6,14,3,7⟩,
    ![515,1602,3047,4621,6099,7273,7985],![533,1647,3123,4728,6234,7431,8192]⟩,
    ⟨1617987589253115970185629,170340287549167892288337920⟩,
    ⟨305011781353703,23388625692450304⟩⟩

def packet0678 : StripRowPacket :=
  ⟨⟨⟨6,15,3,7⟩,
    ![511,1596,3040,4616,6096,7272,7986],![529,1640,3115,4722,6230,7429,8192]⟩,
    ⟨24415793028890437491,2513129093040778301440⟩,
    ⟨77113,5788640⟩⟩

def packet0679 : StripRowPacket :=
  ⟨⟨⟨6,16,4,0⟩,
    ![0,897,2223,3796,5386,6768,7748],![138,978,2284,3842,5417,6785,7756]⟩,
    ⟨-345077199020369,24948392769899456⟩,
    ⟨-166704189823301744507,14047384734785906696192⟩⟩

def packet0680 : StripRowPacket :=
  ⟨⟨⟨6,16,4,1⟩,
    ![104,959,2272,3832,5409,6779,7752],![228,1050,2342,3884,5443,6798,7760]⟩,
    ⟨-6127419088372765597,504955469662764989440⟩,
    ⟨-357144436893764933991,35118461836964766740480⟩⟩

def packet0681 : StripRowPacket :=
  ⟨⟨⟨6,17,4,0⟩,
    ![0,893,2216,3790,5382,6765,7748],![137,973,2278,3836,5412,6782,7755]⟩,
    ⟨-177233707737,12575318783456⟩,
    ⟨-137273857257555578256447131,11344443006018218755009015808⟩⟩

def packet0682 : StripRowPacket :=
  ⟨⟨⟨6,17,4,1⟩,
    ![104,955,2266,3826,5404,6776,7751],![227,1045,2335,3878,5439,6795,7759]⟩,
    ⟨-16151568407785215690244247,1306428591836629703543349248⟩,
    ⟨-58817728779288907603482235,5672221503009109377504507904⟩⟩

def packet0683 : StripRowPacket :=
  ⟨⟨⟨6,16,4,2⟩,
    ![203,1031,2328,3873,5434,6792,7756],![297,1126,2405,3931,5473,6813,7765]⟩,
    ⟨-2635237834286631317,252477734831382494720⟩,
    ⟨-45773599881427001033,5402840282609964113920⟩⟩

def packet0684 : StripRowPacket :=
  ⟨⟨⟨6,16,4,3⟩,
    ![279,1108,2392,3919,5464,6807,7760],![348,1200,2475,3984,5508,6831,7770]⟩,
    ⟨-4413532248773759671,504955469662764989440⟩,
    ⟨-118956180782393039719,17559230918482383370240⟩⟩

def packet0685 : StripRowPacket :=
  ⟨⟨⟨6,17,4,2⟩,
    ![203,1027,2322,3867,5430,6789,7755],![295,1121,2399,3925,5469,6811,7764]⟩,
    ⟨-6945313393023671082034199,653214295918314851771674624⟩,
    ⟨-97997057859600052157481809,11344443006018218755009015808⟩⟩

def packet0686 : StripRowPacket :=
  ⟨⟨⟨6,17,4,3⟩,
    ![278,1104,2386,3913,5460,6804,7760],![346,1195,2469,3978,5503,6828,7769]⟩,
    ⟨-11629685164309468637892549,1306428591836629703543349248⟩,
    ⟨-19589664540155572276999787,2836110751504554688752253952⟩⟩

def packet0687 : StripRowPacket :=
  ⟨⟨⟨5,9,4,0⟩,
    ![0,881,2204,3779,5373,6760,7746],![149,974,2273,3830,5408,6780,7754]⟩,
    ⟨-2648312527,181323951952⟩,
    ⟨-7310747736205970789,593721644402366425088⟩⟩

def packet0688 : StripRowPacket :=
  ⟨⟨⟨5,9,4,1⟩,
    ![89,942,2253,3815,5396,6772,7750],![234,1046,2331,3872,5435,6793,7758]⟩,
    ⟨-4230050172065608056853,329803888774313199161344⟩,
    ⟨-3126858237532720901,296860822201183212544⟩⟩

def packet0689 : StripRowPacket :=
  ⟨⟨⟨5,9,4,2⟩,
    ![192,1014,2309,3855,5422,6785,7754],![299,1122,2395,3921,5465,6809,7763]⟩,
    ⟨-1821587967564515192981,164901944387156599580672⟩,
    ⟨-5196685213924912815,593721644402366425088⟩⟩

def packet0690 : StripRowPacket :=
  ⟨⟨⟨5,9,4,3⟩,
    ![270,1091,2372,3901,5451,6800,7758],![347,1195,2465,3975,5501,6827,7769]⟩,
    ⟨-277845608926586610461,29982171706755745378304⟩,
    ⟨-1034913488196095957,148430411100591606272⟩⟩

def packet0691 : StripRowPacket :=
  ⟨⟨⟨6,16,4,4⟩,
    ![336,1184,2460,3971,5497,6824,7766],![386,1270,2549,4044,5547,6851,7777]⟩,
    ⟨-889147207243564177,126238867415691247360⟩,
    ⟨-356592647800593304323,70236923673929533480960⟩⟩

def packet0692 : StripRowPacket :=
  ⟨⟨⟨6,16,4,5⟩,
    ![378,1256,2532,4029,5536,6844,7772],![417,1334,2623,4109,5593,6876,7784]⟩,
    ⟨-539929081834950749,100991093932552997888⟩,
    ⟨-2157823386105585907,638517487944813940736⟩⟩

def packet0693 : StripRowPacket :=
  ⟨⟨⟨6,17,4,4⟩,
    ![334,1180,2454,3966,5493,6822,7765],![384,1265,2542,4038,5543,6849,7776]⟩,
    ⟨-2342185885642898777929175,326607147959157425885837312⟩,
    ⟨-58720258461644526058516487,11344443006018218755009015808⟩⟩

def packet0694 : StripRowPacket :=
  ⟨⟨⟨6,17,4,5⟩,
    ![376,1251,2526,4024,5532,6842,7771],![414,1329,2617,4103,5589,6874,7784]⟩,
    ⟨-7107801920833721585540851,1306428591836629703543349248⟩,
    ⟨-1776448125575761954956083,515656500273555397954955264⟩⟩

def packet0695 : StripRowPacket :=
  ⟨⟨⟨6,16,4,6⟩,
    ![408,1319,2605,4092,5580,6867,7780],![440,1389,2696,4179,5645,6905,7794]⟩,
    ⟨-921350994687625391,252477734831382494720⟩,
    ⟨-16875499591805085031,10033846239132790497280⟩⟩

def packets028 : List StripRowPacket :=
  [packet0672, packet0673, packet0674, packet0675, packet0676, packet0677,
   packet0678, packet0679, packet0680, packet0681, packet0682, packet0683,
   packet0684, packet0685, packet0686, packet0687, packet0688, packet0689,
   packet0690, packet0691, packet0692, packet0693, packet0694, packet0695]

theorem packet0672_membership : packet0672 ∈ packets028 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0672_shape : checkStripShape packet0672.row = true := by
  decide +kernel

private theorem packet0672_cache : checkStripCache packet0672 = true := by
  decide +kernel

private theorem packet0672_pair (i : Fin 7) : checkEdgePair packet0672 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0672_ok : checkStripPacket packet0672 = true :=
  checkStripPacket_intro packet0672_shape packet0672_cache packet0672_pair

theorem packet0673_membership : packet0673 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0673_shape : checkStripShape packet0673.row = true := by
  decide +kernel

private theorem packet0673_cache : checkStripCache packet0673 = true := by
  decide +kernel

private theorem packet0673_pair (i : Fin 7) : checkEdgePair packet0673 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0673_ok : checkStripPacket packet0673 = true :=
  checkStripPacket_intro packet0673_shape packet0673_cache packet0673_pair

theorem packet0674_membership : packet0674 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0674_shape : checkStripShape packet0674.row = true := by
  decide +kernel

private theorem packet0674_cache : checkStripCache packet0674 = true := by
  decide +kernel

private theorem packet0674_pair (i : Fin 7) : checkEdgePair packet0674 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0674_ok : checkStripPacket packet0674 = true :=
  checkStripPacket_intro packet0674_shape packet0674_cache packet0674_pair

theorem packet0675_membership : packet0675 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0675_shape : checkStripShape packet0675.row = true := by
  decide +kernel

private theorem packet0675_cache : checkStripCache packet0675 = true := by
  decide +kernel

private theorem packet0675_pair (i : Fin 7) : checkEdgePair packet0675 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0675_ok : checkStripPacket packet0675 = true :=
  checkStripPacket_intro packet0675_shape packet0675_cache packet0675_pair

theorem packet0676_membership : packet0676 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0676_shape : checkStripShape packet0676.row = true := by
  decide +kernel

private theorem packet0676_cache : checkStripCache packet0676 = true := by
  decide +kernel

private theorem packet0676_pair (i : Fin 7) : checkEdgePair packet0676 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0676_ok : checkStripPacket packet0676 = true :=
  checkStripPacket_intro packet0676_shape packet0676_cache packet0676_pair

theorem packet0677_membership : packet0677 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0677_shape : checkStripShape packet0677.row = true := by
  decide +kernel

private theorem packet0677_cache : checkStripCache packet0677 = true := by
  decide +kernel

private theorem packet0677_pair (i : Fin 7) : checkEdgePair packet0677 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0677_ok : checkStripPacket packet0677 = true :=
  checkStripPacket_intro packet0677_shape packet0677_cache packet0677_pair

theorem packet0678_membership : packet0678 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0678_shape : checkStripShape packet0678.row = true := by
  decide +kernel

private theorem packet0678_cache : checkStripCache packet0678 = true := by
  decide +kernel

private theorem packet0678_pair (i : Fin 7) : checkEdgePair packet0678 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0678_ok : checkStripPacket packet0678 = true :=
  checkStripPacket_intro packet0678_shape packet0678_cache packet0678_pair

theorem packet0679_membership : packet0679 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0679_shape : checkStripShape packet0679.row = true := by
  decide +kernel

private theorem packet0679_cache : checkStripCache packet0679 = true := by
  decide +kernel

private theorem packet0679_pair (i : Fin 7) : checkEdgePair packet0679 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0679_ok : checkStripPacket packet0679 = true :=
  checkStripPacket_intro packet0679_shape packet0679_cache packet0679_pair

theorem packet0680_membership : packet0680 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0680_shape : checkStripShape packet0680.row = true := by
  decide +kernel

private theorem packet0680_cache : checkStripCache packet0680 = true := by
  decide +kernel

private theorem packet0680_pair (i : Fin 7) : checkEdgePair packet0680 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0680_ok : checkStripPacket packet0680 = true :=
  checkStripPacket_intro packet0680_shape packet0680_cache packet0680_pair

theorem packet0681_membership : packet0681 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0681_shape : checkStripShape packet0681.row = true := by
  decide +kernel

private theorem packet0681_cache : checkStripCache packet0681 = true := by
  decide +kernel

private theorem packet0681_pair (i : Fin 7) : checkEdgePair packet0681 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0681_ok : checkStripPacket packet0681 = true :=
  checkStripPacket_intro packet0681_shape packet0681_cache packet0681_pair

theorem packet0682_membership : packet0682 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0682_shape : checkStripShape packet0682.row = true := by
  decide +kernel

private theorem packet0682_cache : checkStripCache packet0682 = true := by
  decide +kernel

private theorem packet0682_pair (i : Fin 7) : checkEdgePair packet0682 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0682_ok : checkStripPacket packet0682 = true :=
  checkStripPacket_intro packet0682_shape packet0682_cache packet0682_pair

theorem packet0683_membership : packet0683 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0683_shape : checkStripShape packet0683.row = true := by
  decide +kernel

private theorem packet0683_cache : checkStripCache packet0683 = true := by
  decide +kernel

private theorem packet0683_pair (i : Fin 7) : checkEdgePair packet0683 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0683_ok : checkStripPacket packet0683 = true :=
  checkStripPacket_intro packet0683_shape packet0683_cache packet0683_pair

theorem packet0684_membership : packet0684 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0684_shape : checkStripShape packet0684.row = true := by
  decide +kernel

private theorem packet0684_cache : checkStripCache packet0684 = true := by
  decide +kernel

private theorem packet0684_pair (i : Fin 7) : checkEdgePair packet0684 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0684_ok : checkStripPacket packet0684 = true :=
  checkStripPacket_intro packet0684_shape packet0684_cache packet0684_pair

theorem packet0685_membership : packet0685 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0685_shape : checkStripShape packet0685.row = true := by
  decide +kernel

private theorem packet0685_cache : checkStripCache packet0685 = true := by
  decide +kernel

private theorem packet0685_pair (i : Fin 7) : checkEdgePair packet0685 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0685_ok : checkStripPacket packet0685 = true :=
  checkStripPacket_intro packet0685_shape packet0685_cache packet0685_pair

theorem packet0686_membership : packet0686 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0686_shape : checkStripShape packet0686.row = true := by
  decide +kernel

private theorem packet0686_cache : checkStripCache packet0686 = true := by
  decide +kernel

private theorem packet0686_pair (i : Fin 7) : checkEdgePair packet0686 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0686_ok : checkStripPacket packet0686 = true :=
  checkStripPacket_intro packet0686_shape packet0686_cache packet0686_pair

theorem packet0687_membership : packet0687 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0687_shape : checkStripShape packet0687.row = true := by
  decide +kernel

private theorem packet0687_cache : checkStripCache packet0687 = true := by
  decide +kernel

private theorem packet0687_pair (i : Fin 7) : checkEdgePair packet0687 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0687_ok : checkStripPacket packet0687 = true :=
  checkStripPacket_intro packet0687_shape packet0687_cache packet0687_pair

theorem packet0688_membership : packet0688 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0688_shape : checkStripShape packet0688.row = true := by
  decide +kernel

private theorem packet0688_cache : checkStripCache packet0688 = true := by
  decide +kernel

private theorem packet0688_pair (i : Fin 7) : checkEdgePair packet0688 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0688_ok : checkStripPacket packet0688 = true :=
  checkStripPacket_intro packet0688_shape packet0688_cache packet0688_pair

theorem packet0689_membership : packet0689 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0689_shape : checkStripShape packet0689.row = true := by
  decide +kernel

private theorem packet0689_cache : checkStripCache packet0689 = true := by
  decide +kernel

private theorem packet0689_pair (i : Fin 7) : checkEdgePair packet0689 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0689_ok : checkStripPacket packet0689 = true :=
  checkStripPacket_intro packet0689_shape packet0689_cache packet0689_pair

theorem packet0690_membership : packet0690 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0690_shape : checkStripShape packet0690.row = true := by
  decide +kernel

private theorem packet0690_cache : checkStripCache packet0690 = true := by
  decide +kernel

private theorem packet0690_pair (i : Fin 7) : checkEdgePair packet0690 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0690_ok : checkStripPacket packet0690 = true :=
  checkStripPacket_intro packet0690_shape packet0690_cache packet0690_pair

theorem packet0691_membership : packet0691 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0691_shape : checkStripShape packet0691.row = true := by
  decide +kernel

private theorem packet0691_cache : checkStripCache packet0691 = true := by
  decide +kernel

private theorem packet0691_pair (i : Fin 7) : checkEdgePair packet0691 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0691_ok : checkStripPacket packet0691 = true :=
  checkStripPacket_intro packet0691_shape packet0691_cache packet0691_pair

theorem packet0692_membership : packet0692 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0692_shape : checkStripShape packet0692.row = true := by
  decide +kernel

private theorem packet0692_cache : checkStripCache packet0692 = true := by
  decide +kernel

private theorem packet0692_pair (i : Fin 7) : checkEdgePair packet0692 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0692_ok : checkStripPacket packet0692 = true :=
  checkStripPacket_intro packet0692_shape packet0692_cache packet0692_pair

theorem packet0693_membership : packet0693 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0693_shape : checkStripShape packet0693.row = true := by
  decide +kernel

private theorem packet0693_cache : checkStripCache packet0693 = true := by
  decide +kernel

private theorem packet0693_pair (i : Fin 7) : checkEdgePair packet0693 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0693_ok : checkStripPacket packet0693 = true :=
  checkStripPacket_intro packet0693_shape packet0693_cache packet0693_pair

theorem packet0694_membership : packet0694 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0694_shape : checkStripShape packet0694.row = true := by
  decide +kernel

private theorem packet0694_cache : checkStripCache packet0694 = true := by
  decide +kernel

private theorem packet0694_pair (i : Fin 7) : checkEdgePair packet0694 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0694_ok : checkStripPacket packet0694 = true :=
  checkStripPacket_intro packet0694_shape packet0694_cache packet0694_pair

theorem packet0695_membership : packet0695 ∈ packets028 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0695_shape : checkStripShape packet0695.row = true := by
  decide +kernel

private theorem packet0695_cache : checkStripCache packet0695 = true := by
  decide +kernel

private theorem packet0695_pair (i : Fin 7) : checkEdgePair packet0695 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0695_ok : checkStripPacket packet0695 = true :=
  checkStripPacket_intro packet0695_shape packet0695_cache packet0695_pair

theorem packets028_checked : packets028.all checkStripPacket = true := by
  simp only [packets028, List.all_cons, List.all_nil, Bool.true_and, packet0672_ok,
    packet0673_ok, packet0674_ok, packet0675_ok, packet0676_ok, packet0677_ok,
    packet0678_ok, packet0679_ok, packet0680_ok, packet0681_ok, packet0682_ok,
    packet0683_ok, packet0684_ok, packet0685_ok, packet0686_ok, packet0687_ok,
    packet0688_ok, packet0689_ok, packet0690_ok, packet0691_ok, packet0692_ok,
    packet0693_ok, packet0694_ok, packet0695_ok]

theorem packets028_valid : packets028.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
