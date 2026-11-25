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

def packet0792 : StripRowPacket :=
  ⟨⟨⟨5,14,4,4⟩,
    ![320,1140,2398,3910,5452,6798,7757],![371,1228,2491,3988,5506,6828,7769]⟩,
    ⟨-22562208643738485076645,2611183482522549678734848⟩,
    ⟨-7702884765343021839309,1262351085864926039437312⟩⟩

def packet0793 : StripRowPacket :=
  ⟨⟨⟨5,14,4,5⟩,
    ![360,1211,2471,3969,5491,6819,7764],![398,1290,2566,4055,5553,6854,7777]⟩,
    ⟨-68494020971506280671817,10444733930090198714939392⟩,
    ⟨-2536382360147478371323,631175542932463019718656⟩⟩

def packet0794 : StripRowPacket :=
  ⟨⟨⟨5,15,4,4⟩,
    ![319,1135,2391,3903,5446,6795,7756],![369,1223,2484,3980,5500,6825,7768]⟩,
    ⟨-18421551790725245,2079679714083580928⟩,
    ⟨-86945058384332417,13864351885222339072⟩⟩

def packet0795 : StripRowPacket :=
  ⟨⟨⟨5,15,4,5⟩,
    ![358,1206,2464,3962,5485,6816,7763],![396,1285,2558,4047,5547,6850,7776]⟩,
    ⟨-726543812432848829,108143345132346208256⟩,
    ⟨-28636448419096959,6932175942611169536⟩⟩

def packet0796 : StripRowPacket :=
  ⟨⟨⟨5,14,4,6⟩,
    ![389,1273,2543,4033,5536,6843,7772],![420,1344,2638,4126,5607,6884,7787]⟩,
    ⟨-23369603684029310518527,5222366965045099357469696⟩,
    ⟨-2442644675246891645983,1262351085864926039437312⟩⟩

def packet0797 : StripRowPacket :=
  ⟨⟨⟨5,14,4,7⟩,
    ![411,1326,2614,4102,5587,6871,7781],![437,1389,2706,4199,5667,6919,7799]⟩,
    ⟨-24984393764610961402291,10444733930090198714939392⟩,
    ⟨23434421225146681335,157793885733115754929664⟩⟩

def packet0798 : StripRowPacket :=
  ⟨⟨⟨5,15,4,6⟩,
    ![387,1268,2537,4026,5531,6840,7771],![418,1338,2630,4118,5601,6880,7786]⟩,
    ⟨-247583465873992459,54071672566173104128⟩,
    ⟨-2123133484004263,1066488606555564544⟩⟩

def packet0799 : StripRowPacket :=
  ⟨⟨⟨5,15,4,7⟩,
    ![409,1321,2607,4095,5582,6868,7780],![434,1383,2698,4191,5661,6916,7798]⟩,
    ⟨-263790051063121007,108143345132346208256⟩,
    ⟨258928281760385,1733043985652792384⟩⟩

def packet0800 : StripRowPacket :=
  ⟨⟨⟨6,24,4,8⟩,
    ![435,1388,2704,4195,5662,6915,7795],![455,1439,2783,4284,5740,6965,7816]⟩,
    ⟨-2584717438675216539,12139654843489146733760⟩,
    ⟨3124010158272805903317,1578552328059047105290240⟩⟩

def packet0801 : StripRowPacket :=
  ⟨⟨⟨6,25,4,8⟩,
    ![434,1385,2700,4191,5659,6913,7795],![454,1436,2778,4280,5737,6964,7815]⟩,
    ⟨-15129203181888069634319,72513132723587765542108160⟩,
    ⟨7696440979476906956522189,3828373581899111509493166080⟩⟩

def packet0802 : StripRowPacket :=
  ⟨⟨⟨6,24,4,9⟩,
    ![449,1428,2767,4267,5725,6955,7810],![467,1472,2839,4356,5810,7015,7835]⟩,
    ⟨84412585224319912817,48558619373956586935040⟩,
    ⟨3102390984736599470113,789276164029523552645120⟩⟩

def packet0803 : StripRowPacket :=
  ⟨⟨⟨6,25,4,9⟩,
    ![448,1424,2763,4263,5722,6953,7809],![465,1468,2834,4352,5807,7013,7834]⟩,
    ⟨1909588985267387415033683,1077337971893303945197035520⟩,
    ⟨117556713102872545616281,29449027553070088534562816⟩⟩

def packet0804 : StripRowPacket :=
  ⟨⟨⟨5,13,4,8⟩,
    ![430,1377,2689,4180,5650,6908,7793],![453,1434,2777,4281,5739,6965,7816]⟩,
    ⟨-35681996682704658147,111737616105755206561280⟩,
    ⟨220753350214025285167,101561233814784778311680⟩⟩

def packet0805 : StripRowPacket :=
  ⟨⟨⟨6,26,4,9⟩,
    ![446,1421,2758,4260,5719,6952,7809],![464,1465,2830,4347,5804,7012,7834]⟩,
    ⟨104505305402509344815292009,57860460440681073493032366080⟩,
    ⟨13996112635719616032870047,3453790927443364421477724160⟩⟩

def packet0806 : StripRowPacket :=
  ⟨⟨⟨6,27,4,9⟩,
    ![445,1418,2755,4256,5717,6950,7808],![462,1461,2825,4343,5801,7010,7833]⟩,
    ⟨13534726895256461342035,7358389856432794136928256⟩,
    ⟨1108716276047409610888753,269611211610265373955611648⟩⟩

def packet0807 : StripRowPacket :=
  ⟨⟨⟨6,24,4,10⟩,
    ![461,1461,2823,4338,5793,7002,7828],![476,1500,2889,4423,5882,7072,7860]⟩,
    ⟨17916404020334069179,4855861937395658693504⟩,
    ⟨1857110756134718395427,315710465611809421058048⟩⟩

def packet0808 : StripRowPacket :=
  ⟨⟨⟨6,25,4,10⟩,
    ![459,1457,2819,4334,5790,7001,7828],![474,1496,2884,4419,5879,7071,7860]⟩,
    ⟨14153841462329891526220369,3770682901626563808189624320⟩,
    ⟨22868304427269954903710871,3828373581899111509493166080⟩⟩

def packet0809 : StripRowPacket :=
  ⟨⟨⟨6,24,4,11⟩,
    ![470,1489,2873,4405,5864,7057,7852],![484,1524,2933,4486,5955,7138,7894]⟩,
    ⟨21070422706335497751,3735278413381275918080⟩,
    ⟨3091581397968496253511,394638082014761776322560⟩⟩

def packet0810 : StripRowPacket :=
  ⟨⟨⟨6,25,4,11⟩,
    ![468,1485,2869,4401,5861,7056,7852],![482,1520,2928,4481,5952,7136,7894]⟩,
    ⟨8649648590489570839929139,1508273160650625523275849728⟩,
    ⟨7613559037791619719326303,957093395474777877373291520⟩⟩

def packet0811 : StripRowPacket :=
  ⟨⟨⟨6,26,4,10⟩,
    ![458,1454,2815,4330,5788,6999,7827],![473,1493,2880,4415,5876,7069,7859]⟩,
    ⟨22084388397615793020038209,5786046044068107349303236608⟩,
    ⟨761518554303650332064503,125592397361576888053735424⟩⟩

def packet0812 : StripRowPacket :=
  ⟨⟨⟨6,27,4,10⟩,
    ![456,1451,2811,4327,5785,6998,7827],![471,1489,2875,4411,5874,7068,7859]⟩,
    ⟨14272479695865831661159,3679194928216397068464128⟩,
    ⟨3317564476152075329433103,539222423220530747911223296⟩⟩

def packet0813 : StripRowPacket :=
  ⟨⟨⟨6,26,4,11⟩,
    ![467,1482,2865,4397,5859,7055,7851],![480,1516,2923,4477,5949,7135,7893]⟩,
    ⟨337182462549806515585472171,57860460440681073493032366080⟩,
    ⟨13943703925490576115338809,1726895463721682210738862080⟩⟩

def packet0814 : StripRowPacket :=
  ⟨⟨⟨6,27,4,11⟩,
    ![465,1479,2861,4394,5856,7054,7851],![479,1513,2919,4473,5946,7133,7893]⟩,
    ⟨3959562898927896845691,668944532402981285175296⟩,
    ⟨1104424100052332859272175,134805605805132686977805824⟩⟩

def packet0815 : StripRowPacket :=
  ⟨⟨⟨6,28,4,8⟩,
    ![430,1376,2689,4180,5650,6908,7793],![450,1426,2765,4268,5728,6959,7814]⟩,
    ⟨-15317047937634515049779,77891147566694321527965440⟩,
    ⟨312507771059307772022213,148639630237292407656734720⟩⟩

def packets033 : List StripRowPacket :=
  [packet0792, packet0793, packet0794, packet0795, packet0796, packet0797,
   packet0798, packet0799, packet0800, packet0801, packet0802, packet0803,
   packet0804, packet0805, packet0806, packet0807, packet0808, packet0809,
   packet0810, packet0811, packet0812, packet0813, packet0814, packet0815]

theorem packet0792_membership : packet0792 ∈ packets033 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0792_shape : checkStripShape packet0792.row = true := by
  decide +kernel

private theorem packet0792_cache : checkStripCache packet0792 = true := by
  decide +kernel

private theorem packet0792_pair (i : Fin 7) : checkEdgePair packet0792 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0792_ok : checkStripPacket packet0792 = true :=
  checkStripPacket_intro packet0792_shape packet0792_cache packet0792_pair

theorem packet0793_membership : packet0793 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0793_shape : checkStripShape packet0793.row = true := by
  decide +kernel

private theorem packet0793_cache : checkStripCache packet0793 = true := by
  decide +kernel

private theorem packet0793_pair (i : Fin 7) : checkEdgePair packet0793 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0793_ok : checkStripPacket packet0793 = true :=
  checkStripPacket_intro packet0793_shape packet0793_cache packet0793_pair

theorem packet0794_membership : packet0794 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0794_shape : checkStripShape packet0794.row = true := by
  decide +kernel

private theorem packet0794_cache : checkStripCache packet0794 = true := by
  decide +kernel

private theorem packet0794_pair (i : Fin 7) : checkEdgePair packet0794 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0794_ok : checkStripPacket packet0794 = true :=
  checkStripPacket_intro packet0794_shape packet0794_cache packet0794_pair

theorem packet0795_membership : packet0795 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0795_shape : checkStripShape packet0795.row = true := by
  decide +kernel

private theorem packet0795_cache : checkStripCache packet0795 = true := by
  decide +kernel

private theorem packet0795_pair (i : Fin 7) : checkEdgePair packet0795 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0795_ok : checkStripPacket packet0795 = true :=
  checkStripPacket_intro packet0795_shape packet0795_cache packet0795_pair

theorem packet0796_membership : packet0796 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0796_shape : checkStripShape packet0796.row = true := by
  decide +kernel

private theorem packet0796_cache : checkStripCache packet0796 = true := by
  decide +kernel

private theorem packet0796_pair (i : Fin 7) : checkEdgePair packet0796 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0796_ok : checkStripPacket packet0796 = true :=
  checkStripPacket_intro packet0796_shape packet0796_cache packet0796_pair

theorem packet0797_membership : packet0797 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0797_shape : checkStripShape packet0797.row = true := by
  decide +kernel

private theorem packet0797_cache : checkStripCache packet0797 = true := by
  decide +kernel

private theorem packet0797_pair (i : Fin 7) : checkEdgePair packet0797 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0797_ok : checkStripPacket packet0797 = true :=
  checkStripPacket_intro packet0797_shape packet0797_cache packet0797_pair

theorem packet0798_membership : packet0798 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0798_shape : checkStripShape packet0798.row = true := by
  decide +kernel

private theorem packet0798_cache : checkStripCache packet0798 = true := by
  decide +kernel

private theorem packet0798_pair (i : Fin 7) : checkEdgePair packet0798 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0798_ok : checkStripPacket packet0798 = true :=
  checkStripPacket_intro packet0798_shape packet0798_cache packet0798_pair

theorem packet0799_membership : packet0799 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0799_shape : checkStripShape packet0799.row = true := by
  decide +kernel

private theorem packet0799_cache : checkStripCache packet0799 = true := by
  decide +kernel

private theorem packet0799_pair (i : Fin 7) : checkEdgePair packet0799 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0799_ok : checkStripPacket packet0799 = true :=
  checkStripPacket_intro packet0799_shape packet0799_cache packet0799_pair

theorem packet0800_membership : packet0800 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0800_shape : checkStripShape packet0800.row = true := by
  decide +kernel

private theorem packet0800_cache : checkStripCache packet0800 = true := by
  decide +kernel

private theorem packet0800_pair (i : Fin 7) : checkEdgePair packet0800 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0800_ok : checkStripPacket packet0800 = true :=
  checkStripPacket_intro packet0800_shape packet0800_cache packet0800_pair

theorem packet0801_membership : packet0801 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0801_shape : checkStripShape packet0801.row = true := by
  decide +kernel

private theorem packet0801_cache : checkStripCache packet0801 = true := by
  decide +kernel

private theorem packet0801_pair (i : Fin 7) : checkEdgePair packet0801 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0801_ok : checkStripPacket packet0801 = true :=
  checkStripPacket_intro packet0801_shape packet0801_cache packet0801_pair

theorem packet0802_membership : packet0802 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0802_shape : checkStripShape packet0802.row = true := by
  decide +kernel

private theorem packet0802_cache : checkStripCache packet0802 = true := by
  decide +kernel

private theorem packet0802_pair (i : Fin 7) : checkEdgePair packet0802 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0802_ok : checkStripPacket packet0802 = true :=
  checkStripPacket_intro packet0802_shape packet0802_cache packet0802_pair

theorem packet0803_membership : packet0803 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0803_shape : checkStripShape packet0803.row = true := by
  decide +kernel

private theorem packet0803_cache : checkStripCache packet0803 = true := by
  decide +kernel

private theorem packet0803_pair (i : Fin 7) : checkEdgePair packet0803 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0803_ok : checkStripPacket packet0803 = true :=
  checkStripPacket_intro packet0803_shape packet0803_cache packet0803_pair

theorem packet0804_membership : packet0804 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0804_shape : checkStripShape packet0804.row = true := by
  decide +kernel

private theorem packet0804_cache : checkStripCache packet0804 = true := by
  decide +kernel

private theorem packet0804_pair (i : Fin 7) : checkEdgePair packet0804 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0804_ok : checkStripPacket packet0804 = true :=
  checkStripPacket_intro packet0804_shape packet0804_cache packet0804_pair

theorem packet0805_membership : packet0805 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0805_shape : checkStripShape packet0805.row = true := by
  decide +kernel

private theorem packet0805_cache : checkStripCache packet0805 = true := by
  decide +kernel

private theorem packet0805_pair (i : Fin 7) : checkEdgePair packet0805 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0805_ok : checkStripPacket packet0805 = true :=
  checkStripPacket_intro packet0805_shape packet0805_cache packet0805_pair

theorem packet0806_membership : packet0806 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0806_shape : checkStripShape packet0806.row = true := by
  decide +kernel

private theorem packet0806_cache : checkStripCache packet0806 = true := by
  decide +kernel

private theorem packet0806_pair (i : Fin 7) : checkEdgePair packet0806 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0806_ok : checkStripPacket packet0806 = true :=
  checkStripPacket_intro packet0806_shape packet0806_cache packet0806_pair

theorem packet0807_membership : packet0807 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0807_shape : checkStripShape packet0807.row = true := by
  decide +kernel

private theorem packet0807_cache : checkStripCache packet0807 = true := by
  decide +kernel

private theorem packet0807_pair (i : Fin 7) : checkEdgePair packet0807 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0807_ok : checkStripPacket packet0807 = true :=
  checkStripPacket_intro packet0807_shape packet0807_cache packet0807_pair

theorem packet0808_membership : packet0808 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0808_shape : checkStripShape packet0808.row = true := by
  decide +kernel

private theorem packet0808_cache : checkStripCache packet0808 = true := by
  decide +kernel

private theorem packet0808_pair (i : Fin 7) : checkEdgePair packet0808 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0808_ok : checkStripPacket packet0808 = true :=
  checkStripPacket_intro packet0808_shape packet0808_cache packet0808_pair

theorem packet0809_membership : packet0809 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0809_shape : checkStripShape packet0809.row = true := by
  decide +kernel

private theorem packet0809_cache : checkStripCache packet0809 = true := by
  decide +kernel

private theorem packet0809_pair (i : Fin 7) : checkEdgePair packet0809 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0809_ok : checkStripPacket packet0809 = true :=
  checkStripPacket_intro packet0809_shape packet0809_cache packet0809_pair

theorem packet0810_membership : packet0810 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0810_shape : checkStripShape packet0810.row = true := by
  decide +kernel

private theorem packet0810_cache : checkStripCache packet0810 = true := by
  decide +kernel

private theorem packet0810_pair (i : Fin 7) : checkEdgePair packet0810 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0810_ok : checkStripPacket packet0810 = true :=
  checkStripPacket_intro packet0810_shape packet0810_cache packet0810_pair

theorem packet0811_membership : packet0811 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0811_shape : checkStripShape packet0811.row = true := by
  decide +kernel

private theorem packet0811_cache : checkStripCache packet0811 = true := by
  decide +kernel

private theorem packet0811_pair (i : Fin 7) : checkEdgePair packet0811 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0811_ok : checkStripPacket packet0811 = true :=
  checkStripPacket_intro packet0811_shape packet0811_cache packet0811_pair

theorem packet0812_membership : packet0812 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0812_shape : checkStripShape packet0812.row = true := by
  decide +kernel

private theorem packet0812_cache : checkStripCache packet0812 = true := by
  decide +kernel

private theorem packet0812_pair (i : Fin 7) : checkEdgePair packet0812 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0812_ok : checkStripPacket packet0812 = true :=
  checkStripPacket_intro packet0812_shape packet0812_cache packet0812_pair

theorem packet0813_membership : packet0813 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0813_shape : checkStripShape packet0813.row = true := by
  decide +kernel

private theorem packet0813_cache : checkStripCache packet0813 = true := by
  decide +kernel

private theorem packet0813_pair (i : Fin 7) : checkEdgePair packet0813 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0813_ok : checkStripPacket packet0813 = true :=
  checkStripPacket_intro packet0813_shape packet0813_cache packet0813_pair

theorem packet0814_membership : packet0814 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0814_shape : checkStripShape packet0814.row = true := by
  decide +kernel

private theorem packet0814_cache : checkStripCache packet0814 = true := by
  decide +kernel

private theorem packet0814_pair (i : Fin 7) : checkEdgePair packet0814 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0814_ok : checkStripPacket packet0814 = true :=
  checkStripPacket_intro packet0814_shape packet0814_cache packet0814_pair

theorem packet0815_membership : packet0815 ∈ packets033 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0815_shape : checkStripShape packet0815.row = true := by
  decide +kernel

private theorem packet0815_cache : checkStripCache packet0815 = true := by
  decide +kernel

private theorem packet0815_pair (i : Fin 7) : checkEdgePair packet0815 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0815_ok : checkStripPacket packet0815 = true :=
  checkStripPacket_intro packet0815_shape packet0815_cache packet0815_pair

theorem packets033_checked : packets033.all checkStripPacket = true := by
  simp only [packets033, List.all_cons, List.all_nil, Bool.true_and, packet0792_ok,
    packet0793_ok, packet0794_ok, packet0795_ok, packet0796_ok, packet0797_ok,
    packet0798_ok, packet0799_ok, packet0800_ok, packet0801_ok, packet0802_ok,
    packet0803_ok, packet0804_ok, packet0805_ok, packet0806_ok, packet0807_ok,
    packet0808_ok, packet0809_ok, packet0810_ok, packet0811_ok, packet0812_ok,
    packet0813_ok, packet0814_ok, packet0815_ok]

theorem packets033_valid : packets033.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
