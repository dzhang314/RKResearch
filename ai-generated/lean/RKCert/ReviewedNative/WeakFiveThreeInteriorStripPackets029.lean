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

def packet0696 : StripRowPacket :=
  ⟨⟨⟨6,16,4,7⟩,
    ![432,1374,2676,4160,5631,6895,7789],![458,1437,2764,4251,5703,6939,7805]⟩,
    ⟨-985758569575747819,504955469662764989440⟩,
    ⟨137947273292907417,8779615459241191685120⟩⟩

def packet0697 : StripRowPacket :=
  ⟨⟨⟨6,17,4,6⟩,
    ![406,1314,2599,4087,5577,6865,7779],![438,1384,2689,4173,5641,6903,7793]⟩,
    ⟨-2423430149547924029682501,653214295918314851771674624⟩,
    ⟨-1495650697206846150734705,872649462001401442693001216⟩⟩

def packet0698 : StripRowPacket :=
  ⟨⟨⟨6,17,4,7⟩,
    ![429,1369,2671,4155,5627,6893,7788],![456,1431,2758,4246,5700,6937,7805]⟩,
    ⟨-33583359446207461469989,16966605088787398747316224⟩,
    ⟨24367579411095386241437,1418055375752277344376126976⟩⟩

def packet0699 : StripRowPacket :=
  ⟨⟨⟨5,9,4,4⟩,
    ![328,1168,2441,3953,5484,6817,7764],![384,1264,2540,4035,5541,6848,7775]⟩,
    ⟨-617356865313968761045,82450972193578299790336⟩,
    ⟨-3082622691643854841,593721644402366425088⟩⟩

def packet0700 : StripRowPacket :=
  ⟨⟨⟨5,9,4,5⟩,
    ![371,1240,2512,4011,5523,6837,7770],![414,1327,2615,4102,5588,6873,7783]⟩,
    ⟨-1882553224319297373289,329803888774313199161344⟩,
    ⟨-77907362711666379,22835447861629477888⟩⟩

def packet0701 : StripRowPacket :=
  ⟨⟨⟨5,9,4,6⟩,
    ![401,1303,2584,4074,5567,6860,7777],![436,1382,2688,4172,5641,6902,7793]⟩,
    ⟨-647839493691359851199,164901944387156599580672⟩,
    ⟨-968560169362796867,593721644402366425088⟩⟩

def packet0702 : StripRowPacket :=
  ⟨⟨⟨5,9,4,7⟩,
    ![424,1357,2655,4141,5617,6888,7786],![454,1429,2757,4246,5700,6938,7805]⟩,
    ⟨-708804750446142031507,329803888774313199161344⟩,
    ⟨11058886472216515,74215205550295803136⟩⟩

def packet0703 : StripRowPacket :=
  ⟨⟨⟨5,10,4,0⟩,
    ![0,874,2193,3768,5365,6756,7745],![146,966,2262,3819,5400,6775,7753]⟩,
    ⟨-268482747139,17777809608416⟩,
    ⟨-6419890106604178500631,503077448107049310736384⟩⟩

def packet0704 : StripRowPacket :=
  ⟨⟨⟨5,10,4,1⟩,
    ![90,936,2242,3804,5388,6768,7748],![232,1038,2320,3861,5427,6789,7757]⟩,
    ⟨-1011701194275369679,76304375812629772288⟩,
    ⟨-2746061322457176537239,251538724053524655368192⟩⟩

def packet0705 : StripRowPacket :=
  ⟨⟨⟨5,11,4,0⟩,
    ![0,868,2183,3758,5358,6752,7743],![144,959,2251,3808,5392,6771,7751]⟩,
    ⟨-337682727,21666107320⟩,
    ⟨-24122948816439052351,1828062295313275141120⟩⟩

def packet0706 : StripRowPacket :=
  ⟨⟨⟨5,11,4,1⟩,
    ![91,930,2232,3794,5381,6763,7747],![230,1031,2309,3851,5419,6784,7756]⟩,
    ⟨-328939700186997549913,24044765986226536984576⟩,
    ⟨-10319133897794964111,914031147656637570560⟩⟩

def packet0707 : StripRowPacket :=
  ⟨⟨⟨5,10,4,2⟩,
    ![192,1007,2298,3845,5414,6781,7752],![296,1113,2384,3910,5457,6804,7762]⟩,
    ⟨-4790741874831617733,419674066969463747584⟩,
    ⟨-4564355183224527648325,503077448107049310736384⟩⟩

def packet0708 : StripRowPacket :=
  ⟨⟨⟨5,10,4,3⟩,
    ![269,1084,2362,3891,5443,6795,7757],![344,1186,2454,3964,5493,6822,7767]⟩,
    ⟨-8034254362297404463,839348133938927495168⟩,
    ⟨-909146930383675555543,125769362026762327684096⟩⟩

def packet0709 : StripRowPacket :=
  ⟨⟨⟨5,11,4,2⟩,
    ![192,1001,2289,3835,5407,6776,7751],![294,1106,2374,3899,5450,6800,7760]⟩,
    ⟨-64346243790053507671,5464719542324212951040⟩,
    ⟨-17153586774740804093,1828062295313275141120⟩⟩

def packet0710 : StripRowPacket :=
  ⟨⟨⟨5,11,4,3⟩,
    ![268,1078,2352,3882,5436,6792,7756],![342,1179,2444,3954,5485,6818,7766]⟩,
    ⟨-1186536225827366587959,120223829931132684922880⟩,
    ⟨-3417226438472919991,457015573828318785280⟩⟩

def packet0711 : StripRowPacket :=
  ⟨⟨⟨5,10,4,4⟩,
    ![326,1161,2431,3943,5477,6813,7762],![380,1255,2528,4025,5533,6844,7774]⟩,
    ⟨-1621756243732893365,209837033484731873792⟩,
    ⟨-2708820259844876796019,503077448107049310736384⟩⟩

def packet0712 : StripRowPacket :=
  ⟨⟨⟨5,10,4,5⟩,
    ![368,1233,2502,4001,5516,6833,7769],![410,1318,2603,4091,5580,6869,7782]⟩,
    ⟨-4939795587565742457,839348133938927495168⟩,
    ⟨-890526399077525684933,251538724053524655368192⟩⟩

def packet0713 : StripRowPacket :=
  ⟨⟨⟨5,11,4,4⟩,
    ![324,1155,2422,3934,5470,6809,7761],![378,1247,2518,4015,5526,6840,7773]⟩,
    ⟨-239363772068389001789,30055957482783171230720⟩,
    ⟨-2036844946608511167,365612459062655028224⟩⟩

def packet0714 : StripRowPacket :=
  ⟨⟨⟨5,11,4,5⟩,
    ![365,1227,2494,3992,5509,6829,7767],![406,1310,2593,4081,5573,6865,7781]⟩,
    ⟨-728373950719745426353,120223829931132684922880⟩,
    ⟨-3349771856096715853,914031147656637570560⟩⟩

def packet0715 : StripRowPacket :=
  ⟨⟨⟨5,10,4,6⟩,
    ![398,1295,2575,4065,5560,6856,7776],![432,1373,2676,4162,5633,6898,7792]⟩,
    ⟨-1696283100099955727,419674066969463747584⟩,
    ⟨-853285336465225943713,503077448107049310736384⟩⟩

def packet0716 : StripRowPacket :=
  ⟨⟨⟨5,10,4,7⟩,
    ![421,1350,2646,4132,5610,6884,7785],![450,1419,2745,4235,5693,6934,7804]⟩,
    ⟨-1845336812834080451,839348133938927495168⟩,
    ⟨9310265653074935305,62884681013381163842048⟩⟩

def packet0717 : StripRowPacket :=
  ⟨⟨⟨5,11,4,6⟩,
    ![396,1289,2566,4056,5554,6853,7775],![429,1364,2665,4152,5626,6894,7791]⟩,
    ⟨-49929281316593484555,12022382993113268492288⟩,
    ⟨-459266098763472511,261151756473325020160⟩⟩

def packet0718 : StripRowPacket :=
  ⟨⟨⟨5,11,4,7⟩,
    ![418,1343,2637,4124,5604,6881,7784],![446,1411,2734,4225,5686,6930,7803]⟩,
    ⟨-270211675612124264747,120223829931132684922880⟩,
    ⟨33727291188102069,228507786914159392640⟩⟩

def packet0719 : StripRowPacket :=
  ⟨⟨⟨6,16,4,8⟩,
    ![450,1421,2744,4231,5687,6928,7800],![473,1477,2828,4324,5768,6980,7820]⟩,
    ⟨-16101893722030607,63119433707845623680⟩,
    ⟨120335653515322113889,70236923673929533480960⟩⟩

def packets029 : List StripRowPacket :=
  [packet0696, packet0697, packet0698, packet0699, packet0700, packet0701,
   packet0702, packet0703, packet0704, packet0705, packet0706, packet0707,
   packet0708, packet0709, packet0710, packet0711, packet0712, packet0713,
   packet0714, packet0715, packet0716, packet0717, packet0718, packet0719]

theorem packet0696_membership : packet0696 ∈ packets029 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0696_shape : checkStripShape packet0696.row = true := by
  decide +kernel

private theorem packet0696_cache : checkStripCache packet0696 = true := by
  decide +kernel

private theorem packet0696_pair (i : Fin 7) : checkEdgePair packet0696 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0696_ok : checkStripPacket packet0696 = true :=
  checkStripPacket_intro packet0696_shape packet0696_cache packet0696_pair

theorem packet0697_membership : packet0697 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0697_shape : checkStripShape packet0697.row = true := by
  decide +kernel

private theorem packet0697_cache : checkStripCache packet0697 = true := by
  decide +kernel

private theorem packet0697_pair (i : Fin 7) : checkEdgePair packet0697 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0697_ok : checkStripPacket packet0697 = true :=
  checkStripPacket_intro packet0697_shape packet0697_cache packet0697_pair

theorem packet0698_membership : packet0698 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0698_shape : checkStripShape packet0698.row = true := by
  decide +kernel

private theorem packet0698_cache : checkStripCache packet0698 = true := by
  decide +kernel

private theorem packet0698_pair (i : Fin 7) : checkEdgePair packet0698 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0698_ok : checkStripPacket packet0698 = true :=
  checkStripPacket_intro packet0698_shape packet0698_cache packet0698_pair

theorem packet0699_membership : packet0699 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0699_shape : checkStripShape packet0699.row = true := by
  decide +kernel

private theorem packet0699_cache : checkStripCache packet0699 = true := by
  decide +kernel

private theorem packet0699_pair (i : Fin 7) : checkEdgePair packet0699 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0699_ok : checkStripPacket packet0699 = true :=
  checkStripPacket_intro packet0699_shape packet0699_cache packet0699_pair

theorem packet0700_membership : packet0700 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0700_shape : checkStripShape packet0700.row = true := by
  decide +kernel

private theorem packet0700_cache : checkStripCache packet0700 = true := by
  decide +kernel

private theorem packet0700_pair (i : Fin 7) : checkEdgePair packet0700 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0700_ok : checkStripPacket packet0700 = true :=
  checkStripPacket_intro packet0700_shape packet0700_cache packet0700_pair

theorem packet0701_membership : packet0701 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0701_shape : checkStripShape packet0701.row = true := by
  decide +kernel

private theorem packet0701_cache : checkStripCache packet0701 = true := by
  decide +kernel

private theorem packet0701_pair (i : Fin 7) : checkEdgePair packet0701 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0701_ok : checkStripPacket packet0701 = true :=
  checkStripPacket_intro packet0701_shape packet0701_cache packet0701_pair

theorem packet0702_membership : packet0702 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0702_shape : checkStripShape packet0702.row = true := by
  decide +kernel

private theorem packet0702_cache : checkStripCache packet0702 = true := by
  decide +kernel

private theorem packet0702_pair (i : Fin 7) : checkEdgePair packet0702 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0702_ok : checkStripPacket packet0702 = true :=
  checkStripPacket_intro packet0702_shape packet0702_cache packet0702_pair

theorem packet0703_membership : packet0703 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0703_shape : checkStripShape packet0703.row = true := by
  decide +kernel

private theorem packet0703_cache : checkStripCache packet0703 = true := by
  decide +kernel

private theorem packet0703_pair (i : Fin 7) : checkEdgePair packet0703 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0703_ok : checkStripPacket packet0703 = true :=
  checkStripPacket_intro packet0703_shape packet0703_cache packet0703_pair

theorem packet0704_membership : packet0704 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0704_shape : checkStripShape packet0704.row = true := by
  decide +kernel

private theorem packet0704_cache : checkStripCache packet0704 = true := by
  decide +kernel

private theorem packet0704_pair (i : Fin 7) : checkEdgePair packet0704 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0704_ok : checkStripPacket packet0704 = true :=
  checkStripPacket_intro packet0704_shape packet0704_cache packet0704_pair

theorem packet0705_membership : packet0705 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0705_shape : checkStripShape packet0705.row = true := by
  decide +kernel

private theorem packet0705_cache : checkStripCache packet0705 = true := by
  decide +kernel

private theorem packet0705_pair (i : Fin 7) : checkEdgePair packet0705 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0705_ok : checkStripPacket packet0705 = true :=
  checkStripPacket_intro packet0705_shape packet0705_cache packet0705_pair

theorem packet0706_membership : packet0706 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0706_shape : checkStripShape packet0706.row = true := by
  decide +kernel

private theorem packet0706_cache : checkStripCache packet0706 = true := by
  decide +kernel

private theorem packet0706_pair (i : Fin 7) : checkEdgePair packet0706 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0706_ok : checkStripPacket packet0706 = true :=
  checkStripPacket_intro packet0706_shape packet0706_cache packet0706_pair

theorem packet0707_membership : packet0707 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0707_shape : checkStripShape packet0707.row = true := by
  decide +kernel

private theorem packet0707_cache : checkStripCache packet0707 = true := by
  decide +kernel

private theorem packet0707_pair (i : Fin 7) : checkEdgePair packet0707 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0707_ok : checkStripPacket packet0707 = true :=
  checkStripPacket_intro packet0707_shape packet0707_cache packet0707_pair

theorem packet0708_membership : packet0708 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0708_shape : checkStripShape packet0708.row = true := by
  decide +kernel

private theorem packet0708_cache : checkStripCache packet0708 = true := by
  decide +kernel

private theorem packet0708_pair (i : Fin 7) : checkEdgePair packet0708 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0708_ok : checkStripPacket packet0708 = true :=
  checkStripPacket_intro packet0708_shape packet0708_cache packet0708_pair

theorem packet0709_membership : packet0709 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0709_shape : checkStripShape packet0709.row = true := by
  decide +kernel

private theorem packet0709_cache : checkStripCache packet0709 = true := by
  decide +kernel

private theorem packet0709_pair (i : Fin 7) : checkEdgePair packet0709 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0709_ok : checkStripPacket packet0709 = true :=
  checkStripPacket_intro packet0709_shape packet0709_cache packet0709_pair

theorem packet0710_membership : packet0710 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0710_shape : checkStripShape packet0710.row = true := by
  decide +kernel

private theorem packet0710_cache : checkStripCache packet0710 = true := by
  decide +kernel

private theorem packet0710_pair (i : Fin 7) : checkEdgePair packet0710 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0710_ok : checkStripPacket packet0710 = true :=
  checkStripPacket_intro packet0710_shape packet0710_cache packet0710_pair

theorem packet0711_membership : packet0711 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0711_shape : checkStripShape packet0711.row = true := by
  decide +kernel

private theorem packet0711_cache : checkStripCache packet0711 = true := by
  decide +kernel

private theorem packet0711_pair (i : Fin 7) : checkEdgePair packet0711 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0711_ok : checkStripPacket packet0711 = true :=
  checkStripPacket_intro packet0711_shape packet0711_cache packet0711_pair

theorem packet0712_membership : packet0712 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0712_shape : checkStripShape packet0712.row = true := by
  decide +kernel

private theorem packet0712_cache : checkStripCache packet0712 = true := by
  decide +kernel

private theorem packet0712_pair (i : Fin 7) : checkEdgePair packet0712 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0712_ok : checkStripPacket packet0712 = true :=
  checkStripPacket_intro packet0712_shape packet0712_cache packet0712_pair

theorem packet0713_membership : packet0713 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0713_shape : checkStripShape packet0713.row = true := by
  decide +kernel

private theorem packet0713_cache : checkStripCache packet0713 = true := by
  decide +kernel

private theorem packet0713_pair (i : Fin 7) : checkEdgePair packet0713 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0713_ok : checkStripPacket packet0713 = true :=
  checkStripPacket_intro packet0713_shape packet0713_cache packet0713_pair

theorem packet0714_membership : packet0714 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0714_shape : checkStripShape packet0714.row = true := by
  decide +kernel

private theorem packet0714_cache : checkStripCache packet0714 = true := by
  decide +kernel

private theorem packet0714_pair (i : Fin 7) : checkEdgePair packet0714 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0714_ok : checkStripPacket packet0714 = true :=
  checkStripPacket_intro packet0714_shape packet0714_cache packet0714_pair

theorem packet0715_membership : packet0715 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0715_shape : checkStripShape packet0715.row = true := by
  decide +kernel

private theorem packet0715_cache : checkStripCache packet0715 = true := by
  decide +kernel

private theorem packet0715_pair (i : Fin 7) : checkEdgePair packet0715 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0715_ok : checkStripPacket packet0715 = true :=
  checkStripPacket_intro packet0715_shape packet0715_cache packet0715_pair

theorem packet0716_membership : packet0716 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0716_shape : checkStripShape packet0716.row = true := by
  decide +kernel

private theorem packet0716_cache : checkStripCache packet0716 = true := by
  decide +kernel

private theorem packet0716_pair (i : Fin 7) : checkEdgePair packet0716 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0716_ok : checkStripPacket packet0716 = true :=
  checkStripPacket_intro packet0716_shape packet0716_cache packet0716_pair

theorem packet0717_membership : packet0717 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0717_shape : checkStripShape packet0717.row = true := by
  decide +kernel

private theorem packet0717_cache : checkStripCache packet0717 = true := by
  decide +kernel

private theorem packet0717_pair (i : Fin 7) : checkEdgePair packet0717 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0717_ok : checkStripPacket packet0717 = true :=
  checkStripPacket_intro packet0717_shape packet0717_cache packet0717_pair

theorem packet0718_membership : packet0718 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0718_shape : checkStripShape packet0718.row = true := by
  decide +kernel

private theorem packet0718_cache : checkStripCache packet0718 = true := by
  decide +kernel

private theorem packet0718_pair (i : Fin 7) : checkEdgePair packet0718 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0718_ok : checkStripPacket packet0718 = true :=
  checkStripPacket_intro packet0718_shape packet0718_cache packet0718_pair

theorem packet0719_membership : packet0719 ∈ packets029 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0719_shape : checkStripShape packet0719.row = true := by
  decide +kernel

private theorem packet0719_cache : checkStripCache packet0719 = true := by
  decide +kernel

private theorem packet0719_pair (i : Fin 7) : checkEdgePair packet0719 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0719_ok : checkStripPacket packet0719 = true :=
  checkStripPacket_intro packet0719_shape packet0719_cache packet0719_pair

theorem packets029_checked : packets029.all checkStripPacket = true := by
  simp only [packets029, List.all_cons, List.all_nil, Bool.true_and, packet0696_ok,
    packet0697_ok, packet0698_ok, packet0699_ok, packet0700_ok, packet0701_ok,
    packet0702_ok, packet0703_ok, packet0704_ok, packet0705_ok, packet0706_ok,
    packet0707_ok, packet0708_ok, packet0709_ok, packet0710_ok, packet0711_ok,
    packet0712_ok, packet0713_ok, packet0714_ok, packet0715_ok, packet0716_ok,
    packet0717_ok, packet0718_ok, packet0719_ok]

theorem packets029_valid : packets029.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
