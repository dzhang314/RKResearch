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

def packet0888 : StripRowPacket :=
  ⟨⟨⟨5,21,4,5⟩,
    ![352,1186,2431,3926,5456,6798,7757],![387,1260,2521,4008,5516,6832,7770]⟩,
    ⟨-99171671470757349471757,12989975660210578367303680⟩,
    ⟨-927059405567801133009,194595693881025337472000⟩⟩

def packet0889 : StripRowPacket :=
  ⟨⟨⟨5,20,4,6⟩,
    ![381,1250,2509,3996,5507,6826,7766],![409,1316,2598,4085,5575,6865,7781]⟩,
    ⟨-100537217563636915761,19800707526449417165312⟩,
    ⟨-21402968815742387231,9500246795864876699648⟩⟩

def packet0890 : StripRowPacket :=
  ⟨⟨⟨5,20,4,7⟩,
    ![402,1302,2579,4065,5559,6855,7775],![425,1360,2666,4158,5635,6902,7793]⟩,
    ⟨-105666025131836164813,39601415052898834330624⟩,
    ⟨186333408381801495,1187530849483109587456⟩⟩

def packet0891 : StripRowPacket :=
  ⟨⟨⟨5,21,4,6⟩,
    ![380,1247,2504,3991,5502,6823,7765],![408,1312,2593,4079,5570,6863,7780]⟩,
    ⟨-6720483407893885799359,1298997566021057836730368⟩,
    ⟨-896141684597736901021,389191387762050674944000⟩⟩

def packet0892 : StripRowPacket :=
  ⟨⟨⟨5,21,4,7⟩,
    ![401,1299,2575,4060,5554,6852,7775],![424,1356,2660,4153,5631,6899,7792]⟩,
    ⟨-35237996687120366515423,12989975660210578367303680⟩,
    ⟨7729430242516057997,48648923470256334368000⟩⟩

def packet0893 : StripRowPacket :=
  ⟨⟨⟨5,22,4,4⟩,
    ![313,1114,2353,3861,5411,6774,7749],![360,1197,2442,3935,5464,6804,7761]⟩,
    ⟨-2751134887425901420069,267294361413663483328000⟩,
    ⟨-272938015372335638182489,37001144292973039515381760⟩⟩

def packet0894 : StripRowPacket :=
  ⟨⟨⟨5,22,4,5⟩,
    ![351,1183,2427,3921,5452,6795,7756],![386,1257,2516,4002,5511,6829,7769]⟩,
    ⟨-1663770065918360273589,213835489130930786662400⟩,
    ⟨-6922045254133241165003,1423120934345116904437760⟩⟩

def packet0895 : StripRowPacket :=
  ⟨⟨⟨5,23,4,4⟩,
    ![312,1111,2349,3856,5407,6771,7748],![359,1194,2437,3930,5459,6801,7760]⟩,
    ⟨-146992429140398720729,14015926821839986334720⟩,
    ⟨-1577684422299950883,209642866703979554560⟩⟩

def packet0896 : StripRowPacket :=
  ⟨⟨⟨5,23,4,5⟩,
    ![350,1180,2422,3916,5447,6793,7755],![385,1254,2511,3997,5507,6827,7768]⟩,
    ⟨-88862794076431700441,11212741457471989067776⟩,
    ⟨-104038521576169205,20964286670397955456⟩⟩

def packet0897 : StripRowPacket :=
  ⟨⟨⟨5,22,4,6⟩,
    ![379,1244,2499,3986,5498,6820,7764],![406,1308,2588,4074,5566,6860,7779]⟩,
    ⟨-2816580554739998527807,534588722827326966656000⟩,
    ⟨-87008337842592902397667,37001144292973039515381760⟩⟩

def packet0898 : StripRowPacket :=
  ⟨⟨⟨5,22,4,7⟩,
    ![400,1296,2570,4055,5550,6850,7774],![423,1353,2655,4147,5626,6896,7792]⟩,
    ⟨-2947471889368192743283,1069177445654653933312000⟩,
    ⟨744562615284808186843,4625143036621629939422720⟩⟩

def packet0899 : StripRowPacket :=
  ⟨⟨⟨5,23,4,6⟩,
    ![378,1241,2495,3981,5494,6818,7763],![405,1305,2583,4068,5561,6857,7778]⟩,
    ⟨-13666282918305550977,2548350331243633879040⟩,
    ⟨-503086009223433217,209642866703979554560⟩⟩

def packet0900 : StripRowPacket :=
  ⟨⟨⟨5,23,4,7⟩,
    ![399,1293,2566,4050,5546,6847,7773],![421,1349,2650,4142,5622,6894,7791]⟩,
    ⟨-157002478023285740783,56063707287359945338880⟩,
    ⟨2138324832176601,13102679168998722160⟩⟩

def packet0901 : StripRowPacket :=
  ⟨⟨⟨6,32,4,8⟩,
    ![426,1366,2675,4167,5640,6903,7792],![445,1414,2750,4254,5718,6953,7812]⟩,
    ⟨-4500393431934577,24706417090328914304⟩,
    ⟨2300425630673867617,1035588103252734107648⟩⟩

def packet0902 : StripRowPacket :=
  ⟨⟨⟨6,33,4,8⟩,
    ![425,1364,2671,4163,5638,6901,7791],![444,1411,2746,4250,5715,6952,7811]⟩,
    ⟨-442864680269017187001687,2477691786052925794103065600⟩,
    ⟨54807749553420177309690291,24353577481576049598225551360⟩⟩

def packet0903 : StripRowPacket :=
  ⟨⟨⟨6,32,4,9⟩,
    ![439,1404,2737,4239,5704,6944,7806],![456,1446,2806,4325,5788,7003,7831]⟩,
    ⟨621024353010874845,310594957706992065536⟩,
    ⟨175385018408308913,39830311663566696448⟩⟩

def packet0904 : StripRowPacket :=
  ⟨⟨⟨6,33,4,9⟩,
    ![439,1402,2733,4236,5702,6942,7806],![455,1444,2802,4321,5785,7001,7831]⟩,
    ⟨40246939417731215683060241,19821534288423406352824524800⟩,
    ⟨76032131770099658838254749,17047504237103234718757885952⟩⟩

def packet0905 : StripRowPacket :=
  ⟨⟨⟨6,34,4,8⟩,
    ![424,1362,2668,4160,5635,6900,7791],![443,1409,2743,4247,5712,6950,7811]⟩,
    ⟨-19250853823918814218391,109755968165390619948254720⟩,
    ⟨894802401492153931394566411,392558276073209254600595660800⟩⟩

def packet0906 : StripRowPacket :=
  ⟨⟨⟨6,35,4,8⟩,
    ![423,1359,2665,4157,5633,6899,7790],![442,1407,2740,4244,5710,6949,7810]⟩,
    ⟨-149887791100701252132109,870846210088406507953986560⟩,
    ⟨239117077098093204860407,103598345325099757555005440⟩⟩

def packet0907 : StripRowPacket :=
  ⟨⟨⟨6,34,4,9⟩,
    ![438,1400,2730,4233,5700,6941,7805],![454,1441,2799,4318,5783,7000,7830]⟩,
    ⟨23527422420974332516467413,11414620689200624474618490880⟩,
    ⟨80586503489494588737302429,17843558003327693390936166400⟩⟩

def packet0908 : StripRowPacket :=
  ⟨⟨⟨6,35,4,9⟩,
    ![437,1397,2727,4230,5697,6940,7805],![453,1439,2795,4315,5780,6999,7830]⟩,
    ⟨14571573940996068518984907,6966769680707252063631892480⟩,
    ⟨47366387683452049547119,10359834532509975755500544⟩⟩

def packet0909 : StripRowPacket :=
  ⟨⟨⟨6,32,4,10⟩,
    ![450,1437,2792,4310,5773,6992,7825],![465,1474,2855,4392,5860,7061,7857]⟩,
    ⟨4545187782081245303,1087082351974472229376⟩,
    ⟨6819595326558195859,1035588103252734107648⟩⟩

def packet0910 : StripRowPacket :=
  ⟨⟨⟨6,33,4,10⟩,
    ![449,1434,2789,4306,5771,6991,7825],![464,1471,2851,4389,5858,7060,7856]⟩,
    ⟨42018398138807284431066989,9910767144211703176412262400⟩,
    ⟨1136988388528051935597262943,170475042371032347187578859520⟩⟩

def packet0911 : StripRowPacket :=
  ⟨⟨⟨6,32,4,11⟩,
    ![460,1464,2842,4377,5845,7048,7849],![472,1497,2898,4454,5933,7127,7891]⟩,
    ⟨1064121589019142869,167243438765303419904⟩,
    ⟨2269795043625089995,258897025813183526912⟩⟩

def packets037 : List StripRowPacket :=
  [packet0888, packet0889, packet0890, packet0891, packet0892, packet0893,
   packet0894, packet0895, packet0896, packet0897, packet0898, packet0899,
   packet0900, packet0901, packet0902, packet0903, packet0904, packet0905,
   packet0906, packet0907, packet0908, packet0909, packet0910, packet0911]

theorem packet0888_membership : packet0888 ∈ packets037 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0888_shape : checkStripShape packet0888.row = true := by
  decide +kernel

private theorem packet0888_cache : checkStripCache packet0888 = true := by
  decide +kernel

private theorem packet0888_pair (i : Fin 7) : checkEdgePair packet0888 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0888_ok : checkStripPacket packet0888 = true :=
  checkStripPacket_intro packet0888_shape packet0888_cache packet0888_pair

theorem packet0889_membership : packet0889 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0889_shape : checkStripShape packet0889.row = true := by
  decide +kernel

private theorem packet0889_cache : checkStripCache packet0889 = true := by
  decide +kernel

private theorem packet0889_pair (i : Fin 7) : checkEdgePair packet0889 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0889_ok : checkStripPacket packet0889 = true :=
  checkStripPacket_intro packet0889_shape packet0889_cache packet0889_pair

theorem packet0890_membership : packet0890 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0890_shape : checkStripShape packet0890.row = true := by
  decide +kernel

private theorem packet0890_cache : checkStripCache packet0890 = true := by
  decide +kernel

private theorem packet0890_pair (i : Fin 7) : checkEdgePair packet0890 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0890_ok : checkStripPacket packet0890 = true :=
  checkStripPacket_intro packet0890_shape packet0890_cache packet0890_pair

theorem packet0891_membership : packet0891 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0891_shape : checkStripShape packet0891.row = true := by
  decide +kernel

private theorem packet0891_cache : checkStripCache packet0891 = true := by
  decide +kernel

private theorem packet0891_pair (i : Fin 7) : checkEdgePair packet0891 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0891_ok : checkStripPacket packet0891 = true :=
  checkStripPacket_intro packet0891_shape packet0891_cache packet0891_pair

theorem packet0892_membership : packet0892 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0892_shape : checkStripShape packet0892.row = true := by
  decide +kernel

private theorem packet0892_cache : checkStripCache packet0892 = true := by
  decide +kernel

private theorem packet0892_pair (i : Fin 7) : checkEdgePair packet0892 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0892_ok : checkStripPacket packet0892 = true :=
  checkStripPacket_intro packet0892_shape packet0892_cache packet0892_pair

theorem packet0893_membership : packet0893 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0893_shape : checkStripShape packet0893.row = true := by
  decide +kernel

private theorem packet0893_cache : checkStripCache packet0893 = true := by
  decide +kernel

private theorem packet0893_pair (i : Fin 7) : checkEdgePair packet0893 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0893_ok : checkStripPacket packet0893 = true :=
  checkStripPacket_intro packet0893_shape packet0893_cache packet0893_pair

theorem packet0894_membership : packet0894 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0894_shape : checkStripShape packet0894.row = true := by
  decide +kernel

private theorem packet0894_cache : checkStripCache packet0894 = true := by
  decide +kernel

private theorem packet0894_pair (i : Fin 7) : checkEdgePair packet0894 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0894_ok : checkStripPacket packet0894 = true :=
  checkStripPacket_intro packet0894_shape packet0894_cache packet0894_pair

theorem packet0895_membership : packet0895 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0895_shape : checkStripShape packet0895.row = true := by
  decide +kernel

private theorem packet0895_cache : checkStripCache packet0895 = true := by
  decide +kernel

private theorem packet0895_pair (i : Fin 7) : checkEdgePair packet0895 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0895_ok : checkStripPacket packet0895 = true :=
  checkStripPacket_intro packet0895_shape packet0895_cache packet0895_pair

theorem packet0896_membership : packet0896 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0896_shape : checkStripShape packet0896.row = true := by
  decide +kernel

private theorem packet0896_cache : checkStripCache packet0896 = true := by
  decide +kernel

private theorem packet0896_pair (i : Fin 7) : checkEdgePair packet0896 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0896_ok : checkStripPacket packet0896 = true :=
  checkStripPacket_intro packet0896_shape packet0896_cache packet0896_pair

theorem packet0897_membership : packet0897 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0897_shape : checkStripShape packet0897.row = true := by
  decide +kernel

private theorem packet0897_cache : checkStripCache packet0897 = true := by
  decide +kernel

private theorem packet0897_pair (i : Fin 7) : checkEdgePair packet0897 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0897_ok : checkStripPacket packet0897 = true :=
  checkStripPacket_intro packet0897_shape packet0897_cache packet0897_pair

theorem packet0898_membership : packet0898 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0898_shape : checkStripShape packet0898.row = true := by
  decide +kernel

private theorem packet0898_cache : checkStripCache packet0898 = true := by
  decide +kernel

private theorem packet0898_pair (i : Fin 7) : checkEdgePair packet0898 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0898_ok : checkStripPacket packet0898 = true :=
  checkStripPacket_intro packet0898_shape packet0898_cache packet0898_pair

theorem packet0899_membership : packet0899 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0899_shape : checkStripShape packet0899.row = true := by
  decide +kernel

private theorem packet0899_cache : checkStripCache packet0899 = true := by
  decide +kernel

private theorem packet0899_pair (i : Fin 7) : checkEdgePair packet0899 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0899_ok : checkStripPacket packet0899 = true :=
  checkStripPacket_intro packet0899_shape packet0899_cache packet0899_pair

theorem packet0900_membership : packet0900 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0900_shape : checkStripShape packet0900.row = true := by
  decide +kernel

private theorem packet0900_cache : checkStripCache packet0900 = true := by
  decide +kernel

private theorem packet0900_pair (i : Fin 7) : checkEdgePair packet0900 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0900_ok : checkStripPacket packet0900 = true :=
  checkStripPacket_intro packet0900_shape packet0900_cache packet0900_pair

theorem packet0901_membership : packet0901 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0901_shape : checkStripShape packet0901.row = true := by
  decide +kernel

private theorem packet0901_cache : checkStripCache packet0901 = true := by
  decide +kernel

private theorem packet0901_pair (i : Fin 7) : checkEdgePair packet0901 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0901_ok : checkStripPacket packet0901 = true :=
  checkStripPacket_intro packet0901_shape packet0901_cache packet0901_pair

theorem packet0902_membership : packet0902 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0902_shape : checkStripShape packet0902.row = true := by
  decide +kernel

private theorem packet0902_cache : checkStripCache packet0902 = true := by
  decide +kernel

private theorem packet0902_pair (i : Fin 7) : checkEdgePair packet0902 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0902_ok : checkStripPacket packet0902 = true :=
  checkStripPacket_intro packet0902_shape packet0902_cache packet0902_pair

theorem packet0903_membership : packet0903 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0903_shape : checkStripShape packet0903.row = true := by
  decide +kernel

private theorem packet0903_cache : checkStripCache packet0903 = true := by
  decide +kernel

private theorem packet0903_pair (i : Fin 7) : checkEdgePair packet0903 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0903_ok : checkStripPacket packet0903 = true :=
  checkStripPacket_intro packet0903_shape packet0903_cache packet0903_pair

theorem packet0904_membership : packet0904 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0904_shape : checkStripShape packet0904.row = true := by
  decide +kernel

private theorem packet0904_cache : checkStripCache packet0904 = true := by
  decide +kernel

private theorem packet0904_pair (i : Fin 7) : checkEdgePair packet0904 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0904_ok : checkStripPacket packet0904 = true :=
  checkStripPacket_intro packet0904_shape packet0904_cache packet0904_pair

theorem packet0905_membership : packet0905 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0905_shape : checkStripShape packet0905.row = true := by
  decide +kernel

private theorem packet0905_cache : checkStripCache packet0905 = true := by
  decide +kernel

private theorem packet0905_pair (i : Fin 7) : checkEdgePair packet0905 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0905_ok : checkStripPacket packet0905 = true :=
  checkStripPacket_intro packet0905_shape packet0905_cache packet0905_pair

theorem packet0906_membership : packet0906 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0906_shape : checkStripShape packet0906.row = true := by
  decide +kernel

private theorem packet0906_cache : checkStripCache packet0906 = true := by
  decide +kernel

private theorem packet0906_pair (i : Fin 7) : checkEdgePair packet0906 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0906_ok : checkStripPacket packet0906 = true :=
  checkStripPacket_intro packet0906_shape packet0906_cache packet0906_pair

theorem packet0907_membership : packet0907 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0907_shape : checkStripShape packet0907.row = true := by
  decide +kernel

private theorem packet0907_cache : checkStripCache packet0907 = true := by
  decide +kernel

private theorem packet0907_pair (i : Fin 7) : checkEdgePair packet0907 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0907_ok : checkStripPacket packet0907 = true :=
  checkStripPacket_intro packet0907_shape packet0907_cache packet0907_pair

theorem packet0908_membership : packet0908 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0908_shape : checkStripShape packet0908.row = true := by
  decide +kernel

private theorem packet0908_cache : checkStripCache packet0908 = true := by
  decide +kernel

private theorem packet0908_pair (i : Fin 7) : checkEdgePair packet0908 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0908_ok : checkStripPacket packet0908 = true :=
  checkStripPacket_intro packet0908_shape packet0908_cache packet0908_pair

theorem packet0909_membership : packet0909 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0909_shape : checkStripShape packet0909.row = true := by
  decide +kernel

private theorem packet0909_cache : checkStripCache packet0909 = true := by
  decide +kernel

private theorem packet0909_pair (i : Fin 7) : checkEdgePair packet0909 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0909_ok : checkStripPacket packet0909 = true :=
  checkStripPacket_intro packet0909_shape packet0909_cache packet0909_pair

theorem packet0910_membership : packet0910 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0910_shape : checkStripShape packet0910.row = true := by
  decide +kernel

private theorem packet0910_cache : checkStripCache packet0910 = true := by
  decide +kernel

private theorem packet0910_pair (i : Fin 7) : checkEdgePair packet0910 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0910_ok : checkStripPacket packet0910 = true :=
  checkStripPacket_intro packet0910_shape packet0910_cache packet0910_pair

theorem packet0911_membership : packet0911 ∈ packets037 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0911_shape : checkStripShape packet0911.row = true := by
  decide +kernel

private theorem packet0911_cache : checkStripCache packet0911 = true := by
  decide +kernel

private theorem packet0911_pair (i : Fin 7) : checkEdgePair packet0911 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0911_ok : checkStripPacket packet0911 = true :=
  checkStripPacket_intro packet0911_shape packet0911_cache packet0911_pair

theorem packets037_checked : packets037.all checkStripPacket = true := by
  simp only [packets037, List.all_cons, List.all_nil, Bool.true_and, packet0888_ok,
    packet0889_ok, packet0890_ok, packet0891_ok, packet0892_ok, packet0893_ok,
    packet0894_ok, packet0895_ok, packet0896_ok, packet0897_ok, packet0898_ok,
    packet0899_ok, packet0900_ok, packet0901_ok, packet0902_ok, packet0903_ok,
    packet0904_ok, packet0905_ok, packet0906_ok, packet0907_ok, packet0908_ok,
    packet0909_ok, packet0910_ok, packet0911_ok]

theorem packets037_valid : packets037.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
