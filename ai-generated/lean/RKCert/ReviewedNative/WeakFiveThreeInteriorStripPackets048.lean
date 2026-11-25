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

def packet1152 : StripRowPacket :=
  ⟨⟨⟨6,56,5,23⟩,
    ![447,1433,2802,4347,5836,7056,7858],![454,1450,2832,4388,5884,7101,7884]⟩,
    ⟨22953383675528326805387,2373471041708749635178240⟩,
    ⟨215338742620811046636979,19122597638587574668359680⟩⟩

def packet1153 : StripRowPacket :=
  ⟨⟨⟨6,57,5,22⟩,
    ![442,1420,2779,4313,5798,7023,7842],![450,1438,2810,4356,5846,7066,7864]⟩,
    ⟨48859535473853481069629840691,5853192791088640048250571513856⟩,
    ⟨313569820176366662144390117,31518910276452994499585548288⟩⟩

def packet1154 : StripRowPacket :=
  ⟨⟨⟨6,57,5,23⟩,
    ![446,1432,2800,4345,5834,7055,7858],![454,1449,2830,4386,5882,7100,7883]⟩,
    ⟨114219314119240720904558207455,11706385582177280096501143027712⟩,
    ⟨492250399845700145456611635,43338501630122867436930128896⟩⟩

def packet1155 : StripRowPacket :=
  ⟨⟨⟨6,58,5,20⟩,
    ![433,1392,2728,4245,5723,6964,7816],![442,1413,2762,4289,5771,7002,7834]⟩,
    ⟨9024047193769106275774934069,1617606035870860480811162368000⟩,
    ⟨1216758585379063870533127483,169215732741789872150233661440⟩⟩

def packet1156 : StripRowPacket :=
  ⟨⟨⟨6,58,5,21⟩,
    ![438,1406,2753,4278,5760,6992,7828],![446,1425,2786,4322,5807,7032,7848]⟩,
    ⟨45293241902828516128289641253,6470424143483441923244649472000⟩,
    ⟨56106234127574321860912729761,6514805710558910077783995965440⟩⟩

def packet1157 : StripRowPacket :=
  ⟨⟨⟨6,59,5,20⟩,
    ![433,1391,2727,4243,5722,6964,7816],![442,1411,2761,4287,5769,7001,7833]⟩,
    ⟨62834093043595224414469739,11163380866697584520161374208⟩,
    ⟨407490304880152083205436713,56193342503610470055552512000⟩⟩

def packet1158 : StripRowPacket :=
  ⟨⟨⟨6,59,5,21⟩,
    ![437,1405,2752,4277,5758,6992,7828],![446,1424,2784,4320,5806,7031,7848]⟩,
    ⟨225239701179449804651401281,31895373904850241486175354880⟩,
    ⟨4436695707424330788374753,510848568214640636868659200⟩⟩

def packet1159 : StripRowPacket :=
  ⟨⟨⟨6,58,5,22⟩,
    ![442,1419,2777,4311,5796,7023,7842],![450,1437,2808,4354,5844,7065,7864]⟩,
    ⟨419156115619850824257534971,49772493411411091717266534400⟩,
    ⟨5684109801569972583156526211,566504844396426963285564866560⟩⟩

def packet1160 : StripRowPacket :=
  ⟨⟨⟨6,58,5,23⟩,
    ![446,1430,2799,4343,5832,7055,7858],![453,1447,2828,4384,5880,7099,7883]⟩,
    ⟨63687348158332698178669451207,6470424143483441923244649472000⟩,
    ⟨18657072827133761887921843273,1628701427639727519445998991360⟩⟩

def packet1161 : StripRowPacket :=
  ⟨⟨⟨6,59,5,22⟩,
    ![441,1417,2775,4309,5794,7022,7842],![449,1435,2806,4352,5843,7064,7864]⟩,
    ⟨948336977820196388415111577,111633808666975845201613742080⟩,
    ⟨568582750753200690237008947,56193342503610470055552512000⟩⟩

def packet1162 : StripRowPacket :=
  ⟨⟨⟨6,59,5,23⟩,
    ![445,1429,2797,4341,5831,7054,7857],![453,1446,2826,4382,5879,7098,7883]⟩,
    ⟨96376956653245083526114667,9707287710171812626227281920⟩,
    ⟨81141121711215624219099383,7024167812951308756944064000⟩⟩

def packet1163 : StripRowPacket :=
  ⟨⟨⟨6,60,4,8⟩,
    ![410,1323,2610,4098,5585,6870,7781],![427,1366,2680,4181,5660,6920,7801]⟩,
    ⟨-30130154729446719205767,295979108075050964370625280⟩,
    ⟨21703577613156807262955253,7290823118554982038369525760⟩⟩

def packet1164 : StripRowPacket :=
  ⟨⟨⟨6,61,4,8⟩,
    ![409,1321,2608,4096,5583,6869,7780],![426,1365,2678,4179,5658,6919,7800]⟩,
    ⟨-372656110437016993259507,3755199277272269253184609280⟩,
    ⟨1873906487838092673457945469,624190790061637256286499573760⟩⟩

def packet1165 : StripRowPacket :=
  ⟨⟨⟨6,60,5,18⟩,
    ![422,1359,2671,4170,5650,6913,7796],![432,1382,2708,4216,5695,6945,7810]⟩,
    ⟨12261133516711111707024919,4397403891400757184935004160⟩,
    ⟨64480098492703496643014263,14581646237109964076739051520⟩⟩

def packet1166 : StripRowPacket :=
  ⟨⟨⟨6,60,5,19⟩,
    ![428,1375,2699,4206,5685,6937,7805],![437,1397,2734,4251,5731,6971,7821]⟩,
    ⟨260617339942795804644923067,61563654479610600589090058240⟩,
    ⟨4277652087954668938005901,729082311855498203836952576⟩⟩

def packet1167 : StripRowPacket :=
  ⟨⟨⟨6,61,5,18⟩,
    ![422,1358,2669,4168,5649,6912,7796],![431,1381,2706,4214,5693,6944,7810]⟩,
    ⟨84546582699188185677820757,30041594218178154025476874240⟩,
    ⟨38966183422461299624028577257,8738671060862921588010994032640⟩⟩

def packet1168 : StripRowPacket :=
  ⟨⟨⟨6,61,5,19⟩,
    ![427,1374,2697,4204,5683,6936,7805],![436,1395,2732,4249,5729,6970,7820]⟩,
    ⟨256620996981060692979538327,60083188436356308050953748480⟩,
    ⟨12924419003797325454911479487,2184667765215730397002748508160⟩⟩

def packet1169 : StripRowPacket :=
  ⟨⟨⟨6,62,4,8⟩,
    ![409,1320,2607,4094,5581,6868,7780],![426,1363,2676,4177,5657,6918,7800]⟩,
    ⟨-57741919228498954420335653,597209569797511941524178935296⟩,
    ⟨1712540055107290502460671407,565688439489759032661842321408⟩⟩

def packet1170 : StripRowPacket :=
  ⟨⟨⟨6,63,5,16⟩,
    ![409,1319,2605,4092,5580,6867,7779],![419,1345,2645,4138,5621,6894,7791]⟩,
    ⟨-805175224349037,8552585785273953280⟩,
    ⟨108252506777401003,68853050695127029760⟩⟩

def packet1171 : StripRowPacket :=
  ⟨⟨⟨6,63,5,17⟩,
    ![415,1339,2636,4129,5612,6887,7787],![425,1362,2674,4175,5655,6917,7800]⟩,
    ⟨37932042936418087,27368274512876650496⟩,
    ⟨105086687862887811,34426525347563514880⟩⟩

def packet1172 : StripRowPacket :=
  ⟨⟨⟨6,62,5,18⟩,
    ![422,1357,2667,4167,5647,6911,7795],![431,1380,2704,4212,5692,6943,7809]⟩,
    ⟨13569873854609517922020121515,4777676558380095532193431482368⟩,
    ⟨5086634745517739532287150165,1131376878979518065323684642816⟩⟩

def packet1173 : StripRowPacket :=
  ⟨⟨⟨6,62,5,19⟩,
    ![427,1373,2695,4202,5682,6935,7805],![436,1394,2730,4247,5728,6969,7820]⟩,
    ⟨3742868810696049581947549979,868668465160017369489714814976⟩,
    ⟨1687047345205224514913239379,282844219744879516330921160704⟩⟩

def packet1174 : StripRowPacket :=
  ⟨⟨⟨6,63,5,18⟩,
    ![421,1356,2666,4165,5646,6910,7795],![431,1378,2702,4211,5690,6942,7809]⟩,
    ⟨196101616476882731,68420686282191626240⟩,
    ⟨312094244674150241,68853050695127029760⟩⟩

def packet1175 : StripRowPacket :=
  ⟨⟨⟨6,63,5,19⟩,
    ![427,1372,2694,4200,5680,6934,7804],![436,1393,2729,4246,5726,6968,7820]⟩,
    ⟨594746251225440489,136841372564383252480⟩,
    ⟨20700755681126243,3442652534756351488⟩⟩

def packets048 : List StripRowPacket :=
  [packet1152, packet1153, packet1154, packet1155, packet1156, packet1157,
   packet1158, packet1159, packet1160, packet1161, packet1162, packet1163,
   packet1164, packet1165, packet1166, packet1167, packet1168, packet1169,
   packet1170, packet1171, packet1172, packet1173, packet1174, packet1175]

theorem packet1152_membership : packet1152 ∈ packets048 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1152_shape : checkStripShape packet1152.row = true := by
  decide +kernel

private theorem packet1152_cache : checkStripCache packet1152 = true := by
  decide +kernel

private theorem packet1152_pair (i : Fin 7) : checkEdgePair packet1152 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1152_ok : checkStripPacket packet1152 = true :=
  checkStripPacket_intro packet1152_shape packet1152_cache packet1152_pair

theorem packet1153_membership : packet1153 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1153_shape : checkStripShape packet1153.row = true := by
  decide +kernel

private theorem packet1153_cache : checkStripCache packet1153 = true := by
  decide +kernel

private theorem packet1153_pair (i : Fin 7) : checkEdgePair packet1153 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1153_ok : checkStripPacket packet1153 = true :=
  checkStripPacket_intro packet1153_shape packet1153_cache packet1153_pair

theorem packet1154_membership : packet1154 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1154_shape : checkStripShape packet1154.row = true := by
  decide +kernel

private theorem packet1154_cache : checkStripCache packet1154 = true := by
  decide +kernel

private theorem packet1154_pair (i : Fin 7) : checkEdgePair packet1154 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1154_ok : checkStripPacket packet1154 = true :=
  checkStripPacket_intro packet1154_shape packet1154_cache packet1154_pair

theorem packet1155_membership : packet1155 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1155_shape : checkStripShape packet1155.row = true := by
  decide +kernel

private theorem packet1155_cache : checkStripCache packet1155 = true := by
  decide +kernel

private theorem packet1155_pair (i : Fin 7) : checkEdgePair packet1155 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1155_ok : checkStripPacket packet1155 = true :=
  checkStripPacket_intro packet1155_shape packet1155_cache packet1155_pair

theorem packet1156_membership : packet1156 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1156_shape : checkStripShape packet1156.row = true := by
  decide +kernel

private theorem packet1156_cache : checkStripCache packet1156 = true := by
  decide +kernel

private theorem packet1156_pair (i : Fin 7) : checkEdgePair packet1156 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1156_ok : checkStripPacket packet1156 = true :=
  checkStripPacket_intro packet1156_shape packet1156_cache packet1156_pair

theorem packet1157_membership : packet1157 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1157_shape : checkStripShape packet1157.row = true := by
  decide +kernel

private theorem packet1157_cache : checkStripCache packet1157 = true := by
  decide +kernel

private theorem packet1157_pair (i : Fin 7) : checkEdgePair packet1157 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1157_ok : checkStripPacket packet1157 = true :=
  checkStripPacket_intro packet1157_shape packet1157_cache packet1157_pair

theorem packet1158_membership : packet1158 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1158_shape : checkStripShape packet1158.row = true := by
  decide +kernel

private theorem packet1158_cache : checkStripCache packet1158 = true := by
  decide +kernel

private theorem packet1158_pair (i : Fin 7) : checkEdgePair packet1158 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1158_ok : checkStripPacket packet1158 = true :=
  checkStripPacket_intro packet1158_shape packet1158_cache packet1158_pair

theorem packet1159_membership : packet1159 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1159_shape : checkStripShape packet1159.row = true := by
  decide +kernel

private theorem packet1159_cache : checkStripCache packet1159 = true := by
  decide +kernel

private theorem packet1159_pair (i : Fin 7) : checkEdgePair packet1159 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1159_ok : checkStripPacket packet1159 = true :=
  checkStripPacket_intro packet1159_shape packet1159_cache packet1159_pair

theorem packet1160_membership : packet1160 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1160_shape : checkStripShape packet1160.row = true := by
  decide +kernel

private theorem packet1160_cache : checkStripCache packet1160 = true := by
  decide +kernel

private theorem packet1160_pair (i : Fin 7) : checkEdgePair packet1160 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1160_ok : checkStripPacket packet1160 = true :=
  checkStripPacket_intro packet1160_shape packet1160_cache packet1160_pair

theorem packet1161_membership : packet1161 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1161_shape : checkStripShape packet1161.row = true := by
  decide +kernel

private theorem packet1161_cache : checkStripCache packet1161 = true := by
  decide +kernel

private theorem packet1161_pair (i : Fin 7) : checkEdgePair packet1161 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1161_ok : checkStripPacket packet1161 = true :=
  checkStripPacket_intro packet1161_shape packet1161_cache packet1161_pair

theorem packet1162_membership : packet1162 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1162_shape : checkStripShape packet1162.row = true := by
  decide +kernel

private theorem packet1162_cache : checkStripCache packet1162 = true := by
  decide +kernel

private theorem packet1162_pair (i : Fin 7) : checkEdgePair packet1162 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1162_ok : checkStripPacket packet1162 = true :=
  checkStripPacket_intro packet1162_shape packet1162_cache packet1162_pair

theorem packet1163_membership : packet1163 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1163_shape : checkStripShape packet1163.row = true := by
  decide +kernel

private theorem packet1163_cache : checkStripCache packet1163 = true := by
  decide +kernel

private theorem packet1163_pair (i : Fin 7) : checkEdgePair packet1163 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1163_ok : checkStripPacket packet1163 = true :=
  checkStripPacket_intro packet1163_shape packet1163_cache packet1163_pair

theorem packet1164_membership : packet1164 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1164_shape : checkStripShape packet1164.row = true := by
  decide +kernel

private theorem packet1164_cache : checkStripCache packet1164 = true := by
  decide +kernel

private theorem packet1164_pair (i : Fin 7) : checkEdgePair packet1164 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1164_ok : checkStripPacket packet1164 = true :=
  checkStripPacket_intro packet1164_shape packet1164_cache packet1164_pair

theorem packet1165_membership : packet1165 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1165_shape : checkStripShape packet1165.row = true := by
  decide +kernel

private theorem packet1165_cache : checkStripCache packet1165 = true := by
  decide +kernel

private theorem packet1165_pair (i : Fin 7) : checkEdgePair packet1165 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1165_ok : checkStripPacket packet1165 = true :=
  checkStripPacket_intro packet1165_shape packet1165_cache packet1165_pair

theorem packet1166_membership : packet1166 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1166_shape : checkStripShape packet1166.row = true := by
  decide +kernel

private theorem packet1166_cache : checkStripCache packet1166 = true := by
  decide +kernel

private theorem packet1166_pair (i : Fin 7) : checkEdgePair packet1166 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1166_ok : checkStripPacket packet1166 = true :=
  checkStripPacket_intro packet1166_shape packet1166_cache packet1166_pair

theorem packet1167_membership : packet1167 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1167_shape : checkStripShape packet1167.row = true := by
  decide +kernel

private theorem packet1167_cache : checkStripCache packet1167 = true := by
  decide +kernel

private theorem packet1167_pair (i : Fin 7) : checkEdgePair packet1167 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1167_ok : checkStripPacket packet1167 = true :=
  checkStripPacket_intro packet1167_shape packet1167_cache packet1167_pair

theorem packet1168_membership : packet1168 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1168_shape : checkStripShape packet1168.row = true := by
  decide +kernel

private theorem packet1168_cache : checkStripCache packet1168 = true := by
  decide +kernel

private theorem packet1168_pair (i : Fin 7) : checkEdgePair packet1168 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1168_ok : checkStripPacket packet1168 = true :=
  checkStripPacket_intro packet1168_shape packet1168_cache packet1168_pair

theorem packet1169_membership : packet1169 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1169_shape : checkStripShape packet1169.row = true := by
  decide +kernel

private theorem packet1169_cache : checkStripCache packet1169 = true := by
  decide +kernel

private theorem packet1169_pair (i : Fin 7) : checkEdgePair packet1169 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1169_ok : checkStripPacket packet1169 = true :=
  checkStripPacket_intro packet1169_shape packet1169_cache packet1169_pair

theorem packet1170_membership : packet1170 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1170_shape : checkStripShape packet1170.row = true := by
  decide +kernel

private theorem packet1170_cache : checkStripCache packet1170 = true := by
  decide +kernel

private theorem packet1170_pair (i : Fin 7) : checkEdgePair packet1170 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1170_ok : checkStripPacket packet1170 = true :=
  checkStripPacket_intro packet1170_shape packet1170_cache packet1170_pair

theorem packet1171_membership : packet1171 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1171_shape : checkStripShape packet1171.row = true := by
  decide +kernel

private theorem packet1171_cache : checkStripCache packet1171 = true := by
  decide +kernel

private theorem packet1171_pair (i : Fin 7) : checkEdgePair packet1171 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1171_ok : checkStripPacket packet1171 = true :=
  checkStripPacket_intro packet1171_shape packet1171_cache packet1171_pair

theorem packet1172_membership : packet1172 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1172_shape : checkStripShape packet1172.row = true := by
  decide +kernel

private theorem packet1172_cache : checkStripCache packet1172 = true := by
  decide +kernel

private theorem packet1172_pair (i : Fin 7) : checkEdgePair packet1172 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1172_ok : checkStripPacket packet1172 = true :=
  checkStripPacket_intro packet1172_shape packet1172_cache packet1172_pair

theorem packet1173_membership : packet1173 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1173_shape : checkStripShape packet1173.row = true := by
  decide +kernel

private theorem packet1173_cache : checkStripCache packet1173 = true := by
  decide +kernel

private theorem packet1173_pair (i : Fin 7) : checkEdgePair packet1173 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1173_ok : checkStripPacket packet1173 = true :=
  checkStripPacket_intro packet1173_shape packet1173_cache packet1173_pair

theorem packet1174_membership : packet1174 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1174_shape : checkStripShape packet1174.row = true := by
  decide +kernel

private theorem packet1174_cache : checkStripCache packet1174 = true := by
  decide +kernel

private theorem packet1174_pair (i : Fin 7) : checkEdgePair packet1174 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1174_ok : checkStripPacket packet1174 = true :=
  checkStripPacket_intro packet1174_shape packet1174_cache packet1174_pair

theorem packet1175_membership : packet1175 ∈ packets048 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1175_shape : checkStripShape packet1175.row = true := by
  decide +kernel

private theorem packet1175_cache : checkStripCache packet1175 = true := by
  decide +kernel

private theorem packet1175_pair (i : Fin 7) : checkEdgePair packet1175 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1175_ok : checkStripPacket packet1175 = true :=
  checkStripPacket_intro packet1175_shape packet1175_cache packet1175_pair

theorem packets048_checked : packets048.all checkStripPacket = true := by
  simp only [packets048, List.all_cons, List.all_nil, Bool.true_and, packet1152_ok,
    packet1153_ok, packet1154_ok, packet1155_ok, packet1156_ok, packet1157_ok,
    packet1158_ok, packet1159_ok, packet1160_ok, packet1161_ok, packet1162_ok,
    packet1163_ok, packet1164_ok, packet1165_ok, packet1166_ok, packet1167_ok,
    packet1168_ok, packet1169_ok, packet1170_ok, packet1171_ok, packet1172_ok,
    packet1173_ok, packet1174_ok, packet1175_ok]

theorem packets048_valid : packets048.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
