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

def packet1176 : StripRowPacket :=
  ⟨⟨⟨6,60,5,20⟩,
    ![433,1390,2725,4241,5720,6963,7816],![441,1410,2759,4285,5767,7000,7833]⟩,
    ⟨87394702662909011347874317,15390913619902650147272514560⟩,
    ⟨106625985025483260877221777,14581646237109964076739051520⟩⟩

def packet1177 : StripRowPacket :=
  ⟨⟨⟨6,60,5,21⟩,
    ![437,1404,2750,4275,5756,6991,7828],![445,1423,2782,4318,5804,7030,7847]⟩,
    ⟨438540281360476286138071469,61563654479610600589090058240⟩,
    ⟨63849464145936571497162767,7290823118554982038369525760⟩⟩

def packet1178 : StripRowPacket :=
  ⟨⟨⟨6,61,5,20⟩,
    ![432,1389,2723,4239,5719,6962,7815],![441,1409,2757,4283,5766,6999,7833]⟩,
    ⟨17207441428187250730171757,3004159421817815402547687424⟩,
    ⟨64429168607917304015263258639,8738671060862921588010994032640⟩⟩

def packet1179 : StripRowPacket :=
  ⟨⟨⟨6,61,5,21⟩,
    ![437,1403,2748,4273,5755,6990,7827],![445,1421,2780,4316,5803,7029,7847]⟩,
    ⟨431676660146429336227331953,60083188436356308050953748480⟩,
    ⟨7716066120064530621088059933,873867106086292158801099403264⟩⟩

def packet1180 : StripRowPacket :=
  ⟨⟨⟨6,60,5,22⟩,
    ![441,1416,2773,4307,5793,7021,7841],![449,1434,2804,4350,5841,7063,7864]⟩,
    ⟨4795470473357422971678597,559669586178278187173545984⟩,
    ⟨13524715596205729555584481,1325604203373633097885368320⟩⟩

def packet1181 : StripRowPacket :=
  ⟨⟨⟨6,60,5,23⟩,
    ![445,1428,2795,4339,5829,7053,7857],![452,1445,2824,4380,5877,7098,7883]⟩,
    ⟨616463222778156767631219871,61563654479610600589090058240⟩,
    ⟨21230601853081613403566631,1822705779638745509592381440⟩⟩

def packet1182 : StripRowPacket :=
  ⟨⟨⟨6,61,5,22⟩,
    ![441,1415,2771,4305,5791,7020,7841],![448,1433,2802,4348,5839,7062,7863]⟩,
    ⟨259602245864556828925614383,30041594218178154025476874240⟩,
    ⟨355304955705032839551375257,34540201821592575446683770880⟩⟩

def packet1183 : StripRowPacket :=
  ⟨⟨⟨6,61,5,23⟩,
    ![444,1427,2793,4337,5828,7052,7857],![452,1444,2822,4378,5876,7097,7882]⟩,
    ⟨606732323311797979475125579,60083188436356308050953748480⟩,
    ⟨12827955798262663825264410089,1092333882607865198501374254080⟩⟩

def packet1184 : StripRowPacket :=
  ⟨⟨⟨6,62,5,20⟩,
    ![432,1388,2722,4237,5717,6961,7815],![440,1408,2755,4281,5764,6998,7832]⟩,
    ⟨13800841531523513739701464127,2388838279190047766096715741184⟩,
    ⟨8409744016124056587018764867,1131376878979518065323684642816⟩⟩

def packet1185 : StripRowPacket :=
  ⟨⟨⟨6,62,5,21⟩,
    ![436,1401,2746,4271,5753,6989,7827],![444,1420,2778,4314,5801,7029,7847]⟩,
    ⟨69235175334531564516188663247,9555353116760191064386862964736⟩,
    ⟨5035649325713607557192286109,565688439489759032661842321408⟩⟩

def packet1186 : StripRowPacket :=
  ⟨⟨⟨6,63,5,20⟩,
    ![431,1387,2720,4235,5716,6960,7815],![440,1407,2753,4279,5763,6997,7832]⟩,
    ⟨18120210670388989,3110031194645073920⟩,
    ⟨515935982570899479,68853050695127029760⟩⟩

def packet1187 : StripRowPacket :=
  ⟨⟨⟨6,63,5,21⟩,
    ![436,1400,2745,4269,5752,6988,7827],![444,1419,2777,4312,5799,7028,7846]⟩,
    ⟨999832287768790543,136841372564383252480⟩,
    ⟨308928425759637049,34426525347563514880⟩⟩

def packet1188 : StripRowPacket :=
  ⟨⟨⟨6,62,5,22⟩,
    ![440,1414,2770,4304,5790,7019,7841],![448,1432,2800,4346,5838,7061,7863]⟩,
    ⟨41633492271484537036785734993,4777676558380095532193431482368⟩,
    ⟨11732853286730373641750379569,1131376878979518065323684642816⟩⟩

def packet1189 : StripRowPacket :=
  ⟨⟨⟨6,62,5,23⟩,
    ![444,1426,2791,4335,5826,7051,7857],![451,1442,2820,4376,5874,7096,7882]⟩,
    ⟨4230382337017677549171925075,415450135511312654973341868032⟩,
    ⟨1674300990254191521139523365,141422109872439758165460580352⟩⟩

def packet1190 : StripRowPacket :=
  ⟨⟨⟨6,63,5,22⟩,
    ![440,1413,2768,4302,5788,7018,7841],![448,1431,2798,4344,5836,7060,7863]⟩,
    ⟨9249040815695889,1052625942802948096⟩,
    ⟨719777720467648717,68853050695127029760⟩⟩

def packet1191 : StripRowPacket :=
  ⟨⟨⟨6,63,5,23⟩,
    ![444,1425,2790,4333,5825,7050,7856],![451,1441,2819,4374,5872,7095,7882]⟩,
    ⟨1404918324312140597,136841372564383252480⟩,
    ⟨102712323677002917,8606631336890878720⟩⟩

def packet1192 : StripRowPacket :=
  ⟨⟨⟨6,56,4,12⟩,
    ![450,1444,2823,4377,5872,7090,7876],![460,1469,2869,4444,5954,7174,7932]⟩,
    ⟨6567616466544613901469,593367760427187408794560⟩,
    ⟨1075176667791844078849117,76490390554350298673438720⟩⟩

def packet1193 : StripRowPacket :=
  ⟨⟨⟨6,57,4,12⟩,
    ![450,1442,2821,4375,5870,7089,7876],![460,1468,2867,4441,5952,7173,7932]⟩,
    ⟨16339944661346809958732091691,1463298197772160012062642878464⟩,
    ⟨2457736776208368461891048333,173354006520491469747720515584⟩⟩

def packet1194 : StripRowPacket :=
  ⟨⟨⟨5,28,4,13⟩,
    ![455,1461,2856,4427,5936,7157,7919],![466,1487,2903,4496,6023,7253,8002]⟩,
    ⟨36546883539208973378893,2642930094777841720417280⟩,
    ⟨5367008434908719629003,315325929579516987422720⟩⟩

def packet1195 : StripRowPacket :=
  ⟨⟨⟨6,58,4,12⟩,
    ![449,1441,2819,4373,5869,7088,7876],![459,1467,2865,4439,5951,7172,7931]⟩,
    ⟨9110550160760598650482419523,808803017935430240405581184000⟩,
    ⟨93150348489495773242462016423,6514805710558910077783995965440⟩⟩

def packet1196 : StripRowPacket :=
  ⟨⟨⟨6,59,4,12⟩,
    ![449,1440,2817,4371,5867,7088,7876],![459,1465,2863,4437,5949,7171,7931]⟩,
    ⟨317083256301110133171381441,27908452166743961300403435520⟩,
    ⟨405110709781386800392183649,28096671251805235027776256000⟩⟩

def packet1197 : StripRowPacket :=
  ⟨⟨⟨5,29,4,13⟩,
    ![454,1458,2852,4423,5933,7155,7919],![465,1484,2899,4491,6019,7251,8002]⟩,
    ⟨11636587655571242399687209,826932202587614827132841984⟩,
    ⟨329737820599567717801119,19050442408366731554722816⟩⟩

def packet1198 : StripRowPacket :=
  ⟨⟨⟨5,28,4,14⟩,
    ![460,1477,2888,4477,6001,7231,7981],![470,1501,2931,4539,6081,7324,8093]⟩,
    ⟨21982676399426089708887,1321465047388920860208640⟩,
    ⟨12504546126174054518963,630651859159033974845440⟩⟩

def packet1199 : StripRowPacket :=
  ⟨⟨⟨5,28,4,15⟩,
    ![465,1492,2917,4521,6060,7302,8064],![474,1514,2955,4577,6132,7386,8192]⟩,
    ⟨10276764411699077091331,528586018955568344083456⟩,
    ⟨116607150766333,5151532615513856⟩⟩

def packets049 : List StripRowPacket :=
  [packet1176, packet1177, packet1178, packet1179, packet1180, packet1181,
   packet1182, packet1183, packet1184, packet1185, packet1186, packet1187,
   packet1188, packet1189, packet1190, packet1191, packet1192, packet1193,
   packet1194, packet1195, packet1196, packet1197, packet1198, packet1199]

theorem packet1176_membership : packet1176 ∈ packets049 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet1176_shape : checkStripShape packet1176.row = true := by
  decide +kernel

private theorem packet1176_cache : checkStripCache packet1176 = true := by
  decide +kernel

private theorem packet1176_pair (i : Fin 7) : checkEdgePair packet1176 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1176_ok : checkStripPacket packet1176 = true :=
  checkStripPacket_intro packet1176_shape packet1176_cache packet1176_pair

theorem packet1177_membership : packet1177 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet1177_shape : checkStripShape packet1177.row = true := by
  decide +kernel

private theorem packet1177_cache : checkStripCache packet1177 = true := by
  decide +kernel

private theorem packet1177_pair (i : Fin 7) : checkEdgePair packet1177 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1177_ok : checkStripPacket packet1177 = true :=
  checkStripPacket_intro packet1177_shape packet1177_cache packet1177_pair

theorem packet1178_membership : packet1178 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet1178_shape : checkStripShape packet1178.row = true := by
  decide +kernel

private theorem packet1178_cache : checkStripCache packet1178 = true := by
  decide +kernel

private theorem packet1178_pair (i : Fin 7) : checkEdgePair packet1178 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1178_ok : checkStripPacket packet1178 = true :=
  checkStripPacket_intro packet1178_shape packet1178_cache packet1178_pair

theorem packet1179_membership : packet1179 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet1179_shape : checkStripShape packet1179.row = true := by
  decide +kernel

private theorem packet1179_cache : checkStripCache packet1179 = true := by
  decide +kernel

private theorem packet1179_pair (i : Fin 7) : checkEdgePair packet1179 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1179_ok : checkStripPacket packet1179 = true :=
  checkStripPacket_intro packet1179_shape packet1179_cache packet1179_pair

theorem packet1180_membership : packet1180 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet1180_shape : checkStripShape packet1180.row = true := by
  decide +kernel

private theorem packet1180_cache : checkStripCache packet1180 = true := by
  decide +kernel

private theorem packet1180_pair (i : Fin 7) : checkEdgePair packet1180 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1180_ok : checkStripPacket packet1180 = true :=
  checkStripPacket_intro packet1180_shape packet1180_cache packet1180_pair

theorem packet1181_membership : packet1181 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet1181_shape : checkStripShape packet1181.row = true := by
  decide +kernel

private theorem packet1181_cache : checkStripCache packet1181 = true := by
  decide +kernel

private theorem packet1181_pair (i : Fin 7) : checkEdgePair packet1181 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1181_ok : checkStripPacket packet1181 = true :=
  checkStripPacket_intro packet1181_shape packet1181_cache packet1181_pair

theorem packet1182_membership : packet1182 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet1182_shape : checkStripShape packet1182.row = true := by
  decide +kernel

private theorem packet1182_cache : checkStripCache packet1182 = true := by
  decide +kernel

private theorem packet1182_pair (i : Fin 7) : checkEdgePair packet1182 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1182_ok : checkStripPacket packet1182 = true :=
  checkStripPacket_intro packet1182_shape packet1182_cache packet1182_pair

theorem packet1183_membership : packet1183 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet1183_shape : checkStripShape packet1183.row = true := by
  decide +kernel

private theorem packet1183_cache : checkStripCache packet1183 = true := by
  decide +kernel

private theorem packet1183_pair (i : Fin 7) : checkEdgePair packet1183 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1183_ok : checkStripPacket packet1183 = true :=
  checkStripPacket_intro packet1183_shape packet1183_cache packet1183_pair

theorem packet1184_membership : packet1184 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet1184_shape : checkStripShape packet1184.row = true := by
  decide +kernel

private theorem packet1184_cache : checkStripCache packet1184 = true := by
  decide +kernel

private theorem packet1184_pair (i : Fin 7) : checkEdgePair packet1184 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1184_ok : checkStripPacket packet1184 = true :=
  checkStripPacket_intro packet1184_shape packet1184_cache packet1184_pair

theorem packet1185_membership : packet1185 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet1185_shape : checkStripShape packet1185.row = true := by
  decide +kernel

private theorem packet1185_cache : checkStripCache packet1185 = true := by
  decide +kernel

private theorem packet1185_pair (i : Fin 7) : checkEdgePair packet1185 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1185_ok : checkStripPacket packet1185 = true :=
  checkStripPacket_intro packet1185_shape packet1185_cache packet1185_pair

theorem packet1186_membership : packet1186 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet1186_shape : checkStripShape packet1186.row = true := by
  decide +kernel

private theorem packet1186_cache : checkStripCache packet1186 = true := by
  decide +kernel

private theorem packet1186_pair (i : Fin 7) : checkEdgePair packet1186 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1186_ok : checkStripPacket packet1186 = true :=
  checkStripPacket_intro packet1186_shape packet1186_cache packet1186_pair

theorem packet1187_membership : packet1187 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet1187_shape : checkStripShape packet1187.row = true := by
  decide +kernel

private theorem packet1187_cache : checkStripCache packet1187 = true := by
  decide +kernel

private theorem packet1187_pair (i : Fin 7) : checkEdgePair packet1187 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1187_ok : checkStripPacket packet1187 = true :=
  checkStripPacket_intro packet1187_shape packet1187_cache packet1187_pair

theorem packet1188_membership : packet1188 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet1188_shape : checkStripShape packet1188.row = true := by
  decide +kernel

private theorem packet1188_cache : checkStripCache packet1188 = true := by
  decide +kernel

private theorem packet1188_pair (i : Fin 7) : checkEdgePair packet1188 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1188_ok : checkStripPacket packet1188 = true :=
  checkStripPacket_intro packet1188_shape packet1188_cache packet1188_pair

theorem packet1189_membership : packet1189 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet1189_shape : checkStripShape packet1189.row = true := by
  decide +kernel

private theorem packet1189_cache : checkStripCache packet1189 = true := by
  decide +kernel

private theorem packet1189_pair (i : Fin 7) : checkEdgePair packet1189 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1189_ok : checkStripPacket packet1189 = true :=
  checkStripPacket_intro packet1189_shape packet1189_cache packet1189_pair

theorem packet1190_membership : packet1190 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet1190_shape : checkStripShape packet1190.row = true := by
  decide +kernel

private theorem packet1190_cache : checkStripCache packet1190 = true := by
  decide +kernel

private theorem packet1190_pair (i : Fin 7) : checkEdgePair packet1190 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1190_ok : checkStripPacket packet1190 = true :=
  checkStripPacket_intro packet1190_shape packet1190_cache packet1190_pair

theorem packet1191_membership : packet1191 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet1191_shape : checkStripShape packet1191.row = true := by
  decide +kernel

private theorem packet1191_cache : checkStripCache packet1191 = true := by
  decide +kernel

private theorem packet1191_pair (i : Fin 7) : checkEdgePair packet1191 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1191_ok : checkStripPacket packet1191 = true :=
  checkStripPacket_intro packet1191_shape packet1191_cache packet1191_pair

theorem packet1192_membership : packet1192 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet1192_shape : checkStripShape packet1192.row = true := by
  decide +kernel

private theorem packet1192_cache : checkStripCache packet1192 = true := by
  decide +kernel

private theorem packet1192_pair (i : Fin 7) : checkEdgePair packet1192 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1192_ok : checkStripPacket packet1192 = true :=
  checkStripPacket_intro packet1192_shape packet1192_cache packet1192_pair

theorem packet1193_membership : packet1193 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet1193_shape : checkStripShape packet1193.row = true := by
  decide +kernel

private theorem packet1193_cache : checkStripCache packet1193 = true := by
  decide +kernel

private theorem packet1193_pair (i : Fin 7) : checkEdgePair packet1193 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1193_ok : checkStripPacket packet1193 = true :=
  checkStripPacket_intro packet1193_shape packet1193_cache packet1193_pair

theorem packet1194_membership : packet1194 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet1194_shape : checkStripShape packet1194.row = true := by
  decide +kernel

private theorem packet1194_cache : checkStripCache packet1194 = true := by
  decide +kernel

private theorem packet1194_pair (i : Fin 7) : checkEdgePair packet1194 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1194_ok : checkStripPacket packet1194 = true :=
  checkStripPacket_intro packet1194_shape packet1194_cache packet1194_pair

theorem packet1195_membership : packet1195 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet1195_shape : checkStripShape packet1195.row = true := by
  decide +kernel

private theorem packet1195_cache : checkStripCache packet1195 = true := by
  decide +kernel

private theorem packet1195_pair (i : Fin 7) : checkEdgePair packet1195 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1195_ok : checkStripPacket packet1195 = true :=
  checkStripPacket_intro packet1195_shape packet1195_cache packet1195_pair

theorem packet1196_membership : packet1196 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet1196_shape : checkStripShape packet1196.row = true := by
  decide +kernel

private theorem packet1196_cache : checkStripCache packet1196 = true := by
  decide +kernel

private theorem packet1196_pair (i : Fin 7) : checkEdgePair packet1196 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1196_ok : checkStripPacket packet1196 = true :=
  checkStripPacket_intro packet1196_shape packet1196_cache packet1196_pair

theorem packet1197_membership : packet1197 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet1197_shape : checkStripShape packet1197.row = true := by
  decide +kernel

private theorem packet1197_cache : checkStripCache packet1197 = true := by
  decide +kernel

private theorem packet1197_pair (i : Fin 7) : checkEdgePair packet1197 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1197_ok : checkStripPacket packet1197 = true :=
  checkStripPacket_intro packet1197_shape packet1197_cache packet1197_pair

theorem packet1198_membership : packet1198 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1198_shape : checkStripShape packet1198.row = true := by
  decide +kernel

private theorem packet1198_cache : checkStripCache packet1198 = true := by
  decide +kernel

private theorem packet1198_pair (i : Fin 7) : checkEdgePair packet1198 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1198_ok : checkStripPacket packet1198 = true :=
  checkStripPacket_intro packet1198_shape packet1198_cache packet1198_pair

theorem packet1199_membership : packet1199 ∈ packets049 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet1199_shape : checkStripShape packet1199.row = true := by
  decide +kernel

private theorem packet1199_cache : checkStripCache packet1199 = true := by
  decide +kernel

private theorem packet1199_pair (i : Fin 7) : checkEdgePair packet1199 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet1199_ok : checkStripPacket packet1199 = true :=
  checkStripPacket_intro packet1199_shape packet1199_cache packet1199_pair

theorem packets049_checked : packets049.all checkStripPacket = true := by
  simp only [packets049, List.all_cons, List.all_nil, Bool.true_and, packet1176_ok,
    packet1177_ok, packet1178_ok, packet1179_ok, packet1180_ok, packet1181_ok,
    packet1182_ok, packet1183_ok, packet1184_ok, packet1185_ok, packet1186_ok,
    packet1187_ok, packet1188_ok, packet1189_ok, packet1190_ok, packet1191_ok,
    packet1192_ok, packet1193_ok, packet1194_ok, packet1195_ok, packet1196_ok,
    packet1197_ok, packet1198_ok, packet1199_ok]

theorem packets049_valid : packets049.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
