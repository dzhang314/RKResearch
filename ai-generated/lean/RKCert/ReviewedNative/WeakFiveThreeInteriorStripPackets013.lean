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

def packet0312 : StripRowPacket :=
  ⟨⟨⟨7,10,5,2⟩,
    ![114,1049,2380,3925,5473,6813,7763],![202,1098,2417,3954,5493,6824,7768]⟩,
    ⟨-2522507022554254021224875923,278029110710281293109756911616⟩,
    ⟨-1126598847936152081335055,136424649263506927319220224⟩⟩

def packet0313 : StripRowPacket :=
  ⟨⟨⟨7,10,5,3⟩,
    ![172,1083,2406,3944,5485,6819,7765],![250,1135,2446,3974,5505,6831,7770]⟩,
    ⟨-4696579166714088182719833337,556058221420562586219513823232⟩,
    ⟨-1078225366664021325106471,141296958165775031866335232⟩⟩

def packet0314 : StripRowPacket :=
  ⟨⟨⟨7,11,5,2⟩,
    ![114,1043,2373,3920,5470,6811,7762],![200,1092,2410,3948,5489,6822,7768]⟩,
    ⟨-66044951057030055832093,7154779205106513188995072⟩,
    ⟨-44615144134430157446189921,5305765289164364551204986880⟩⟩

def packet0315 : StripRowPacket :=
  ⟨⟨⟨7,11,5,3⟩,
    ![172,1077,2399,3938,5481,6817,7764],![247,1128,2439,3969,5502,6829,7770]⟩,
    ⟨-614756390924392435956147,71547792051065131889950720⟩,
    ⟨-10306082523314109871480827,1326441322291091137801246720⟩⟩

def packet0316 : StripRowPacket :=
  ⟨⟨⟨7,8,5,4⟩,
    ![228,1133,2448,3975,5505,6829,7768],![298,1187,2491,4008,5527,6842,7774]⟩,
    ⟨-22178345855323618237511,2940665449429082092664320⟩,
    ⟨-17022704928093047776594171,2525599017844933548020039680⟩⟩

def packet0317 : StripRowPacket :=
  ⟨⟨⟨7,8,5,5⟩,
    ![275,1170,2477,3996,5519,6836,7770],![335,1225,2522,4031,5542,6849,7776]⟩,
    ⟨-212261261772799591850375,30582920674062453763708928⟩,
    ⟨-7751052461569627399359229,1262799508922466774010019840⟩⟩

def packet0318 : StripRowPacket :=
  ⟨⟨⟨7,9,5,4⟩,
    ![226,1126,2440,3969,5501,6827,7767],![295,1179,2483,4002,5523,6840,7773]⟩,
    ⟨-14993301660092192668721813,1951629469614581180415647744⟩,
    ⟨-42753163880486997202768345619,6219803507079325947419148271616⟩⟩

def packet0319 : StripRowPacket :=
  ⟨⟨⟨7,9,5,5⟩,
    ![273,1163,2470,3991,5515,6834,7769],![331,1217,2515,4025,5538,6847,7775]⟩,
    ⟨-5021217759538070307326312531,710393126939707549671295778816⟩,
    ⟨-19464640309763642018810616933,3109901753539662973709574135808⟩⟩

def packet0320 : StripRowPacket :=
  ⟨⟨⟨7,8,5,6⟩,
    ![317,1209,2508,4019,5533,6843,7772],![368,1264,2555,4056,5558,6857,7779]⟩,
    ⟨-44060846965962171370599,6950663789559648582661120⟩,
    ⟨-254209180330644760378959,45919982142635155418546176⟩⟩

def packet0321 : StripRowPacket :=
  ⟨⟨⟨7,8,5,7⟩,
    ![353,1247,2540,4043,5548,6851,7775],![397,1302,2590,4082,5575,6866,7781]⟩,
    ⟨-877370957638337581054481,152914603370312268818544640⟩,
    ⟨-1557613114153958605370879,315699877230616693502504960⟩⟩

def packet0322 : StripRowPacket :=
  ⟨⟨⟨7,9,5,6⟩,
    ![313,1202,2501,4013,5529,6841,7771],![364,1256,2548,4050,5554,6855,7778]⟩,
    ⟨-2292436857401291241618942565,355196563469853774835647889408⟩,
    ⟨-35105397358567570872474122113,6219803507079325947419148271616⟩⟩

def packet0323 : StripRowPacket :=
  ⟨⟨⟨7,9,5,7⟩,
    ![349,1240,2533,4037,5545,6849,7774],![392,1294,2583,4076,5571,6864,7781]⟩,
    ⟨-4148529670067094659149457729,710393126939707549671295778816⟩,
    ⟨-3910189262200982213415876295,777475438384915743427393533952⟩⟩

def packet0324 : StripRowPacket :=
  ⟨⟨⟨7,10,5,4⟩,
    ![225,1119,2434,3964,5498,6825,7767],![292,1172,2476,3996,5519,6838,7772]⟩,
    ⟨-1087036072079917080747478707,139014555355140646554878455808⟩,
    ⟨-27709253943036783847245781,3956314828641700892257386496⟩⟩

def packet0325 : StripRowPacket :=
  ⟨⟨⟨7,10,5,5⟩,
    ![270,1157,2463,3985,5511,6832,7769],![328,1210,2508,4019,5534,6845,7775]⟩,
    ⟨-3999709409925248463259996319,556058221420562586219513823232⟩,
    ⟨-1146736255430953208705017,179832492210986404193517568⟩⟩

def packet0326 : StripRowPacket :=
  ⟨⟨⟨7,11,5,4⟩,
    ![223,1113,2427,3959,5494,6823,7766],![289,1166,2469,3990,5516,6836,7772]⟩,
    ⟨-10943524447663159876757,1375919077905098690191360⟩,
    ⟨-687882110037867664102849,96468459802988446385545216⟩⟩

def packet0327 : StripRowPacket :=
  ⟨⟨⟨7,11,5,5⟩,
    ![269,1151,2457,3980,5508,6830,7768],![325,1204,2501,4014,5530,6843,7774]⟩,
    ⟨-523370151632576191226581,71547792051065131889950720⟩,
    ⟨-17221351005454501782695041,2652882644582182275602493440⟩⟩

def packet0328 : StripRowPacket :=
  ⟨⟨⟨7,10,5,6⟩,
    ![311,1195,2494,4008,5526,6839,7771],![360,1249,2541,4044,5550,6853,7777]⟩,
    ⟨-1825637265765414301765038905,278029110710281293109756911616⟩,
    ⟨-22747141295925157335774967,3956314828641700892257386496⟩⟩

def packet0329 : StripRowPacket :=
  ⟨⟨⟨7,10,5,7⟩,
    ![346,1234,2527,4032,5541,6847,7773],![387,1287,2576,4070,5567,6862,7780]⟩,
    ⟨-3302839653136408743800159301,556058221420562586219513823232⟩,
    ⟨-2533260621546168010004945,494539353580212611532173312⟩⟩

def packet0330 : StripRowPacket :=
  ⟨⟨⟨7,11,5,6⟩,
    ![308,1189,2488,4003,5522,6838,7770],![356,1242,2534,4039,5546,6851,7777]⟩,
    ⟨-238838515993334034430899,35773896025532565944975360⟩,
    ⟨-31051887969735285605123469,5305765289164364551204986880⟩⟩

def packet0331 : StripRowPacket :=
  ⟨⟨⟨7,11,5,7⟩,
    ![343,1228,2520,4027,5538,6846,7773],![384,1281,2569,4065,5563,6860,7779]⟩,
    ⟨-86396782468151989299403,14309558410213026377990144⟩,
    ⟨-3457634241070195955607107,663220661145545568900623360⟩⟩

def packet0332 : StripRowPacket :=
  ⟨⟨⟨7,12,5,0⟩,
    ![0,976,2319,3880,5445,6798,7758],![86,1018,2352,3905,5462,6809,7763]⟩,
    ⟨-10462477024385317,979073481943722880⟩,
    ⟨-37806810318117560055063983,3835361726292351782848921600⟩⟩

def packet0333 : StripRowPacket :=
  ⟨⟨⟨7,12,5,1⟩,
    ![49,1005,2342,3897,5455,6804,7760],![146,1051,2377,3923,5473,6814,7765]⟩,
    ⟨-159615809633795000725549823,15904694305240490269017006080⟩,
    ⟨-17655510209363571601946543,1917680863146175891424460800⟩⟩

def packet0334 : StripRowPacket :=
  ⟨⟨⟨7,13,5,0⟩,
    ![0,970,2313,3875,5441,6797,7758],![85,1012,2345,3900,5458,6807,7763]⟩,
    ⟨-88956493489879,8191052144639936⟩,
    ⟨-122953429773857510651626507829,12265897301900464322897675141120⟩⟩

def packet0335 : StripRowPacket :=
  ⟨⟨⟨7,13,5,1⟩,
    ![50,999,2336,3892,5451,6802,7759],![144,1045,2370,3918,5469,6812,7765]⟩,
    ⟨-244438978367740164360943087923,23968198767906282918472501657600⟩,
    ⟨-11483225578066093672630399025,1226589730190046432289767514112⟩⟩

def packets013 : List StripRowPacket :=
  [packet0312, packet0313, packet0314, packet0315, packet0316, packet0317,
   packet0318, packet0319, packet0320, packet0321, packet0322, packet0323,
   packet0324, packet0325, packet0326, packet0327, packet0328, packet0329,
   packet0330, packet0331, packet0332, packet0333, packet0334, packet0335]

theorem packet0312_membership : packet0312 ∈ packets013 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0312_shape : checkStripShape packet0312.row = true := by
  decide +kernel

private theorem packet0312_cache : checkStripCache packet0312 = true := by
  decide +kernel

private theorem packet0312_pair (i : Fin 7) : checkEdgePair packet0312 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0312_ok : checkStripPacket packet0312 = true :=
  checkStripPacket_intro packet0312_shape packet0312_cache packet0312_pair

theorem packet0313_membership : packet0313 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0313_shape : checkStripShape packet0313.row = true := by
  decide +kernel

private theorem packet0313_cache : checkStripCache packet0313 = true := by
  decide +kernel

private theorem packet0313_pair (i : Fin 7) : checkEdgePair packet0313 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0313_ok : checkStripPacket packet0313 = true :=
  checkStripPacket_intro packet0313_shape packet0313_cache packet0313_pair

theorem packet0314_membership : packet0314 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0314_shape : checkStripShape packet0314.row = true := by
  decide +kernel

private theorem packet0314_cache : checkStripCache packet0314 = true := by
  decide +kernel

private theorem packet0314_pair (i : Fin 7) : checkEdgePair packet0314 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0314_ok : checkStripPacket packet0314 = true :=
  checkStripPacket_intro packet0314_shape packet0314_cache packet0314_pair

theorem packet0315_membership : packet0315 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0315_shape : checkStripShape packet0315.row = true := by
  decide +kernel

private theorem packet0315_cache : checkStripCache packet0315 = true := by
  decide +kernel

private theorem packet0315_pair (i : Fin 7) : checkEdgePair packet0315 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0315_ok : checkStripPacket packet0315 = true :=
  checkStripPacket_intro packet0315_shape packet0315_cache packet0315_pair

theorem packet0316_membership : packet0316 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0316_shape : checkStripShape packet0316.row = true := by
  decide +kernel

private theorem packet0316_cache : checkStripCache packet0316 = true := by
  decide +kernel

private theorem packet0316_pair (i : Fin 7) : checkEdgePair packet0316 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0316_ok : checkStripPacket packet0316 = true :=
  checkStripPacket_intro packet0316_shape packet0316_cache packet0316_pair

theorem packet0317_membership : packet0317 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0317_shape : checkStripShape packet0317.row = true := by
  decide +kernel

private theorem packet0317_cache : checkStripCache packet0317 = true := by
  decide +kernel

private theorem packet0317_pair (i : Fin 7) : checkEdgePair packet0317 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0317_ok : checkStripPacket packet0317 = true :=
  checkStripPacket_intro packet0317_shape packet0317_cache packet0317_pair

theorem packet0318_membership : packet0318 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0318_shape : checkStripShape packet0318.row = true := by
  decide +kernel

private theorem packet0318_cache : checkStripCache packet0318 = true := by
  decide +kernel

private theorem packet0318_pair (i : Fin 7) : checkEdgePair packet0318 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0318_ok : checkStripPacket packet0318 = true :=
  checkStripPacket_intro packet0318_shape packet0318_cache packet0318_pair

theorem packet0319_membership : packet0319 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0319_shape : checkStripShape packet0319.row = true := by
  decide +kernel

private theorem packet0319_cache : checkStripCache packet0319 = true := by
  decide +kernel

private theorem packet0319_pair (i : Fin 7) : checkEdgePair packet0319 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0319_ok : checkStripPacket packet0319 = true :=
  checkStripPacket_intro packet0319_shape packet0319_cache packet0319_pair

theorem packet0320_membership : packet0320 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0320_shape : checkStripShape packet0320.row = true := by
  decide +kernel

private theorem packet0320_cache : checkStripCache packet0320 = true := by
  decide +kernel

private theorem packet0320_pair (i : Fin 7) : checkEdgePair packet0320 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0320_ok : checkStripPacket packet0320 = true :=
  checkStripPacket_intro packet0320_shape packet0320_cache packet0320_pair

theorem packet0321_membership : packet0321 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0321_shape : checkStripShape packet0321.row = true := by
  decide +kernel

private theorem packet0321_cache : checkStripCache packet0321 = true := by
  decide +kernel

private theorem packet0321_pair (i : Fin 7) : checkEdgePair packet0321 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0321_ok : checkStripPacket packet0321 = true :=
  checkStripPacket_intro packet0321_shape packet0321_cache packet0321_pair

theorem packet0322_membership : packet0322 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0322_shape : checkStripShape packet0322.row = true := by
  decide +kernel

private theorem packet0322_cache : checkStripCache packet0322 = true := by
  decide +kernel

private theorem packet0322_pair (i : Fin 7) : checkEdgePair packet0322 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0322_ok : checkStripPacket packet0322 = true :=
  checkStripPacket_intro packet0322_shape packet0322_cache packet0322_pair

theorem packet0323_membership : packet0323 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0323_shape : checkStripShape packet0323.row = true := by
  decide +kernel

private theorem packet0323_cache : checkStripCache packet0323 = true := by
  decide +kernel

private theorem packet0323_pair (i : Fin 7) : checkEdgePair packet0323 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0323_ok : checkStripPacket packet0323 = true :=
  checkStripPacket_intro packet0323_shape packet0323_cache packet0323_pair

theorem packet0324_membership : packet0324 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0324_shape : checkStripShape packet0324.row = true := by
  decide +kernel

private theorem packet0324_cache : checkStripCache packet0324 = true := by
  decide +kernel

private theorem packet0324_pair (i : Fin 7) : checkEdgePair packet0324 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0324_ok : checkStripPacket packet0324 = true :=
  checkStripPacket_intro packet0324_shape packet0324_cache packet0324_pair

theorem packet0325_membership : packet0325 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0325_shape : checkStripShape packet0325.row = true := by
  decide +kernel

private theorem packet0325_cache : checkStripCache packet0325 = true := by
  decide +kernel

private theorem packet0325_pair (i : Fin 7) : checkEdgePair packet0325 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0325_ok : checkStripPacket packet0325 = true :=
  checkStripPacket_intro packet0325_shape packet0325_cache packet0325_pair

theorem packet0326_membership : packet0326 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0326_shape : checkStripShape packet0326.row = true := by
  decide +kernel

private theorem packet0326_cache : checkStripCache packet0326 = true := by
  decide +kernel

private theorem packet0326_pair (i : Fin 7) : checkEdgePair packet0326 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0326_ok : checkStripPacket packet0326 = true :=
  checkStripPacket_intro packet0326_shape packet0326_cache packet0326_pair

theorem packet0327_membership : packet0327 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0327_shape : checkStripShape packet0327.row = true := by
  decide +kernel

private theorem packet0327_cache : checkStripCache packet0327 = true := by
  decide +kernel

private theorem packet0327_pair (i : Fin 7) : checkEdgePair packet0327 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0327_ok : checkStripPacket packet0327 = true :=
  checkStripPacket_intro packet0327_shape packet0327_cache packet0327_pair

theorem packet0328_membership : packet0328 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0328_shape : checkStripShape packet0328.row = true := by
  decide +kernel

private theorem packet0328_cache : checkStripCache packet0328 = true := by
  decide +kernel

private theorem packet0328_pair (i : Fin 7) : checkEdgePair packet0328 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0328_ok : checkStripPacket packet0328 = true :=
  checkStripPacket_intro packet0328_shape packet0328_cache packet0328_pair

theorem packet0329_membership : packet0329 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0329_shape : checkStripShape packet0329.row = true := by
  decide +kernel

private theorem packet0329_cache : checkStripCache packet0329 = true := by
  decide +kernel

private theorem packet0329_pair (i : Fin 7) : checkEdgePair packet0329 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0329_ok : checkStripPacket packet0329 = true :=
  checkStripPacket_intro packet0329_shape packet0329_cache packet0329_pair

theorem packet0330_membership : packet0330 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0330_shape : checkStripShape packet0330.row = true := by
  decide +kernel

private theorem packet0330_cache : checkStripCache packet0330 = true := by
  decide +kernel

private theorem packet0330_pair (i : Fin 7) : checkEdgePair packet0330 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0330_ok : checkStripPacket packet0330 = true :=
  checkStripPacket_intro packet0330_shape packet0330_cache packet0330_pair

theorem packet0331_membership : packet0331 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0331_shape : checkStripShape packet0331.row = true := by
  decide +kernel

private theorem packet0331_cache : checkStripCache packet0331 = true := by
  decide +kernel

private theorem packet0331_pair (i : Fin 7) : checkEdgePair packet0331 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0331_ok : checkStripPacket packet0331 = true :=
  checkStripPacket_intro packet0331_shape packet0331_cache packet0331_pair

theorem packet0332_membership : packet0332 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0332_shape : checkStripShape packet0332.row = true := by
  decide +kernel

private theorem packet0332_cache : checkStripCache packet0332 = true := by
  decide +kernel

private theorem packet0332_pair (i : Fin 7) : checkEdgePair packet0332 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0332_ok : checkStripPacket packet0332 = true :=
  checkStripPacket_intro packet0332_shape packet0332_cache packet0332_pair

theorem packet0333_membership : packet0333 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0333_shape : checkStripShape packet0333.row = true := by
  decide +kernel

private theorem packet0333_cache : checkStripCache packet0333 = true := by
  decide +kernel

private theorem packet0333_pair (i : Fin 7) : checkEdgePair packet0333 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0333_ok : checkStripPacket packet0333 = true :=
  checkStripPacket_intro packet0333_shape packet0333_cache packet0333_pair

theorem packet0334_membership : packet0334 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0334_shape : checkStripShape packet0334.row = true := by
  decide +kernel

private theorem packet0334_cache : checkStripCache packet0334 = true := by
  decide +kernel

private theorem packet0334_pair (i : Fin 7) : checkEdgePair packet0334 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0334_ok : checkStripPacket packet0334 = true :=
  checkStripPacket_intro packet0334_shape packet0334_cache packet0334_pair

theorem packet0335_membership : packet0335 ∈ packets013 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0335_shape : checkStripShape packet0335.row = true := by
  decide +kernel

private theorem packet0335_cache : checkStripCache packet0335 = true := by
  decide +kernel

private theorem packet0335_pair (i : Fin 7) : checkEdgePair packet0335 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0335_ok : checkStripPacket packet0335 = true :=
  checkStripPacket_intro packet0335_shape packet0335_cache packet0335_pair

theorem packets013_checked : packets013.all checkStripPacket = true := by
  simp only [packets013, List.all_cons, List.all_nil, Bool.true_and, packet0312_ok,
    packet0313_ok, packet0314_ok, packet0315_ok, packet0316_ok, packet0317_ok,
    packet0318_ok, packet0319_ok, packet0320_ok, packet0321_ok, packet0322_ok,
    packet0323_ok, packet0324_ok, packet0325_ok, packet0326_ok, packet0327_ok,
    packet0328_ok, packet0329_ok, packet0330_ok, packet0331_ok, packet0332_ok,
    packet0333_ok, packet0334_ok, packet0335_ok]

theorem packets013_valid : packets013.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
