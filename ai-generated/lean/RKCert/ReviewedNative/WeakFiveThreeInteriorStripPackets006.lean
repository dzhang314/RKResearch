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

def packet0144 : StripRowPacket :=
  ⟨⟨⟨8,12,5,3⟩,
    ![186,1119,2441,3972,5503,6828,7768],![257,1165,2477,3999,5522,6839,7773]⟩,
    ⟨-13451359132185285372006667607,1740263059489992710280728952832⟩,
    ⟨-87531974063613898392932047979,12414948227539695153023118721024⟩⟩

def packet0145 : StripRowPacket :=
  ⟨⟨⟨8,13,5,3⟩,
    ![185,1115,2436,3968,5501,6827,7767],![255,1160,2473,3995,5519,6838,7773]⟩,
    ⟨-2454508126240870201523171740091,314171247455326723379194736476160⟩,
    ⟨-692351081805070069807203334953,97122800070262283556656196116480⟩⟩

def packet0146 : StripRowPacket :=
  ⟨⟨⟨7,7,5,2⟩,
    ![114,1071,2402,3943,5485,6819,7765],![210,1121,2441,3972,5505,6831,7770]⟩,
    ⟨-157101408275285511202679,18322776609380533920481280⟩,
    ⟨-2305059273646866245063,296267916574667719235840⟩⟩

def packet0147 : StripRowPacket :=
  ⟨⟨⟨7,7,5,3⟩,
    ![175,1105,2428,3961,5497,6825,7766],![259,1157,2469,3992,5518,6837,7772]⟩,
    ⟨-292649067173467126970981,36645553218761067840962560⟩,
    ⟨-213058344767879518595,29626791657466771923584⟩⟩

def packet0148 : StripRowPacket :=
  ⟨⟨⟨8,8,6,8⟩,
    ![247,1174,2486,4005,5525,6839,7771],![291,1203,2510,4023,5538,6847,7775]⟩,
    ⟨-68875737233580131591221687,10067471098884363681571957760⟩,
    ⟨-8507901253256419106998956691,1318387698459542657452872171520⟩⟩

def packet0149 : StripRowPacket :=
  ⟨⟨⟨8,8,6,9⟩,
    ![273,1192,2500,4015,5531,6843,7772],![313,1221,2525,4034,5544,6851,7777]⟩,
    ⟨-105841600729345803937977855,16107953758214981890515132416⟩,
    ⟨-815065009160981258412917947,131838769845954265745287217152⟩⟩

def packet0150 : StripRowPacket :=
  ⟨⟨⟨8,9,5,4⟩,
    ![245,1168,2481,4002,5522,6838,7771],![310,1216,2520,4031,5542,6849,7776]⟩,
    ⟨-300742112611410553879526830611,43443173696209667474514780405760⟩,
    ⟨-9447144357001281231845295103903,1509506747372340137293148841410560⟩⟩

def packet0151 : StripRowPacket :=
  ⟨⟨⟨8,8,6,10⟩,
    ![297,1210,2515,4026,5538,6846,7773],![334,1240,2540,4045,5551,6854,7778]⟩,
    ⟨-253705054712408493325002527,40269884395537454726287831040⟩,
    ⟨-708490811814836914659945659,119853427132685696132079288320⟩⟩

def packet0152 : StripRowPacket :=
  ⟨⟨⟨8,8,6,11⟩,
    ![320,1229,2530,4037,5545,6849,7774],![354,1260,2556,4057,5559,6858,7779]⟩,
    ⟨-485612215202904953610120833,80539768791074909452575662080⟩,
    ⟨-1859036942079149884597406257,329596924614885664363218042880⟩⟩

def packet0153 : StripRowPacket :=
  ⟨⟨⟨8,9,6,10⟩,
    ![294,1205,2510,4022,5536,6845,7773],![331,1235,2535,4042,5549,6853,7777]⟩,
    ⟨-221512129752942435328837413779,34754538956967733979611824324608⟩,
    ⟨-18064614502882205646400719914257,3019013494744680274586297682821120⟩⟩

def packet0154 : StripRowPacket :=
  ⟨⟨⟨8,9,6,11⟩,
    ![317,1224,2525,4033,5543,6848,7774],![351,1254,2551,4053,5556,6857,7778]⟩,
    ⟨-192701226895317664946768534931,31595035415425212708738022113280⟩,
    ⟨-4308735072940462207277712405177,754753373686170068646574420705280⟩⟩

def packet0155 : StripRowPacket :=
  ⟨⟨⟨8,10,5,4⟩,
    ![243,1164,2477,3998,5520,6837,7770],![307,1211,2515,4027,5540,6848,7776]⟩,
    ⟨-37524324738252909140185349335063,5358688649602675260067806968012800⟩,
    ⟨-296455383416697202618038203815,46809632849965037563680341426176⟩⟩

def packet0156 : StripRowPacket :=
  ⟨⟨⟨8,11,5,4⟩,
    ![242,1159,2472,3995,5518,6836,7770],![305,1207,2511,4023,5537,6847,7775]⟩,
    ⟨-1320265975128073502623206994429,186449926665072592633740379013120⟩,
    ⟨-71671536463813575071259371611,11186962820888753550245936742400⟩⟩

def packet0157 : StripRowPacket :=
  ⟨⟨⟨8,10,5,5⟩,
    ![292,1201,2506,4019,5533,6844,7772],![348,1249,2546,4050,5554,6856,7778]⟩,
    ⟨-138167196395493069338007070727443,21434754598410701040271227872051200⟩,
    ⟨-7435363622912158246073455036807,1287264903374038533001209389219840⟩⟩

def packet0158 : StripRowPacket :=
  ⟨⟨⟨8,11,5,5⟩,
    ![290,1196,2501,4016,5531,6842,7772],![345,1245,2542,4046,5552,6854,7778]⟩,
    ⟨-972096862286681548021462461181,149159941332058074106992303210496⟩,
    ⟨-32678663917767108273534917309,5593481410444376775122968371200⟩⟩

def packet0159 : StripRowPacket :=
  ⟨⟨⟨8,8,6,12⟩,
    ![341,1248,2545,4048,5552,6853,7775],![373,1279,2572,4069,5566,6862,7780]⟩,
    ⟨-115953580245248230142559153,20134942197768727363143915520⟩,
    ⟨-7078896606669993015519847807,1318387698459542657452872171520⟩⟩

def packet0160 : StripRowPacket :=
  ⟨⟨⟨8,8,6,13⟩,
    ![361,1267,2561,4060,5559,6857,7776],![390,1298,2588,4081,5574,6866,7781]⟩,
    ⟨-442016426759080887530352391,80539768791074909452575662080⟩,
    ⟨-3360822722511693246325035293,659193849229771328726436085760⟩⟩

def packet0161 : StripRowPacket :=
  ⟨⟨⟨8,9,5,6⟩,
    ![338,1243,2540,4045,5550,6852,7775],![386,1293,2583,4077,5572,6865,7781]⟩,
    ⟨-506076423541891068885133407673,86886347392419334949029560811520⟩,
    ⟨-1557559186952113519453110903361,301901349474468027458629768282112⟩⟩

def packet0162 : StripRowPacket :=
  ⟨⟨⟨8,8,6,14⟩,
    ![379,1286,2577,4072,5567,6861,7778],![407,1318,2605,4093,5582,6870,7782]⟩,
    ⟨-3820168477610625949913347,732179716282499176841596928⟩,
    ⟨-97913758205796614919696821,20282887668608348576198033408⟩⟩

def packet0163 : StripRowPacket :=
  ⟨⟨⟨8,8,6,15⟩,
    ![396,1305,2593,4084,5575,6865,7779],![423,1337,2622,4106,5591,6874,7784]⟩,
    ⟨-398420638315256821450583949,80539768791074909452575662080⟩,
    ⟨-375446445108135840431907259,82399231153721416090804510720⟩⟩

def packet0164 : StripRowPacket :=
  ⟨⟨⟨8,9,5,7⟩,
    ![376,1281,2572,4068,5565,6860,7777],![418,1332,2617,4103,5588,6873,7783]⟩,
    ⟨-916745045402852098896346561797,173772694784838669898059121623040⟩,
    ⟨-869765215455026347496960527907,188688343421542517161643605176320⟩⟩

def packet0165 : StripRowPacket :=
  ⟨⟨⟨8,10,5,6⟩,
    ![335,1238,2536,4041,5548,6851,7774],![383,1288,2579,4074,5569,6863,7780]⟩,
    ⟨-63118546918987251057636372057317,10717377299205350520135613936025600⟩,
    ⟨-13436408403730286840301718937403,2574529806748077066002418778439680⟩⟩

def packet0166 : StripRowPacket :=
  ⟨⟨⟨8,11,5,6⟩,
    ![332,1234,2532,4038,5545,6850,7774],![379,1283,2574,4070,5567,6862,7780]⟩,
    ⟨-170765566244404671912376793619,28684604102318860405190827540480⟩,
    ⟨-337389252612884902987887415,63925501833650020287119638528⟩⟩

def packet0167 : StripRowPacket :=
  ⟨⟨⟨8,10,5,7⟩,
    ![372,1277,2568,4065,5563,6858,7777],![414,1327,2613,4099,5586,6872,7783]⟩,
    ⟨-4572279651218237395701536700073,857390183936428041610849114882048⟩,
    ⟨-1500261195204532148557065975149,321816225843509633250302347304960⟩⟩

def packets006 : List StripRowPacket :=
  [packet0144, packet0145, packet0146, packet0147, packet0148, packet0149,
   packet0150, packet0151, packet0152, packet0153, packet0154, packet0155,
   packet0156, packet0157, packet0158, packet0159, packet0160, packet0161,
   packet0162, packet0163, packet0164, packet0165, packet0166, packet0167]

theorem packet0144_membership : packet0144 ∈ packets006 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0144_shape : checkStripShape packet0144.row = true := by
  decide +kernel

private theorem packet0144_cache : checkStripCache packet0144 = true := by
  decide +kernel

private theorem packet0144_pair (i : Fin 7) : checkEdgePair packet0144 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0144_ok : checkStripPacket packet0144 = true :=
  checkStripPacket_intro packet0144_shape packet0144_cache packet0144_pair

theorem packet0145_membership : packet0145 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0145_shape : checkStripShape packet0145.row = true := by
  decide +kernel

private theorem packet0145_cache : checkStripCache packet0145 = true := by
  decide +kernel

private theorem packet0145_pair (i : Fin 7) : checkEdgePair packet0145 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0145_ok : checkStripPacket packet0145 = true :=
  checkStripPacket_intro packet0145_shape packet0145_cache packet0145_pair

theorem packet0146_membership : packet0146 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0146_shape : checkStripShape packet0146.row = true := by
  decide +kernel

private theorem packet0146_cache : checkStripCache packet0146 = true := by
  decide +kernel

private theorem packet0146_pair (i : Fin 7) : checkEdgePair packet0146 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0146_ok : checkStripPacket packet0146 = true :=
  checkStripPacket_intro packet0146_shape packet0146_cache packet0146_pair

theorem packet0147_membership : packet0147 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0147_shape : checkStripShape packet0147.row = true := by
  decide +kernel

private theorem packet0147_cache : checkStripCache packet0147 = true := by
  decide +kernel

private theorem packet0147_pair (i : Fin 7) : checkEdgePair packet0147 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0147_ok : checkStripPacket packet0147 = true :=
  checkStripPacket_intro packet0147_shape packet0147_cache packet0147_pair

theorem packet0148_membership : packet0148 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0148_shape : checkStripShape packet0148.row = true := by
  decide +kernel

private theorem packet0148_cache : checkStripCache packet0148 = true := by
  decide +kernel

private theorem packet0148_pair (i : Fin 7) : checkEdgePair packet0148 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0148_ok : checkStripPacket packet0148 = true :=
  checkStripPacket_intro packet0148_shape packet0148_cache packet0148_pair

theorem packet0149_membership : packet0149 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0149_shape : checkStripShape packet0149.row = true := by
  decide +kernel

private theorem packet0149_cache : checkStripCache packet0149 = true := by
  decide +kernel

private theorem packet0149_pair (i : Fin 7) : checkEdgePair packet0149 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0149_ok : checkStripPacket packet0149 = true :=
  checkStripPacket_intro packet0149_shape packet0149_cache packet0149_pair

theorem packet0150_membership : packet0150 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0150_shape : checkStripShape packet0150.row = true := by
  decide +kernel

private theorem packet0150_cache : checkStripCache packet0150 = true := by
  decide +kernel

private theorem packet0150_pair (i : Fin 7) : checkEdgePair packet0150 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0150_ok : checkStripPacket packet0150 = true :=
  checkStripPacket_intro packet0150_shape packet0150_cache packet0150_pair

theorem packet0151_membership : packet0151 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0151_shape : checkStripShape packet0151.row = true := by
  decide +kernel

private theorem packet0151_cache : checkStripCache packet0151 = true := by
  decide +kernel

private theorem packet0151_pair (i : Fin 7) : checkEdgePair packet0151 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0151_ok : checkStripPacket packet0151 = true :=
  checkStripPacket_intro packet0151_shape packet0151_cache packet0151_pair

theorem packet0152_membership : packet0152 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0152_shape : checkStripShape packet0152.row = true := by
  decide +kernel

private theorem packet0152_cache : checkStripCache packet0152 = true := by
  decide +kernel

private theorem packet0152_pair (i : Fin 7) : checkEdgePair packet0152 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0152_ok : checkStripPacket packet0152 = true :=
  checkStripPacket_intro packet0152_shape packet0152_cache packet0152_pair

theorem packet0153_membership : packet0153 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0153_shape : checkStripShape packet0153.row = true := by
  decide +kernel

private theorem packet0153_cache : checkStripCache packet0153 = true := by
  decide +kernel

private theorem packet0153_pair (i : Fin 7) : checkEdgePair packet0153 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0153_ok : checkStripPacket packet0153 = true :=
  checkStripPacket_intro packet0153_shape packet0153_cache packet0153_pair

theorem packet0154_membership : packet0154 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0154_shape : checkStripShape packet0154.row = true := by
  decide +kernel

private theorem packet0154_cache : checkStripCache packet0154 = true := by
  decide +kernel

private theorem packet0154_pair (i : Fin 7) : checkEdgePair packet0154 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0154_ok : checkStripPacket packet0154 = true :=
  checkStripPacket_intro packet0154_shape packet0154_cache packet0154_pair

theorem packet0155_membership : packet0155 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0155_shape : checkStripShape packet0155.row = true := by
  decide +kernel

private theorem packet0155_cache : checkStripCache packet0155 = true := by
  decide +kernel

private theorem packet0155_pair (i : Fin 7) : checkEdgePair packet0155 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0155_ok : checkStripPacket packet0155 = true :=
  checkStripPacket_intro packet0155_shape packet0155_cache packet0155_pair

theorem packet0156_membership : packet0156 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0156_shape : checkStripShape packet0156.row = true := by
  decide +kernel

private theorem packet0156_cache : checkStripCache packet0156 = true := by
  decide +kernel

private theorem packet0156_pair (i : Fin 7) : checkEdgePair packet0156 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0156_ok : checkStripPacket packet0156 = true :=
  checkStripPacket_intro packet0156_shape packet0156_cache packet0156_pair

theorem packet0157_membership : packet0157 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0157_shape : checkStripShape packet0157.row = true := by
  decide +kernel

private theorem packet0157_cache : checkStripCache packet0157 = true := by
  decide +kernel

private theorem packet0157_pair (i : Fin 7) : checkEdgePair packet0157 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0157_ok : checkStripPacket packet0157 = true :=
  checkStripPacket_intro packet0157_shape packet0157_cache packet0157_pair

theorem packet0158_membership : packet0158 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0158_shape : checkStripShape packet0158.row = true := by
  decide +kernel

private theorem packet0158_cache : checkStripCache packet0158 = true := by
  decide +kernel

private theorem packet0158_pair (i : Fin 7) : checkEdgePair packet0158 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0158_ok : checkStripPacket packet0158 = true :=
  checkStripPacket_intro packet0158_shape packet0158_cache packet0158_pair

theorem packet0159_membership : packet0159 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0159_shape : checkStripShape packet0159.row = true := by
  decide +kernel

private theorem packet0159_cache : checkStripCache packet0159 = true := by
  decide +kernel

private theorem packet0159_pair (i : Fin 7) : checkEdgePair packet0159 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0159_ok : checkStripPacket packet0159 = true :=
  checkStripPacket_intro packet0159_shape packet0159_cache packet0159_pair

theorem packet0160_membership : packet0160 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0160_shape : checkStripShape packet0160.row = true := by
  decide +kernel

private theorem packet0160_cache : checkStripCache packet0160 = true := by
  decide +kernel

private theorem packet0160_pair (i : Fin 7) : checkEdgePair packet0160 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0160_ok : checkStripPacket packet0160 = true :=
  checkStripPacket_intro packet0160_shape packet0160_cache packet0160_pair

theorem packet0161_membership : packet0161 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0161_shape : checkStripShape packet0161.row = true := by
  decide +kernel

private theorem packet0161_cache : checkStripCache packet0161 = true := by
  decide +kernel

private theorem packet0161_pair (i : Fin 7) : checkEdgePair packet0161 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0161_ok : checkStripPacket packet0161 = true :=
  checkStripPacket_intro packet0161_shape packet0161_cache packet0161_pair

theorem packet0162_membership : packet0162 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0162_shape : checkStripShape packet0162.row = true := by
  decide +kernel

private theorem packet0162_cache : checkStripCache packet0162 = true := by
  decide +kernel

private theorem packet0162_pair (i : Fin 7) : checkEdgePair packet0162 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0162_ok : checkStripPacket packet0162 = true :=
  checkStripPacket_intro packet0162_shape packet0162_cache packet0162_pair

theorem packet0163_membership : packet0163 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0163_shape : checkStripShape packet0163.row = true := by
  decide +kernel

private theorem packet0163_cache : checkStripCache packet0163 = true := by
  decide +kernel

private theorem packet0163_pair (i : Fin 7) : checkEdgePair packet0163 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0163_ok : checkStripPacket packet0163 = true :=
  checkStripPacket_intro packet0163_shape packet0163_cache packet0163_pair

theorem packet0164_membership : packet0164 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0164_shape : checkStripShape packet0164.row = true := by
  decide +kernel

private theorem packet0164_cache : checkStripCache packet0164 = true := by
  decide +kernel

private theorem packet0164_pair (i : Fin 7) : checkEdgePair packet0164 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0164_ok : checkStripPacket packet0164 = true :=
  checkStripPacket_intro packet0164_shape packet0164_cache packet0164_pair

theorem packet0165_membership : packet0165 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0165_shape : checkStripShape packet0165.row = true := by
  decide +kernel

private theorem packet0165_cache : checkStripCache packet0165 = true := by
  decide +kernel

private theorem packet0165_pair (i : Fin 7) : checkEdgePair packet0165 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0165_ok : checkStripPacket packet0165 = true :=
  checkStripPacket_intro packet0165_shape packet0165_cache packet0165_pair

theorem packet0166_membership : packet0166 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0166_shape : checkStripShape packet0166.row = true := by
  decide +kernel

private theorem packet0166_cache : checkStripCache packet0166 = true := by
  decide +kernel

private theorem packet0166_pair (i : Fin 7) : checkEdgePair packet0166 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0166_ok : checkStripPacket packet0166 = true :=
  checkStripPacket_intro packet0166_shape packet0166_cache packet0166_pair

theorem packet0167_membership : packet0167 ∈ packets006 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0167_shape : checkStripShape packet0167.row = true := by
  decide +kernel

private theorem packet0167_cache : checkStripCache packet0167 = true := by
  decide +kernel

private theorem packet0167_pair (i : Fin 7) : checkEdgePair packet0167 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0167_ok : checkStripPacket packet0167 = true :=
  checkStripPacket_intro packet0167_shape packet0167_cache packet0167_pair

theorem packets006_checked : packets006.all checkStripPacket = true := by
  simp only [packets006, List.all_cons, List.all_nil, Bool.true_and, packet0144_ok,
    packet0145_ok, packet0146_ok, packet0147_ok, packet0148_ok, packet0149_ok,
    packet0150_ok, packet0151_ok, packet0152_ok, packet0153_ok, packet0154_ok,
    packet0155_ok, packet0156_ok, packet0157_ok, packet0158_ok, packet0159_ok,
    packet0160_ok, packet0161_ok, packet0162_ok, packet0163_ok, packet0164_ok,
    packet0165_ok, packet0166_ok, packet0167_ok]

theorem packets006_valid : packets006.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
