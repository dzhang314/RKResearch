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

def packet0384 : StripRowPacket :=
  ⟨⟨⟨7,9,4,7⟩,
    ![492,1475,2781,4246,5688,6925,7798],![526,1545,2871,4336,5759,6967,7814]⟩,
    ⟨-547060678459339945265232961,355196563469853774835647889408⟩,
    ⟨-43153000620634524134382271,388737719192457871713696766976⟩⟩

def packet0385 : StripRowPacket :=
  ⟨⟨⟨7,10,5,12⟩,
    ![459,1410,2703,4175,5637,6897,7789],![485,1458,2758,4224,5673,6918,7798]⟩,
    ⟨-30012793483929027791357053,10693427335010818965759881216⟩,
    ⟨-7860803354590277801362525,3956314828641700892257386496⟩⟩

def packet0386 : StripRowPacket :=
  ⟨⟨⟨7,10,5,13⟩,
    ![474,1440,2739,4208,5660,6910,7793],![498,1486,2794,4259,5699,6933,7803]⟩,
    ⟨-63801599093152083443192013,29266222180029609801027043328⟩,
    ⟨-206913347347479405601043,152165954947757726625284096⟩⟩

def packet0387 : StripRowPacket :=
  ⟨⟨⟨7,11,5,12⟩,
    ![455,1404,2697,4170,5634,6896,7789],![480,1451,2751,4219,5670,6917,7797]⟩,
    ⟨-10175915705560966733655,3577389602553256594497536⟩,
    ⟨-563526511720683044395989,279250804692861292168683520⟩⟩

def packet0388 : StripRowPacket :=
  ⟨⟨⟨7,11,5,13⟩,
    ![469,1434,2733,4203,5657,6909,7793],![493,1479,2788,4254,5696,6931,7802]⟩,
    ⟨-157825194465311212308317,71547792051065131889950720⟩,
    ⟨-3658094840759629941628589,2652882644582182275602493440⟩⟩

def packet0389 : StripRowPacket :=
  ⟨⟨⟨7,10,4,7⟩,
    ![487,1468,2775,4241,5685,6924,7798],![520,1537,2864,4330,5755,6966,7814]⟩,
    ⟨-431897752187734862845364869,278029110710281293109756911616⟩,
    ⟨-26102148995177377134769,247269676790106305766086656⟩⟩

def packet0390 : StripRowPacket :=
  ⟨⟨⟨7,11,4,7⟩,
    ![482,1462,2769,4237,5682,6922,7797],![514,1529,2857,4325,5752,6964,7813]⟩,
    ⟨-56066037409701544971767,35773896025532565944975360⟩,
    ⟨-3037281813476272515477,30146393688433889495482880⟩⟩

def packet0391 : StripRowPacket :=
  ⟨⟨⟨7,12,5,8⟩,
    ![370,1260,2548,4048,5551,6852,7775],![405,1312,2598,4088,5578,6868,7782]⟩,
    ⟨-2180310324684151220288027,397617357631012256725425152⟩,
    ⟨-1621862829363111385972437,348669247844759252986265600⟩⟩

def packet0392 : StripRowPacket :=
  ⟨⟨⟨7,12,5,9⟩,
    ![395,1297,2583,4075,5569,6862,7778],![426,1348,2635,4117,5598,6878,7785]⟩,
    ⟨-76869070609304769966659831,15904694305240490269017006080⟩,
    ⟨-1534470122360380839452591,383536172629235178284892160⟩⟩

def packet0393 : StripRowPacket :=
  ⟨⟨⟨7,13,5,8⟩,
    ![367,1255,2543,4043,5548,6851,7774],![401,1306,2592,4083,5575,6866,7781]⟩,
    ⟨-1282838532234918613462447871,230463449691406566523774054400⟩,
    ⟨-5271276166207719931731487927,1115081572900042211172515921920⟩⟩

def packet0394 : StripRowPacket :=
  ⟨⟨⟨7,13,5,9⟩,
    ![392,1292,2578,4071,5566,6860,7777],![422,1342,2629,4113,5595,6877,7785]⟩,
    ⟨-117554668635958874577116220107,23968198767906282918472501657600⟩,
    ⟨-24931431917544172661861924809,6132948650950232161448837570560⟩⟩

def packet0395 : StripRowPacket :=
  ⟨⟨⟨7,12,5,10⟩,
    ![416,1332,2619,4104,5588,6872,7781],![445,1382,2671,4148,5619,6889,7789]⟩,
    ⟨-33262864115621745560899291,7952347152620245134508503040⟩,
    ⟨-12848911324213391543355013,3835361726292351782848921600⟩⟩

def packet0396 : StripRowPacket :=
  ⟨⟨⟨7,12,5,11⟩,
    ![434,1366,2655,4134,5609,6882,7784],![461,1414,2708,4181,5642,6902,7793]⟩,
    ⟨-56182385853182212276937333,15904694305240490269017006080⟩,
    ⟨-2588280356205743673046029,958840431573087945712230400⟩⟩

def packet0397 : StripRowPacket :=
  ⟨⟨⟨7,13,5,10⟩,
    ![413,1327,2614,4100,5585,6870,7780],![441,1376,2665,4144,5616,6888,7788]⟩,
    ⟨-10169412991948621335413786163,2396819876790628291847250165760⟩,
    ⟨-3210899218607059338338564003,943530561684651101761359626240⟩⟩

def packet0398 : StripRowPacket :=
  ⟨⟨⟨7,13,5,11⟩,
    ![431,1361,2650,4130,5606,6881,7784],![457,1408,2702,4176,5639,6900,7792]⟩,
    ⟨-85833591203013552131159503153,23968198767906282918472501657600⟩,
    ⟨-1681025792434759873653940723,613294865095023216144883757056⟩⟩

def packet0399 : StripRowPacket :=
  ⟨⟨⟨7,14,5,8⟩,
    ![364,1250,2537,4039,5545,6849,7774],![398,1300,2586,4078,5572,6865,7781]⟩,
    ⟨-9913933216208748598074141541,1755345404626011530278578092032⟩,
    ⟨-737207545097928665999592947,153538332026971632715167072256⟩⟩

def packet0400 : StripRowPacket :=
  ⟨⟨⟨7,14,5,9⟩,
    ![389,1286,2572,4066,5563,6858,7777],![419,1336,2623,4108,5592,6875,7784]⟩,
    ⟨-69862585659548008222484833437,14042763237008092242228624736256⟩,
    ⟨-3486155391960961563989518797,844460826148343979933418897408⟩⟩

def packet0401 : StripRowPacket :=
  ⟨⟨⟨7,15,5,8⟩,
    ![362,1245,2532,4035,5542,6848,7773],![395,1295,2581,4074,5569,6863,7780]⟩,
    ⟨-478583055910766130683,83550825971721053523968⟩,
    ⟨-77769658621996943388903,15955113297083338841255936⟩⟩

def packet0402 : StripRowPacket :=
  ⟨⟨⟨7,15,5,9⟩,
    ![386,1282,2567,4062,5560,6857,7776],![416,1330,2617,4103,5589,6873,7784]⟩,
    ⟨-37088038284500673775121,7352472685511452710109184⟩,
    ⟨-33427743568537516573883,7977556648541669420627968⟩⟩

def packet0403 : StripRowPacket :=
  ⟨⟨⟨7,14,5,10⟩,
    ![410,1322,2608,4095,5582,6869,7780],![437,1370,2660,4139,5613,6886,7788]⟩,
    ⟨-30206852794713013830188267273,7021381618504046121114312368128⟩,
    ⟨-5835338571766630929962552771,1688921652296687959866837794816⟩⟩

def packet0404 : StripRowPacket :=
  ⟨⟨⟨7,14,5,11⟩,
    ![428,1355,2644,4126,5603,6879,7783],![453,1402,2697,4171,5636,6898,7792]⟩,
    ⟨-50964825519304047098268235655,14042763237008092242228624736256⟩,
    ⟨-1174591589902834682986516987,422230413074171989966709448704⟩⟩

def packet0405 : StripRowPacket :=
  ⟨⟨⟨7,15,5,10⟩,
    ![407,1317,2603,4091,5580,6867,7780],![434,1364,2654,4134,5610,6885,7787]⟩,
    ⟨-16030383824426964025069,3676236342755726355054592⟩,
    ⟨-55941315652153122906629,15955113297083338841255936⟩⟩

def packet0406 : StripRowPacket :=
  ⟨⟨⟨7,15,5,11⟩,
    ![425,1350,2639,4122,5600,6878,7783],![450,1396,2691,4167,5633,6897,7791]⟩,
    ⟨-27033497013207182325155,7352472685511452710109184⟩,
    ⟨-1023344185618891196943,362616211297348610028544⟩⟩

def packet0407 : StripRowPacket :=
  ⟨⟨⟨7,12,5,12⟩,
    ![451,1398,2692,4166,5631,6894,7788],![475,1444,2745,4214,5666,6915,7797]⟩,
    ⟨-881520066829248719847617,305859505870009428250327040⟩,
    ⟨-7857331525432557841013219,3835361726292351782848921600⟩⟩

def packets016 : List StripRowPacket :=
  [packet0384, packet0385, packet0386, packet0387, packet0388, packet0389,
   packet0390, packet0391, packet0392, packet0393, packet0394, packet0395,
   packet0396, packet0397, packet0398, packet0399, packet0400, packet0401,
   packet0402, packet0403, packet0404, packet0405, packet0406, packet0407]

theorem packet0384_membership : packet0384 ∈ packets016 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0384_shape : checkStripShape packet0384.row = true := by
  decide +kernel

private theorem packet0384_cache : checkStripCache packet0384 = true := by
  decide +kernel

private theorem packet0384_pair (i : Fin 7) : checkEdgePair packet0384 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0384_ok : checkStripPacket packet0384 = true :=
  checkStripPacket_intro packet0384_shape packet0384_cache packet0384_pair

theorem packet0385_membership : packet0385 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0385_shape : checkStripShape packet0385.row = true := by
  decide +kernel

private theorem packet0385_cache : checkStripCache packet0385 = true := by
  decide +kernel

private theorem packet0385_pair (i : Fin 7) : checkEdgePair packet0385 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0385_ok : checkStripPacket packet0385 = true :=
  checkStripPacket_intro packet0385_shape packet0385_cache packet0385_pair

theorem packet0386_membership : packet0386 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0386_shape : checkStripShape packet0386.row = true := by
  decide +kernel

private theorem packet0386_cache : checkStripCache packet0386 = true := by
  decide +kernel

private theorem packet0386_pair (i : Fin 7) : checkEdgePair packet0386 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0386_ok : checkStripPacket packet0386 = true :=
  checkStripPacket_intro packet0386_shape packet0386_cache packet0386_pair

theorem packet0387_membership : packet0387 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0387_shape : checkStripShape packet0387.row = true := by
  decide +kernel

private theorem packet0387_cache : checkStripCache packet0387 = true := by
  decide +kernel

private theorem packet0387_pair (i : Fin 7) : checkEdgePair packet0387 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0387_ok : checkStripPacket packet0387 = true :=
  checkStripPacket_intro packet0387_shape packet0387_cache packet0387_pair

theorem packet0388_membership : packet0388 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0388_shape : checkStripShape packet0388.row = true := by
  decide +kernel

private theorem packet0388_cache : checkStripCache packet0388 = true := by
  decide +kernel

private theorem packet0388_pair (i : Fin 7) : checkEdgePair packet0388 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0388_ok : checkStripPacket packet0388 = true :=
  checkStripPacket_intro packet0388_shape packet0388_cache packet0388_pair

theorem packet0389_membership : packet0389 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0389_shape : checkStripShape packet0389.row = true := by
  decide +kernel

private theorem packet0389_cache : checkStripCache packet0389 = true := by
  decide +kernel

private theorem packet0389_pair (i : Fin 7) : checkEdgePair packet0389 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0389_ok : checkStripPacket packet0389 = true :=
  checkStripPacket_intro packet0389_shape packet0389_cache packet0389_pair

theorem packet0390_membership : packet0390 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0390_shape : checkStripShape packet0390.row = true := by
  decide +kernel

private theorem packet0390_cache : checkStripCache packet0390 = true := by
  decide +kernel

private theorem packet0390_pair (i : Fin 7) : checkEdgePair packet0390 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0390_ok : checkStripPacket packet0390 = true :=
  checkStripPacket_intro packet0390_shape packet0390_cache packet0390_pair

theorem packet0391_membership : packet0391 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0391_shape : checkStripShape packet0391.row = true := by
  decide +kernel

private theorem packet0391_cache : checkStripCache packet0391 = true := by
  decide +kernel

private theorem packet0391_pair (i : Fin 7) : checkEdgePair packet0391 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0391_ok : checkStripPacket packet0391 = true :=
  checkStripPacket_intro packet0391_shape packet0391_cache packet0391_pair

theorem packet0392_membership : packet0392 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0392_shape : checkStripShape packet0392.row = true := by
  decide +kernel

private theorem packet0392_cache : checkStripCache packet0392 = true := by
  decide +kernel

private theorem packet0392_pair (i : Fin 7) : checkEdgePair packet0392 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0392_ok : checkStripPacket packet0392 = true :=
  checkStripPacket_intro packet0392_shape packet0392_cache packet0392_pair

theorem packet0393_membership : packet0393 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0393_shape : checkStripShape packet0393.row = true := by
  decide +kernel

private theorem packet0393_cache : checkStripCache packet0393 = true := by
  decide +kernel

private theorem packet0393_pair (i : Fin 7) : checkEdgePair packet0393 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0393_ok : checkStripPacket packet0393 = true :=
  checkStripPacket_intro packet0393_shape packet0393_cache packet0393_pair

theorem packet0394_membership : packet0394 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0394_shape : checkStripShape packet0394.row = true := by
  decide +kernel

private theorem packet0394_cache : checkStripCache packet0394 = true := by
  decide +kernel

private theorem packet0394_pair (i : Fin 7) : checkEdgePair packet0394 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0394_ok : checkStripPacket packet0394 = true :=
  checkStripPacket_intro packet0394_shape packet0394_cache packet0394_pair

theorem packet0395_membership : packet0395 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0395_shape : checkStripShape packet0395.row = true := by
  decide +kernel

private theorem packet0395_cache : checkStripCache packet0395 = true := by
  decide +kernel

private theorem packet0395_pair (i : Fin 7) : checkEdgePair packet0395 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0395_ok : checkStripPacket packet0395 = true :=
  checkStripPacket_intro packet0395_shape packet0395_cache packet0395_pair

theorem packet0396_membership : packet0396 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0396_shape : checkStripShape packet0396.row = true := by
  decide +kernel

private theorem packet0396_cache : checkStripCache packet0396 = true := by
  decide +kernel

private theorem packet0396_pair (i : Fin 7) : checkEdgePair packet0396 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0396_ok : checkStripPacket packet0396 = true :=
  checkStripPacket_intro packet0396_shape packet0396_cache packet0396_pair

theorem packet0397_membership : packet0397 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0397_shape : checkStripShape packet0397.row = true := by
  decide +kernel

private theorem packet0397_cache : checkStripCache packet0397 = true := by
  decide +kernel

private theorem packet0397_pair (i : Fin 7) : checkEdgePair packet0397 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0397_ok : checkStripPacket packet0397 = true :=
  checkStripPacket_intro packet0397_shape packet0397_cache packet0397_pair

theorem packet0398_membership : packet0398 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0398_shape : checkStripShape packet0398.row = true := by
  decide +kernel

private theorem packet0398_cache : checkStripCache packet0398 = true := by
  decide +kernel

private theorem packet0398_pair (i : Fin 7) : checkEdgePair packet0398 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0398_ok : checkStripPacket packet0398 = true :=
  checkStripPacket_intro packet0398_shape packet0398_cache packet0398_pair

theorem packet0399_membership : packet0399 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0399_shape : checkStripShape packet0399.row = true := by
  decide +kernel

private theorem packet0399_cache : checkStripCache packet0399 = true := by
  decide +kernel

private theorem packet0399_pair (i : Fin 7) : checkEdgePair packet0399 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0399_ok : checkStripPacket packet0399 = true :=
  checkStripPacket_intro packet0399_shape packet0399_cache packet0399_pair

theorem packet0400_membership : packet0400 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0400_shape : checkStripShape packet0400.row = true := by
  decide +kernel

private theorem packet0400_cache : checkStripCache packet0400 = true := by
  decide +kernel

private theorem packet0400_pair (i : Fin 7) : checkEdgePair packet0400 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0400_ok : checkStripPacket packet0400 = true :=
  checkStripPacket_intro packet0400_shape packet0400_cache packet0400_pair

theorem packet0401_membership : packet0401 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0401_shape : checkStripShape packet0401.row = true := by
  decide +kernel

private theorem packet0401_cache : checkStripCache packet0401 = true := by
  decide +kernel

private theorem packet0401_pair (i : Fin 7) : checkEdgePair packet0401 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0401_ok : checkStripPacket packet0401 = true :=
  checkStripPacket_intro packet0401_shape packet0401_cache packet0401_pair

theorem packet0402_membership : packet0402 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0402_shape : checkStripShape packet0402.row = true := by
  decide +kernel

private theorem packet0402_cache : checkStripCache packet0402 = true := by
  decide +kernel

private theorem packet0402_pair (i : Fin 7) : checkEdgePair packet0402 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0402_ok : checkStripPacket packet0402 = true :=
  checkStripPacket_intro packet0402_shape packet0402_cache packet0402_pair

theorem packet0403_membership : packet0403 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0403_shape : checkStripShape packet0403.row = true := by
  decide +kernel

private theorem packet0403_cache : checkStripCache packet0403 = true := by
  decide +kernel

private theorem packet0403_pair (i : Fin 7) : checkEdgePair packet0403 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0403_ok : checkStripPacket packet0403 = true :=
  checkStripPacket_intro packet0403_shape packet0403_cache packet0403_pair

theorem packet0404_membership : packet0404 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0404_shape : checkStripShape packet0404.row = true := by
  decide +kernel

private theorem packet0404_cache : checkStripCache packet0404 = true := by
  decide +kernel

private theorem packet0404_pair (i : Fin 7) : checkEdgePair packet0404 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0404_ok : checkStripPacket packet0404 = true :=
  checkStripPacket_intro packet0404_shape packet0404_cache packet0404_pair

theorem packet0405_membership : packet0405 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0405_shape : checkStripShape packet0405.row = true := by
  decide +kernel

private theorem packet0405_cache : checkStripCache packet0405 = true := by
  decide +kernel

private theorem packet0405_pair (i : Fin 7) : checkEdgePair packet0405 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0405_ok : checkStripPacket packet0405 = true :=
  checkStripPacket_intro packet0405_shape packet0405_cache packet0405_pair

theorem packet0406_membership : packet0406 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0406_shape : checkStripShape packet0406.row = true := by
  decide +kernel

private theorem packet0406_cache : checkStripCache packet0406 = true := by
  decide +kernel

private theorem packet0406_pair (i : Fin 7) : checkEdgePair packet0406 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0406_ok : checkStripPacket packet0406 = true :=
  checkStripPacket_intro packet0406_shape packet0406_cache packet0406_pair

theorem packet0407_membership : packet0407 ∈ packets016 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0407_shape : checkStripShape packet0407.row = true := by
  decide +kernel

private theorem packet0407_cache : checkStripCache packet0407 = true := by
  decide +kernel

private theorem packet0407_pair (i : Fin 7) : checkEdgePair packet0407 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0407_ok : checkStripPacket packet0407 = true :=
  checkStripPacket_intro packet0407_shape packet0407_cache packet0407_pair

theorem packets016_checked : packets016.all checkStripPacket = true := by
  simp only [packets016, List.all_cons, List.all_nil, Bool.true_and, packet0384_ok,
    packet0385_ok, packet0386_ok, packet0387_ok, packet0388_ok, packet0389_ok,
    packet0390_ok, packet0391_ok, packet0392_ok, packet0393_ok, packet0394_ok,
    packet0395_ok, packet0396_ok, packet0397_ok, packet0398_ok, packet0399_ok,
    packet0400_ok, packet0401_ok, packet0402_ok, packet0403_ok, packet0404_ok,
    packet0405_ok, packet0406_ok, packet0407_ok]

theorem packets016_valid : packets016.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
