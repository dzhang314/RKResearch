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

def packet0552 : StripRowPacket :=
  ⟨⟨⟨7,16,5,10⟩,
    ![404,1312,2598,4087,5577,6866,7779],![431,1359,2649,4130,5607,6883,7787]⟩,
    ⟨-3645632413670714019507,825146379157359597578240⟩,
    ⟨-40531792847257693041793,11396789927450648088248320⟩⟩

def packet0553 : StripRowPacket :=
  ⟨⟨⟨7,16,5,11⟩,
    ![422,1346,2634,4118,5598,6877,7783],![447,1391,2686,4163,5630,6895,7791]⟩,
    ⟨-9656861591621538480761,2593317191637415878103040⟩,
    ⟨-105997127652073961429077,37039567264214606286807040⟩⟩

def packet0554 : StripRowPacket :=
  ⟨⟨⟨7,17,5,10⟩,
    ![402,1308,2593,4083,5574,6864,7779],![428,1354,2644,4126,5604,6882,7786]⟩,
    ⟨-137892602352480433640182537,30813834081366525577044377600⟩,
    ⟨-210327502066338146750634089,58329115268625656050539806720⟩⟩

def packet0555 : StripRowPacket :=
  ⟨⟨⟨7,17,5,11⟩,
    ![420,1341,2630,4114,5595,6875,7782],![444,1386,2681,4158,5627,6894,7790]⟩,
    ⟨-3020492268824286129998975131,801159686115529665003153817600⟩,
    ⟨-296096156695361323470168151,102075951720094898088444661760⟩⟩

def packet0556 : StripRowPacket :=
  ⟨⟨⟨7,18,5,8⟩,
    ![356,1232,2517,4022,5534,6843,7772],![388,1281,2565,4061,5560,6858,7779]⟩,
    ⟨-7788705346648560831777589,1306517567500749622608578560⟩,
    ⟨-1040298810184288544898274713,204568547163246722195687833600⟩⟩

def packet0557 : StripRowPacket :=
  ⟨⟨⟨7,18,5,9⟩,
    ![380,1269,2553,4050,5552,6853,7775],![408,1316,2602,4090,5580,6869,7782]⟩,
    ⟨-54834920250851760342130061,10452140540005996980868628480⟩,
    ⟨-790806042051431200991475311,180964484029025946557723852800⟩⟩

def packet0558 : StripRowPacket :=
  ⟨⟨⟨7,19,5,8⟩,
    ![354,1228,2513,4018,5531,6842,7772],![386,1276,2560,4057,5557,6857,7778]⟩,
    ⟨-688723560269512928864337653,114083286734430805481304682496⟩,
    ⟨-133568509154909128611691,25918229227485355948515328⟩⟩

def packet0559 : StripRowPacket :=
  ⟨⟨⟨7,19,5,9⟩,
    ![378,1265,2548,4046,5549,6851,7775],![406,1312,2597,4086,5577,6867,7782]⟩,
    ⟨-4847899213124483175381507101,912666293875446443850437459968⟩,
    ⟨-57383036487414579798911,12959114613742677974257664⟩⟩

def packet0560 : StripRowPacket :=
  ⟨⟨⟨7,18,5,10⟩,
    ![400,1304,2589,4079,5571,6863,7778],![425,1350,2639,4122,5602,6880,7786]⟩,
    ⟨-4736019772851503403003941,1045214054000599698086862848⟩,
    ⟨-17195041552435785918896397773,4705076584754674610500820172800⟩⟩

def packet0561 : StripRowPacket :=
  ⟨⟨⟨7,18,5,11⟩,
    ![417,1337,2625,4110,5592,6874,7782],![441,1381,2676,4154,5624,6892,7790]⟩,
    ⟨-39885475206178307717948759,10452140540005996980868628480⟩,
    ⟨-691456300576718030600721873,235253829237733730525041008640⟩⟩

def packet0562 : StripRowPacket :=
  ⟨⟨⟨7,19,5,10⟩,
    ![398,1300,2584,4075,5569,6861,7778],![423,1345,2634,4118,5599,6879,7785]⟩,
    ⟨-2093004972046431459924156489,456333146937723221925218729984⟩,
    ⟨-95963636794749190583953,25918229227485355948515328⟩⟩

def packet0563 : StripRowPacket :=
  ⟨⟨⟨7,19,5,11⟩,
    ![415,1333,2621,4106,5590,6872,7781],![438,1377,2671,4150,5622,6891,7789]⟩,
    ⟨-3524120675061242664315118855,912666293875446443850437459968⟩,
    ⟨-19290300153667305392521,6479557306871338987128832⟩⟩

def packet0564 : StripRowPacket :=
  ⟨⟨⟨7,16,4,6⟩,
    ![438,1377,2671,4149,5620,6889,7786],![472,1448,2758,4231,5681,6923,7800]⟩,
    ⟨-2749607459097291515075,907661017073095557336064⟩,
    ⟨-9915405354372159911923,6734466775311746597601280⟩⟩

def packet0565 : StripRowPacket :=
  ⟨⟨⟨7,17,4,6⟩,
    ![435,1373,2666,4145,5617,6887,7786],![469,1443,2753,4227,5678,6922,7799]⟩,
    ⟨-24557768764840809853532043,8011596861155296650031538176⟩,
    ⟨-304284425707800913566570283,204151903440189796176889323520⟩⟩

def packet0566 : StripRowPacket :=
  ⟨⟨⟨6,8,4,7⟩,
    ![460,1427,2734,4209,5664,6913,7794],![494,1500,2832,4307,5741,6959,7812]⟩,
    ⟨-5939792750277719891,3430821849901467507200⟩,
    ⟨13632123742654691,7135176646147793351680⟩⟩

def packet0567 : StripRowPacket :=
  ⟨⟨⟨7,18,4,6⟩,
    ![433,1368,2662,4142,5615,6886,7786],![466,1438,2748,4223,5675,6920,7799]⟩,
    ⟨-8102688170960395351464527,2613035135001499245217157120⟩,
    ⟨-3548647464865754999125258417,2352538292377337305250410086400⟩⟩

def packet0568 : StripRowPacket :=
  ⟨⟨⟨7,19,4,6⟩,
    ![431,1364,2657,4138,5612,6884,7785],![464,1434,2744,4219,5672,6919,7798]⟩,
    ⟨-715557851507405602195481183,228166573468861610962609364992⟩,
    ⟨-2825452018179234538739,1851302087677525424893952⟩⟩

def packet0569 : StripRowPacket :=
  ⟨⟨⟨6,9,4,7⟩,
    ![455,1418,2725,4202,5659,6910,7793],![487,1490,2821,4299,5736,6956,7811]⟩,
    ⟨-526441184115676495365779,299366519284346377303531520⟩,
    ⟨359560688353119679,87749166749673210073600⟩⟩

def packet0570 : StripRowPacket :=
  ⟨⟨⟨7,20,5,8⟩,
    ![352,1224,2508,4014,5528,6840,7771],![384,1272,2556,4053,5555,6855,7778]⟩,
    ⟨-903682082915126533858549,147862896853003038746389504⟩,
    ⟨-5551779619145049816730972619,1063441075949301204146602344448⟩⟩

def packet0571 : StripRowPacket :=
  ⟨⟨⟨7,20,5,9⟩,
    ![376,1261,2544,4042,5547,6850,7774],![403,1307,2592,4083,5575,6866,7781]⟩,
    ⟨-82678013243947176359182929,15377741272712316029624508416⟩,
    ⟨-2384883127237821140349187839,531720537974650602073301172224⟩⟩

def packet0572 : StripRowPacket :=
  ⟨⟨⟨7,21,5,8⟩,
    ![351,1221,2504,4011,5526,6839,7771],![382,1268,2551,4049,5552,6854,7777]⟩,
    ⟨-3476839492123468654403400211,562116338492932513073779240960⟩,
    ⟨-205379905224823068101111989857,38848015718345543687660035358720⟩⟩

def packet0573 : StripRowPacket :=
  ⟨⟨⟨7,21,5,9⟩,
    ![374,1257,2540,4039,5544,6848,7774],![401,1303,2588,4079,5572,6864,7781]⟩,
    ⟨-24464878197319563071082125291,4496930707943460104590233927680⟩,
    ⟨-17643357723878921985646285657,3884801571834554368766003535872⟩⟩

def packet0574 : StripRowPacket :=
  ⟨⟨⟨7,20,4,5⟩,
    ![396,1296,2580,4072,5566,6860,7777],![436,1372,2666,4147,5619,6890,7789]⟩,
    ⟨-35686544932360596598538381,7688870636356158014812254208⟩,
    ⟨-801434881284206802158295449,265860268987325301036650586112⟩⟩

def packet0575 : StripRowPacket :=
  ⟨⟨⟨7,21,4,5⟩,
    ![394,1292,2576,4068,5564,6859,7777],![434,1368,2662,4143,5617,6888,7788]⟩,
    ⟨-10557520228825688453468524447,2248465353971730052295116963840⟩,
    ⟨-29635230316680380841791147499,9712003929586385921915008839680⟩⟩

def packets023 : List StripRowPacket :=
  [packet0552, packet0553, packet0554, packet0555, packet0556, packet0557,
   packet0558, packet0559, packet0560, packet0561, packet0562, packet0563,
   packet0564, packet0565, packet0566, packet0567, packet0568, packet0569,
   packet0570, packet0571, packet0572, packet0573, packet0574, packet0575]

theorem packet0552_membership : packet0552 ∈ packets023 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0552_shape : checkStripShape packet0552.row = true := by
  decide +kernel

private theorem packet0552_cache : checkStripCache packet0552 = true := by
  decide +kernel

private theorem packet0552_pair (i : Fin 7) : checkEdgePair packet0552 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0552_ok : checkStripPacket packet0552 = true :=
  checkStripPacket_intro packet0552_shape packet0552_cache packet0552_pair

theorem packet0553_membership : packet0553 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0553_shape : checkStripShape packet0553.row = true := by
  decide +kernel

private theorem packet0553_cache : checkStripCache packet0553 = true := by
  decide +kernel

private theorem packet0553_pair (i : Fin 7) : checkEdgePair packet0553 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0553_ok : checkStripPacket packet0553 = true :=
  checkStripPacket_intro packet0553_shape packet0553_cache packet0553_pair

theorem packet0554_membership : packet0554 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0554_shape : checkStripShape packet0554.row = true := by
  decide +kernel

private theorem packet0554_cache : checkStripCache packet0554 = true := by
  decide +kernel

private theorem packet0554_pair (i : Fin 7) : checkEdgePair packet0554 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0554_ok : checkStripPacket packet0554 = true :=
  checkStripPacket_intro packet0554_shape packet0554_cache packet0554_pair

theorem packet0555_membership : packet0555 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0555_shape : checkStripShape packet0555.row = true := by
  decide +kernel

private theorem packet0555_cache : checkStripCache packet0555 = true := by
  decide +kernel

private theorem packet0555_pair (i : Fin 7) : checkEdgePair packet0555 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0555_ok : checkStripPacket packet0555 = true :=
  checkStripPacket_intro packet0555_shape packet0555_cache packet0555_pair

theorem packet0556_membership : packet0556 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0556_shape : checkStripShape packet0556.row = true := by
  decide +kernel

private theorem packet0556_cache : checkStripCache packet0556 = true := by
  decide +kernel

private theorem packet0556_pair (i : Fin 7) : checkEdgePair packet0556 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0556_ok : checkStripPacket packet0556 = true :=
  checkStripPacket_intro packet0556_shape packet0556_cache packet0556_pair

theorem packet0557_membership : packet0557 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0557_shape : checkStripShape packet0557.row = true := by
  decide +kernel

private theorem packet0557_cache : checkStripCache packet0557 = true := by
  decide +kernel

private theorem packet0557_pair (i : Fin 7) : checkEdgePair packet0557 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0557_ok : checkStripPacket packet0557 = true :=
  checkStripPacket_intro packet0557_shape packet0557_cache packet0557_pair

theorem packet0558_membership : packet0558 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0558_shape : checkStripShape packet0558.row = true := by
  decide +kernel

private theorem packet0558_cache : checkStripCache packet0558 = true := by
  decide +kernel

private theorem packet0558_pair (i : Fin 7) : checkEdgePair packet0558 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0558_ok : checkStripPacket packet0558 = true :=
  checkStripPacket_intro packet0558_shape packet0558_cache packet0558_pair

theorem packet0559_membership : packet0559 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0559_shape : checkStripShape packet0559.row = true := by
  decide +kernel

private theorem packet0559_cache : checkStripCache packet0559 = true := by
  decide +kernel

private theorem packet0559_pair (i : Fin 7) : checkEdgePair packet0559 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0559_ok : checkStripPacket packet0559 = true :=
  checkStripPacket_intro packet0559_shape packet0559_cache packet0559_pair

theorem packet0560_membership : packet0560 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0560_shape : checkStripShape packet0560.row = true := by
  decide +kernel

private theorem packet0560_cache : checkStripCache packet0560 = true := by
  decide +kernel

private theorem packet0560_pair (i : Fin 7) : checkEdgePair packet0560 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0560_ok : checkStripPacket packet0560 = true :=
  checkStripPacket_intro packet0560_shape packet0560_cache packet0560_pair

theorem packet0561_membership : packet0561 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0561_shape : checkStripShape packet0561.row = true := by
  decide +kernel

private theorem packet0561_cache : checkStripCache packet0561 = true := by
  decide +kernel

private theorem packet0561_pair (i : Fin 7) : checkEdgePair packet0561 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0561_ok : checkStripPacket packet0561 = true :=
  checkStripPacket_intro packet0561_shape packet0561_cache packet0561_pair

theorem packet0562_membership : packet0562 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0562_shape : checkStripShape packet0562.row = true := by
  decide +kernel

private theorem packet0562_cache : checkStripCache packet0562 = true := by
  decide +kernel

private theorem packet0562_pair (i : Fin 7) : checkEdgePair packet0562 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0562_ok : checkStripPacket packet0562 = true :=
  checkStripPacket_intro packet0562_shape packet0562_cache packet0562_pair

theorem packet0563_membership : packet0563 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0563_shape : checkStripShape packet0563.row = true := by
  decide +kernel

private theorem packet0563_cache : checkStripCache packet0563 = true := by
  decide +kernel

private theorem packet0563_pair (i : Fin 7) : checkEdgePair packet0563 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0563_ok : checkStripPacket packet0563 = true :=
  checkStripPacket_intro packet0563_shape packet0563_cache packet0563_pair

theorem packet0564_membership : packet0564 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0564_shape : checkStripShape packet0564.row = true := by
  decide +kernel

private theorem packet0564_cache : checkStripCache packet0564 = true := by
  decide +kernel

private theorem packet0564_pair (i : Fin 7) : checkEdgePair packet0564 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0564_ok : checkStripPacket packet0564 = true :=
  checkStripPacket_intro packet0564_shape packet0564_cache packet0564_pair

theorem packet0565_membership : packet0565 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0565_shape : checkStripShape packet0565.row = true := by
  decide +kernel

private theorem packet0565_cache : checkStripCache packet0565 = true := by
  decide +kernel

private theorem packet0565_pair (i : Fin 7) : checkEdgePair packet0565 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0565_ok : checkStripPacket packet0565 = true :=
  checkStripPacket_intro packet0565_shape packet0565_cache packet0565_pair

theorem packet0566_membership : packet0566 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0566_shape : checkStripShape packet0566.row = true := by
  decide +kernel

private theorem packet0566_cache : checkStripCache packet0566 = true := by
  decide +kernel

private theorem packet0566_pair (i : Fin 7) : checkEdgePair packet0566 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0566_ok : checkStripPacket packet0566 = true :=
  checkStripPacket_intro packet0566_shape packet0566_cache packet0566_pair

theorem packet0567_membership : packet0567 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0567_shape : checkStripShape packet0567.row = true := by
  decide +kernel

private theorem packet0567_cache : checkStripCache packet0567 = true := by
  decide +kernel

private theorem packet0567_pair (i : Fin 7) : checkEdgePair packet0567 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0567_ok : checkStripPacket packet0567 = true :=
  checkStripPacket_intro packet0567_shape packet0567_cache packet0567_pair

theorem packet0568_membership : packet0568 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0568_shape : checkStripShape packet0568.row = true := by
  decide +kernel

private theorem packet0568_cache : checkStripCache packet0568 = true := by
  decide +kernel

private theorem packet0568_pair (i : Fin 7) : checkEdgePair packet0568 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0568_ok : checkStripPacket packet0568 = true :=
  checkStripPacket_intro packet0568_shape packet0568_cache packet0568_pair

theorem packet0569_membership : packet0569 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0569_shape : checkStripShape packet0569.row = true := by
  decide +kernel

private theorem packet0569_cache : checkStripCache packet0569 = true := by
  decide +kernel

private theorem packet0569_pair (i : Fin 7) : checkEdgePair packet0569 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0569_ok : checkStripPacket packet0569 = true :=
  checkStripPacket_intro packet0569_shape packet0569_cache packet0569_pair

theorem packet0570_membership : packet0570 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0570_shape : checkStripShape packet0570.row = true := by
  decide +kernel

private theorem packet0570_cache : checkStripCache packet0570 = true := by
  decide +kernel

private theorem packet0570_pair (i : Fin 7) : checkEdgePair packet0570 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0570_ok : checkStripPacket packet0570 = true :=
  checkStripPacket_intro packet0570_shape packet0570_cache packet0570_pair

theorem packet0571_membership : packet0571 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0571_shape : checkStripShape packet0571.row = true := by
  decide +kernel

private theorem packet0571_cache : checkStripCache packet0571 = true := by
  decide +kernel

private theorem packet0571_pair (i : Fin 7) : checkEdgePair packet0571 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0571_ok : checkStripPacket packet0571 = true :=
  checkStripPacket_intro packet0571_shape packet0571_cache packet0571_pair

theorem packet0572_membership : packet0572 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0572_shape : checkStripShape packet0572.row = true := by
  decide +kernel

private theorem packet0572_cache : checkStripCache packet0572 = true := by
  decide +kernel

private theorem packet0572_pair (i : Fin 7) : checkEdgePair packet0572 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0572_ok : checkStripPacket packet0572 = true :=
  checkStripPacket_intro packet0572_shape packet0572_cache packet0572_pair

theorem packet0573_membership : packet0573 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0573_shape : checkStripShape packet0573.row = true := by
  decide +kernel

private theorem packet0573_cache : checkStripCache packet0573 = true := by
  decide +kernel

private theorem packet0573_pair (i : Fin 7) : checkEdgePair packet0573 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0573_ok : checkStripPacket packet0573 = true :=
  checkStripPacket_intro packet0573_shape packet0573_cache packet0573_pair

theorem packet0574_membership : packet0574 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0574_shape : checkStripShape packet0574.row = true := by
  decide +kernel

private theorem packet0574_cache : checkStripCache packet0574 = true := by
  decide +kernel

private theorem packet0574_pair (i : Fin 7) : checkEdgePair packet0574 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0574_ok : checkStripPacket packet0574 = true :=
  checkStripPacket_intro packet0574_shape packet0574_cache packet0574_pair

theorem packet0575_membership : packet0575 ∈ packets023 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0575_shape : checkStripShape packet0575.row = true := by
  decide +kernel

private theorem packet0575_cache : checkStripCache packet0575 = true := by
  decide +kernel

private theorem packet0575_pair (i : Fin 7) : checkEdgePair packet0575 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0575_ok : checkStripPacket packet0575 = true :=
  checkStripPacket_intro packet0575_shape packet0575_cache packet0575_pair

theorem packets023_checked : packets023.all checkStripPacket = true := by
  simp only [packets023, List.all_cons, List.all_nil, Bool.true_and, packet0552_ok,
    packet0553_ok, packet0554_ok, packet0555_ok, packet0556_ok, packet0557_ok,
    packet0558_ok, packet0559_ok, packet0560_ok, packet0561_ok, packet0562_ok,
    packet0563_ok, packet0564_ok, packet0565_ok, packet0566_ok, packet0567_ok,
    packet0568_ok, packet0569_ok, packet0570_ok, packet0571_ok, packet0572_ok,
    packet0573_ok, packet0574_ok, packet0575_ok]

theorem packets023_valid : packets023.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
