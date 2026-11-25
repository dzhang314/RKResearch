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

def packet0600 : StripRowPacket :=
  ⟨⟨⟨6,14,4,2⟩,
    ![204,1040,2342,3885,5443,6797,7757],![300,1136,2419,3944,5482,6818,7766]⟩,
    ⟨-155428612631087048343983,15485480686287990208030720⟩,
    ⟨-96572843047519847338391851,11878586471125139346398371840⟩⟩

def packet0601 : StripRowPacket :=
  ⟨⟨⟨6,14,4,3⟩,
    ![281,1117,2405,3931,5472,6811,7762],![352,1211,2489,3997,5517,6836,7772]⟩,
    ⟨-2864812423184736146572719,340680575098335784576675840⟩,
    ⟨-19307021306307677757227641,2969646617781284836599592960⟩⟩

def packet0602 : StripRowPacket :=
  ⟨⟨⟨6,15,4,2⟩,
    ![204,1035,2335,3879,5439,6794,7757],![298,1131,2412,3937,5478,6815,7765]⟩,
    ⟨-283054287308373100473,27644420023448561315840⟩,
    ⟨-3456574521551376573,416315055438384593920⟩⟩

def packet0603 : StripRowPacket :=
  ⟨⟨⟨6,15,4,3⟩,
    ![280,1112,2398,3925,5468,6809,7761],![350,1205,2482,3991,5512,6833,7771]⟩,
    ⟨-3315878131788239269,386635245083196661760⟩,
    ⟨-691018840320065131,104078763859596148480⟩⟩

def packet0604 : StripRowPacket :=
  ⟨⟨⟨7,24,4,4⟩,
    ![347,1211,2492,4000,5518,6835,7769],![396,1292,2575,4068,5564,6860,7779]⟩,
    ⟨-13158029463274946185633,2055641090543417892582496⟩,
    ⟨-5026076619888828731171743,1067896561966680596896858112⟩⟩

def packet0605 : StripRowPacket :=
  ⟨⟨⟨7,25,4,4⟩,
    ![345,1207,2488,3997,5516,6834,7769],![395,1289,2571,4064,5562,6859,7779]⟩,
    ⟨-102482175840312315525625451399,15836640602325159002320529813504⟩,
    ⟨-152903002243965671360471863963,32121508226527571785025872519168⟩⟩

def packet0606 : StripRowPacket :=
  ⟨⟨⟨7,24,4,5⟩,
    ![389,1282,2564,4058,5557,6855,7776],![428,1357,2649,4132,5609,6884,7787]⟩,
    ⟨-159654790296900551267311,32890257448694686281319936⟩,
    ⟨-129766071689244979791261,41072944691026176803725312⟩⟩

def packet0607 : StripRowPacket :=
  ⟨⟨⟨7,25,4,5⟩,
    ![388,1279,2560,4054,5554,6854,7775],![426,1353,2645,4129,5607,6883,7787]⟩,
    ⟨-310775753445192612182834162787,63346562409300636009282119254016⟩,
    ⟨-51307184764257254366497562813,16060754113263785892512936259584⟩⟩

def packet0608 : StripRowPacket :=
  ⟨⟨⟨7,26,4,4⟩,
    ![344,1205,2485,3993,5513,6832,7769],![393,1286,2568,4061,5560,6858,7779]⟩,
    ⟨-24025185106211862720820081,3673167708974050499659663360⟩,
    ⟨-69707960334708506722890964989,14482808337657199409963421712384⟩⟩

def packet0609 : StripRowPacket :=
  ⟨⟨⟨7,27,4,4⟩,
    ![343,1202,2481,3990,5511,6831,7768],![392,1283,2564,4058,5557,6857,7778]⟩,
    ⟨-415054423847892763973726881,62796372082398193890651320320⟩,
    ⟨-1071257985641892570251219,220170973850401474735943680⟩⟩

def packet0610 : StripRowPacket :=
  ⟨⟨⟨6,13,4,5⟩,
    ![384,1271,2551,4046,5549,6851,7774],![425,1352,2644,4128,5606,6883,7787]⟩,
    ⟨-324569552273753998409873,64218851331793469408092160⟩,
    ⟨-40033886109106552267853,12610357791909691564042240⟩⟩

def packet0611 : StripRowPacket :=
  ⟨⟨⟨6,12,4,6⟩,
    ![418,1341,2631,4115,5597,6876,7782],![453,1415,2725,4204,5663,6914,7797]⟩,
    ⟨-3683986353190936560709,1084321697863832355040256⟩,
    ⟨-13807923067394623432945,8926124595461024915611648⟩⟩

def packet0612 : StripRowPacket :=
  ⟨⟨⟨6,12,4,7⟩,
    ![443,1396,2702,4183,5646,6903,7791],![472,1463,2794,4276,5721,6948,7808]⟩,
    ⟨-3994038000679133631217,2168643395727664710080512⟩,
    ⟨10648304236795079417,1115765574432628114451456⟩⟩

def packet0613 : StripRowPacket :=
  ⟨⟨⟨6,13,4,6⟩,
    ![415,1335,2624,4109,5592,6874,7782],![449,1408,2717,4197,5658,6912,7796]⟩,
    ⟨-3179088553495087139828485,918329574044646612535717888⟩,
    ⟨-438825656517146930414467,277427871422013214408929280⟩⟩

def packet0614 : StripRowPacket :=
  ⟨⟨⟨6,13,4,7⟩,
    ![440,1390,2695,4177,5642,6901,7791],![468,1456,2786,4270,5716,6946,7808]⟩,
    ⟨-17168325094754921023957861,9183295740446466125357178880⟩,
    ⟨386772670756286132979,34678483927751651801116160⟩⟩

def packet0615 : StripRowPacket :=
  ⟨⟨⟨6,14,4,4⟩,
    ![339,1194,2473,3983,5506,6828,7767],![391,1282,2562,4056,5556,6856,7778]⟩,
    ⟨-577548842121389307394453,85170143774583946144168960⟩,
    ⟨-5262120672994688610857207,1079871497375012667854397440⟩⟩

def packet0616 : StripRowPacket :=
  ⟨⟨⟨6,14,4,5⟩,
    ![382,1266,2544,4040,5544,6848,7774],![422,1346,2637,4121,5602,6880,7786]⟩,
    ⟨-351115662757275662516581,68136115019667156915335168⟩,
    ⟨-3853856958065243840994799,1187858647112513934639837184⟩⟩

def packet0617 : StripRowPacket :=
  ⟨⟨⟨6,15,4,4⟩,
    ![337,1189,2466,3977,5502,6826,7767],![389,1276,2555,4050,5552,6854,7777]⟩,
    ⟨-95558142768672557497,13822210011724280657920⟩,
    ⟨-414315240201828895,83263011087676918784⟩⟩

def packet0618 : StripRowPacket :=
  ⟨⟨⟨6,15,4,5⟩,
    ![380,1261,2538,4035,5540,6846,7773],![419,1340,2630,4115,5597,6878,7785]⟩,
    ⟨-290294569303662244509,55288840046897122631680⟩,
    ⟨-689538520369014213,208157527719192296960⟩⟩

def packet0619 : StripRowPacket :=
  ⟨⟨⟨6,14,4,6⟩,
    ![413,1329,2617,4103,5588,6872,7781],![446,1401,2709,4191,5653,6909,7795]⟩,
    ⟨-600480629543599697793999,170340287549167892288337920⟩,
    ⟨-19193811758363302100466703,11878586471125139346398371840⟩⟩

def packet0620 : StripRowPacket :=
  ⟨⟨⟨6,14,4,7⟩,
    ![437,1384,2689,4171,5638,6899,7790],![465,1449,2778,4263,5712,6943,7807]⟩,
    ⟨-646344204388020478593091,340680575098335784576675840⟩,
    ⟨18868257990729276126823,1484823308890642418299796480⟩⟩

def packet0621 : StripRowPacket :=
  ⟨⟨⟨6,15,4,6⟩,
    ![410,1324,2611,4098,5584,6870,7780],![443,1395,2702,4185,5649,6907,7795]⟩,
    ⟨-19835656753263425903,5528884004689712263168⟩,
    ⟨-686577880466912377,416315055438384593920⟩⟩

def packet0622 : StripRowPacket :=
  ⟨⟨⟨6,15,4,7⟩,
    ![434,1379,2682,4166,5634,6897,7789],![461,1443,2771,4257,5708,6941,7806]⟩,
    ⟨-106418565761606273551,55288840046897122631680⟩,
    ⟨740159975525459,52039381929798074240⟩⟩

def packet0623 : StripRowPacket :=
  ⟨⟨⟨6,8,4,8⟩,
    ![480,1476,2802,4279,5719,6944,7805],![510,1542,2896,4380,5805,6999,7826]⟩,
    ⟨-1370607617723581,4123583954208494600⟩,
    ⟨80022867740205427579,57081413169182346813440⟩⟩

def packets025 : List StripRowPacket :=
  [packet0600, packet0601, packet0602, packet0603, packet0604, packet0605,
   packet0606, packet0607, packet0608, packet0609, packet0610, packet0611,
   packet0612, packet0613, packet0614, packet0615, packet0616, packet0617,
   packet0618, packet0619, packet0620, packet0621, packet0622, packet0623]

theorem packet0600_membership : packet0600 ∈ packets025 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0600_shape : checkStripShape packet0600.row = true := by
  decide +kernel

private theorem packet0600_cache : checkStripCache packet0600 = true := by
  decide +kernel

private theorem packet0600_pair (i : Fin 7) : checkEdgePair packet0600 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0600_ok : checkStripPacket packet0600 = true :=
  checkStripPacket_intro packet0600_shape packet0600_cache packet0600_pair

theorem packet0601_membership : packet0601 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0601_shape : checkStripShape packet0601.row = true := by
  decide +kernel

private theorem packet0601_cache : checkStripCache packet0601 = true := by
  decide +kernel

private theorem packet0601_pair (i : Fin 7) : checkEdgePair packet0601 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0601_ok : checkStripPacket packet0601 = true :=
  checkStripPacket_intro packet0601_shape packet0601_cache packet0601_pair

theorem packet0602_membership : packet0602 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0602_shape : checkStripShape packet0602.row = true := by
  decide +kernel

private theorem packet0602_cache : checkStripCache packet0602 = true := by
  decide +kernel

private theorem packet0602_pair (i : Fin 7) : checkEdgePair packet0602 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0602_ok : checkStripPacket packet0602 = true :=
  checkStripPacket_intro packet0602_shape packet0602_cache packet0602_pair

theorem packet0603_membership : packet0603 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0603_shape : checkStripShape packet0603.row = true := by
  decide +kernel

private theorem packet0603_cache : checkStripCache packet0603 = true := by
  decide +kernel

private theorem packet0603_pair (i : Fin 7) : checkEdgePair packet0603 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0603_ok : checkStripPacket packet0603 = true :=
  checkStripPacket_intro packet0603_shape packet0603_cache packet0603_pair

theorem packet0604_membership : packet0604 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0604_shape : checkStripShape packet0604.row = true := by
  decide +kernel

private theorem packet0604_cache : checkStripCache packet0604 = true := by
  decide +kernel

private theorem packet0604_pair (i : Fin 7) : checkEdgePair packet0604 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0604_ok : checkStripPacket packet0604 = true :=
  checkStripPacket_intro packet0604_shape packet0604_cache packet0604_pair

theorem packet0605_membership : packet0605 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0605_shape : checkStripShape packet0605.row = true := by
  decide +kernel

private theorem packet0605_cache : checkStripCache packet0605 = true := by
  decide +kernel

private theorem packet0605_pair (i : Fin 7) : checkEdgePair packet0605 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0605_ok : checkStripPacket packet0605 = true :=
  checkStripPacket_intro packet0605_shape packet0605_cache packet0605_pair

theorem packet0606_membership : packet0606 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0606_shape : checkStripShape packet0606.row = true := by
  decide +kernel

private theorem packet0606_cache : checkStripCache packet0606 = true := by
  decide +kernel

private theorem packet0606_pair (i : Fin 7) : checkEdgePair packet0606 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0606_ok : checkStripPacket packet0606 = true :=
  checkStripPacket_intro packet0606_shape packet0606_cache packet0606_pair

theorem packet0607_membership : packet0607 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0607_shape : checkStripShape packet0607.row = true := by
  decide +kernel

private theorem packet0607_cache : checkStripCache packet0607 = true := by
  decide +kernel

private theorem packet0607_pair (i : Fin 7) : checkEdgePair packet0607 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0607_ok : checkStripPacket packet0607 = true :=
  checkStripPacket_intro packet0607_shape packet0607_cache packet0607_pair

theorem packet0608_membership : packet0608 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0608_shape : checkStripShape packet0608.row = true := by
  decide +kernel

private theorem packet0608_cache : checkStripCache packet0608 = true := by
  decide +kernel

private theorem packet0608_pair (i : Fin 7) : checkEdgePair packet0608 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0608_ok : checkStripPacket packet0608 = true :=
  checkStripPacket_intro packet0608_shape packet0608_cache packet0608_pair

theorem packet0609_membership : packet0609 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0609_shape : checkStripShape packet0609.row = true := by
  decide +kernel

private theorem packet0609_cache : checkStripCache packet0609 = true := by
  decide +kernel

private theorem packet0609_pair (i : Fin 7) : checkEdgePair packet0609 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0609_ok : checkStripPacket packet0609 = true :=
  checkStripPacket_intro packet0609_shape packet0609_cache packet0609_pair

theorem packet0610_membership : packet0610 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0610_shape : checkStripShape packet0610.row = true := by
  decide +kernel

private theorem packet0610_cache : checkStripCache packet0610 = true := by
  decide +kernel

private theorem packet0610_pair (i : Fin 7) : checkEdgePair packet0610 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0610_ok : checkStripPacket packet0610 = true :=
  checkStripPacket_intro packet0610_shape packet0610_cache packet0610_pair

theorem packet0611_membership : packet0611 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0611_shape : checkStripShape packet0611.row = true := by
  decide +kernel

private theorem packet0611_cache : checkStripCache packet0611 = true := by
  decide +kernel

private theorem packet0611_pair (i : Fin 7) : checkEdgePair packet0611 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0611_ok : checkStripPacket packet0611 = true :=
  checkStripPacket_intro packet0611_shape packet0611_cache packet0611_pair

theorem packet0612_membership : packet0612 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0612_shape : checkStripShape packet0612.row = true := by
  decide +kernel

private theorem packet0612_cache : checkStripCache packet0612 = true := by
  decide +kernel

private theorem packet0612_pair (i : Fin 7) : checkEdgePair packet0612 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0612_ok : checkStripPacket packet0612 = true :=
  checkStripPacket_intro packet0612_shape packet0612_cache packet0612_pair

theorem packet0613_membership : packet0613 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0613_shape : checkStripShape packet0613.row = true := by
  decide +kernel

private theorem packet0613_cache : checkStripCache packet0613 = true := by
  decide +kernel

private theorem packet0613_pair (i : Fin 7) : checkEdgePair packet0613 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0613_ok : checkStripPacket packet0613 = true :=
  checkStripPacket_intro packet0613_shape packet0613_cache packet0613_pair

theorem packet0614_membership : packet0614 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0614_shape : checkStripShape packet0614.row = true := by
  decide +kernel

private theorem packet0614_cache : checkStripCache packet0614 = true := by
  decide +kernel

private theorem packet0614_pair (i : Fin 7) : checkEdgePair packet0614 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0614_ok : checkStripPacket packet0614 = true :=
  checkStripPacket_intro packet0614_shape packet0614_cache packet0614_pair

theorem packet0615_membership : packet0615 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0615_shape : checkStripShape packet0615.row = true := by
  decide +kernel

private theorem packet0615_cache : checkStripCache packet0615 = true := by
  decide +kernel

private theorem packet0615_pair (i : Fin 7) : checkEdgePair packet0615 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0615_ok : checkStripPacket packet0615 = true :=
  checkStripPacket_intro packet0615_shape packet0615_cache packet0615_pair

theorem packet0616_membership : packet0616 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0616_shape : checkStripShape packet0616.row = true := by
  decide +kernel

private theorem packet0616_cache : checkStripCache packet0616 = true := by
  decide +kernel

private theorem packet0616_pair (i : Fin 7) : checkEdgePair packet0616 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0616_ok : checkStripPacket packet0616 = true :=
  checkStripPacket_intro packet0616_shape packet0616_cache packet0616_pair

theorem packet0617_membership : packet0617 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0617_shape : checkStripShape packet0617.row = true := by
  decide +kernel

private theorem packet0617_cache : checkStripCache packet0617 = true := by
  decide +kernel

private theorem packet0617_pair (i : Fin 7) : checkEdgePair packet0617 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0617_ok : checkStripPacket packet0617 = true :=
  checkStripPacket_intro packet0617_shape packet0617_cache packet0617_pair

theorem packet0618_membership : packet0618 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0618_shape : checkStripShape packet0618.row = true := by
  decide +kernel

private theorem packet0618_cache : checkStripCache packet0618 = true := by
  decide +kernel

private theorem packet0618_pair (i : Fin 7) : checkEdgePair packet0618 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0618_ok : checkStripPacket packet0618 = true :=
  checkStripPacket_intro packet0618_shape packet0618_cache packet0618_pair

theorem packet0619_membership : packet0619 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0619_shape : checkStripShape packet0619.row = true := by
  decide +kernel

private theorem packet0619_cache : checkStripCache packet0619 = true := by
  decide +kernel

private theorem packet0619_pair (i : Fin 7) : checkEdgePair packet0619 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0619_ok : checkStripPacket packet0619 = true :=
  checkStripPacket_intro packet0619_shape packet0619_cache packet0619_pair

theorem packet0620_membership : packet0620 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0620_shape : checkStripShape packet0620.row = true := by
  decide +kernel

private theorem packet0620_cache : checkStripCache packet0620 = true := by
  decide +kernel

private theorem packet0620_pair (i : Fin 7) : checkEdgePair packet0620 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0620_ok : checkStripPacket packet0620 = true :=
  checkStripPacket_intro packet0620_shape packet0620_cache packet0620_pair

theorem packet0621_membership : packet0621 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0621_shape : checkStripShape packet0621.row = true := by
  decide +kernel

private theorem packet0621_cache : checkStripCache packet0621 = true := by
  decide +kernel

private theorem packet0621_pair (i : Fin 7) : checkEdgePair packet0621 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0621_ok : checkStripPacket packet0621 = true :=
  checkStripPacket_intro packet0621_shape packet0621_cache packet0621_pair

theorem packet0622_membership : packet0622 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0622_shape : checkStripShape packet0622.row = true := by
  decide +kernel

private theorem packet0622_cache : checkStripCache packet0622 = true := by
  decide +kernel

private theorem packet0622_pair (i : Fin 7) : checkEdgePair packet0622 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0622_ok : checkStripPacket packet0622 = true :=
  checkStripPacket_intro packet0622_shape packet0622_cache packet0622_pair

theorem packet0623_membership : packet0623 ∈ packets025 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0623_shape : checkStripShape packet0623.row = true := by
  decide +kernel

private theorem packet0623_cache : checkStripCache packet0623 = true := by
  decide +kernel

private theorem packet0623_pair (i : Fin 7) : checkEdgePair packet0623 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0623_ok : checkStripPacket packet0623 = true :=
  checkStripPacket_intro packet0623_shape packet0623_cache packet0623_pair

theorem packets025_checked : packets025.all checkStripPacket = true := by
  simp only [packets025, List.all_cons, List.all_nil, Bool.true_and, packet0600_ok,
    packet0601_ok, packet0602_ok, packet0603_ok, packet0604_ok, packet0605_ok,
    packet0606_ok, packet0607_ok, packet0608_ok, packet0609_ok, packet0610_ok,
    packet0611_ok, packet0612_ok, packet0613_ok, packet0614_ok, packet0615_ok,
    packet0616_ok, packet0617_ok, packet0618_ok, packet0619_ok, packet0620_ok,
    packet0621_ok, packet0622_ok, packet0623_ok]

theorem packets025_valid : packets025.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
