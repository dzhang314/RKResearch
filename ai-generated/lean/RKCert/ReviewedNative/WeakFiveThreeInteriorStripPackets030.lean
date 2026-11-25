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

def packet0720 : StripRowPacket :=
  ⟨⟨⟨6,16,4,9⟩,
    ![465,1462,2807,4303,5749,6967,7814],![485,1511,2885,4396,5837,7029,7839]⟩,
    ⟨728128270023258107,504955469662764989440⟩,
    ⟨119783864422150484221,35118461836964766740480⟩⟩

def packet0721 : StripRowPacket :=
  ⟨⟨⟨6,17,4,8⟩,
    ![448,1416,2739,4226,5683,6926,7799],![470,1471,2821,4319,5764,6978,7820]⟩,
    ⟨-40622131952512625876663,163303573979578712942918656⟩,
    ⟨19833340334266526139414157,11344443006018218755009015808⟩⟩

def packet0722 : StripRowPacket :=
  ⟨⟨⟨6,17,4,9⟩,
    ![462,1456,2801,4298,5746,6966,7813],![482,1505,2878,4390,5833,7027,7839]⟩,
    ⟨1935964566117772519162545,1306428591836629703543349248⟩,
    ⟨19735870016622144594448409,5672221503009109377504507904⟩⟩

def packet0723 : StripRowPacket :=
  ⟨⟨⟨6,16,4,10⟩,
    ![477,1496,2864,4373,5816,7014,7831],![495,1540,2935,4463,5909,7086,7864]⟩,
    ⟨158507168982276107,50495546966276498944⟩,
    ⟨71759960834655964599,14047384734785906696192⟩⟩

def packet0724 : StripRowPacket :=
  ⟨⟨⟨6,16,4,11⟩,
    ![487,1525,2915,4440,5887,7068,7855],![503,1564,2980,4526,5982,7151,7898]⟩,
    ⟨17077028738617231,3531157130508846080⟩,
    ⟨119507969875564669387,17559230918482383370240⟩⟩

def packet0725 : StripRowPacket :=
  ⟨⟨⟨6,17,4,10⟩,
    ![474,1491,2858,4368,5813,7012,7831],![492,1534,2928,4458,5906,7084,7864]⟩,
    ⟨2098453093927823022669197,653214295918314851771674624⟩,
    ⟨59110139732222052238379479,11344443006018218755009015808⟩⟩

def packet0726 : StripRowPacket :=
  ⟨⟨⟨6,17,4,11⟩,
    ![484,1520,2909,4435,5884,7067,7854],![500,1558,2973,4520,5978,7149,7898]⟩,
    ⟨496757523814886120885711,100494507064356131041796096⟩,
    ⟨19687134857799953821965535,2836110751504554688752253952⟩⟩

def packet0727 : StripRowPacket :=
  ⟨⟨⟨6,18,4,8⟩,
    ![446,1412,2733,4221,5680,6925,7799],![468,1466,2815,4313,5760,6976,7819]⟩,
    ⟨-429929609206768263987,1770751244211416016309760⟩,
    ⟨2913804506861339918572827,1634492429903107973830860800⟩⟩

def packet0728 : StripRowPacket :=
  ⟨⟨⟨6,19,4,8⟩,
    ![443,1407,2728,4217,5677,6923,7798],![465,1461,2809,4308,5757,6974,7818]⟩,
    ⟨-1397443412502894233023,5891950572568478330598400⟩,
    ⟨5916359633725724569,3256900375723973355520⟩⟩

def packet0729 : StripRowPacket :=
  ⟨⟨⟨6,18,4,9⟩,
    ![460,1452,2796,4293,5743,6964,7813],![479,1500,2872,4385,5830,7025,7838]⟩,
    ⟨95408008128199820569493,62735186937775881720688640⟩,
    ⟨579713476305205193453443,163449242990310797383086080⟩⟩

def packet0730 : StripRowPacket :=
  ⟨⟨⟨6,19,4,9⟩,
    ![458,1447,2791,4288,5740,6962,7812],![477,1494,2866,4379,5826,7023,7837]⟩,
    ⟨73477423730903552541193,47135604580547826644787200⟩,
    ⟨3168107913951720079,876857793464146672640⟩⟩

def packet0731 : StripRowPacket :=
  ⟨⟨⟨6,18,4,10⟩,
    ![472,1486,2853,4364,5810,7011,7831],![489,1528,2922,4452,5902,7082,7863]⟩,
    ⟨721167328439038008720839,219573154282215586022410240⟩,
    ⟨667728078403289534653541,125730186915623690294681600⟩⟩

def packet0732 : StripRowPacket :=
  ⟨⟨⟨6,19,4,10⟩,
    ![470,1481,2847,4359,5807,7009,7830],![486,1523,2916,4447,5898,7081,7863]⟩,
    ⟨1437585406925729626787,428505496186798424043520⟩,
    ⟨24665418817881874425,4559660526013562697728⟩⟩

def packet0733 : StripRowPacket :=
  ⟨⟨⟨6,18,4,11⟩,
    ![482,1514,2903,4431,5881,7065,7854],![497,1552,2966,4515,5974,7148,7897]⟩,
    ⟨443362651371750658179381,87829261712886234408964096⟩,
    ⟨2890948818858368991614409,408623107475776993457715200⟩⟩

def packet0734 : StripRowPacket :=
  ⟨⟨⟨6,19,4,11⟩,
    ![479,1510,2898,4426,5878,7064,7854],![494,1547,2960,4509,5971,7146,7896]⟩,
    ⟨18676258907135151180919,3625815736965217434214400⟩,
    ⟨41070845604018505549,5699575657516953372160⟩⟩

def packet0735 : StripRowPacket :=
  ⟨⟨⟨6,16,4,12⟩,
    ![495,1550,2960,4503,5958,7130,7886],![510,1585,3018,4582,6052,7223,7945]⟩,
    ⟨824739632355441749,126238867415691247360⟩,
    ⟨597263954831237532101,70236923673929533480960⟩⟩

def packet0736 : StripRowPacket :=
  ⟨⟨⟨6,16,4,13⟩,
    ![502,1571,2999,4560,6028,7199,7928],![516,1604,3052,4633,6117,7296,8009]⟩,
    ⟨4155901949221269959,504955469662764989440⟩,
    ⟨51178287868586884761,5016923119566395248640⟩⟩

def packet0737 : StripRowPacket :=
  ⟨⟨⟨6,17,4,12⟩,
    ![492,1544,2954,4498,5955,7129,7885],![507,1579,3011,4577,6048,7221,7944]⟩,
    ⟨2179697357832848274422523,326607147959157425885837312⟩,
    ⟨98386939130177578337344801,11344443006018218755009015808⟩⟩

def packet0738 : StripRowPacket :=
  ⟨⟨⟨6,17,4,13⟩,
    ![499,1566,2993,4555,6025,7198,7928],![513,1597,3045,4627,6113,7294,8009]⟩,
    ⟨10979731053069266623865941,1306428591836629703543349248⟩,
    ⟨59012669414577670693413731,5672221503009109377504507904⟩⟩

def packet0739 : StripRowPacket :=
  ⟨⟨⟨6,16,3,7⟩,
    ![508,1590,3033,4611,6093,7271,7986],![526,1633,3107,4716,6226,7427,8192]⟩,
    ⟨2506422684510386461,252477734831382494720⟩,
    ⟨403973138184953,29712056107621888⟩⟩

def packet0740 : StripRowPacket :=
  ⟨⟨⟨6,17,3,7⟩,
    ![505,1584,3027,4606,6090,7270,7986],![522,1627,3100,4710,6222,7426,8192]⟩,
    ⟨945762333914795725002985,93316327988330693110239232⟩,
    ⟨3606517818433,260097773002496⟩⟩

def packet0741 : StripRowPacket :=
  ⟨⟨⟨5,9,4,12⟩,
    ![487,1532,2938,4482,5941,7119,7881],![505,1576,3009,4578,6052,7228,7950]⟩,
    ⟨556391608559186580737,82450972193578299790336⟩,
    ⟨5373627397480377055,593721644402366425088⟩⟩

def packet0742 : StripRowPacket :=
  ⟨⟨⟨5,9,4,13⟩,
    ![494,1553,2977,4539,6011,7187,7922],![511,1594,3043,4628,6117,7302,8018]⟩,
    ⟨2812440671173323993839,329803888774313199161344⟩,
    ⟨3215329329310453021,296860822201183212544⟩⟩

def packet0743 : StripRowPacket :=
  ⟨⟨⟨5,9,4,14⟩,
    ![500,1571,3011,4590,6076,7259,7978],![516,1609,3072,4671,6175,7372,8111]⟩,
    ⟨154514314004995530215,14991085853377872689152⟩,
    ⟨7487689919761435029,593721644402366425088⟩⟩

def packets030 : List StripRowPacket :=
  [packet0720, packet0721, packet0722, packet0723, packet0724, packet0725,
   packet0726, packet0727, packet0728, packet0729, packet0730, packet0731,
   packet0732, packet0733, packet0734, packet0735, packet0736, packet0737,
   packet0738, packet0739, packet0740, packet0741, packet0742, packet0743]

theorem packet0720_membership : packet0720 ∈ packets030 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0720_shape : checkStripShape packet0720.row = true := by
  decide +kernel

private theorem packet0720_cache : checkStripCache packet0720 = true := by
  decide +kernel

private theorem packet0720_pair (i : Fin 7) : checkEdgePair packet0720 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0720_ok : checkStripPacket packet0720 = true :=
  checkStripPacket_intro packet0720_shape packet0720_cache packet0720_pair

theorem packet0721_membership : packet0721 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0721_shape : checkStripShape packet0721.row = true := by
  decide +kernel

private theorem packet0721_cache : checkStripCache packet0721 = true := by
  decide +kernel

private theorem packet0721_pair (i : Fin 7) : checkEdgePair packet0721 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0721_ok : checkStripPacket packet0721 = true :=
  checkStripPacket_intro packet0721_shape packet0721_cache packet0721_pair

theorem packet0722_membership : packet0722 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0722_shape : checkStripShape packet0722.row = true := by
  decide +kernel

private theorem packet0722_cache : checkStripCache packet0722 = true := by
  decide +kernel

private theorem packet0722_pair (i : Fin 7) : checkEdgePair packet0722 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0722_ok : checkStripPacket packet0722 = true :=
  checkStripPacket_intro packet0722_shape packet0722_cache packet0722_pair

theorem packet0723_membership : packet0723 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0723_shape : checkStripShape packet0723.row = true := by
  decide +kernel

private theorem packet0723_cache : checkStripCache packet0723 = true := by
  decide +kernel

private theorem packet0723_pair (i : Fin 7) : checkEdgePair packet0723 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0723_ok : checkStripPacket packet0723 = true :=
  checkStripPacket_intro packet0723_shape packet0723_cache packet0723_pair

theorem packet0724_membership : packet0724 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0724_shape : checkStripShape packet0724.row = true := by
  decide +kernel

private theorem packet0724_cache : checkStripCache packet0724 = true := by
  decide +kernel

private theorem packet0724_pair (i : Fin 7) : checkEdgePair packet0724 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0724_ok : checkStripPacket packet0724 = true :=
  checkStripPacket_intro packet0724_shape packet0724_cache packet0724_pair

theorem packet0725_membership : packet0725 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0725_shape : checkStripShape packet0725.row = true := by
  decide +kernel

private theorem packet0725_cache : checkStripCache packet0725 = true := by
  decide +kernel

private theorem packet0725_pair (i : Fin 7) : checkEdgePair packet0725 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0725_ok : checkStripPacket packet0725 = true :=
  checkStripPacket_intro packet0725_shape packet0725_cache packet0725_pair

theorem packet0726_membership : packet0726 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0726_shape : checkStripShape packet0726.row = true := by
  decide +kernel

private theorem packet0726_cache : checkStripCache packet0726 = true := by
  decide +kernel

private theorem packet0726_pair (i : Fin 7) : checkEdgePair packet0726 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0726_ok : checkStripPacket packet0726 = true :=
  checkStripPacket_intro packet0726_shape packet0726_cache packet0726_pair

theorem packet0727_membership : packet0727 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0727_shape : checkStripShape packet0727.row = true := by
  decide +kernel

private theorem packet0727_cache : checkStripCache packet0727 = true := by
  decide +kernel

private theorem packet0727_pair (i : Fin 7) : checkEdgePair packet0727 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0727_ok : checkStripPacket packet0727 = true :=
  checkStripPacket_intro packet0727_shape packet0727_cache packet0727_pair

theorem packet0728_membership : packet0728 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0728_shape : checkStripShape packet0728.row = true := by
  decide +kernel

private theorem packet0728_cache : checkStripCache packet0728 = true := by
  decide +kernel

private theorem packet0728_pair (i : Fin 7) : checkEdgePair packet0728 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0728_ok : checkStripPacket packet0728 = true :=
  checkStripPacket_intro packet0728_shape packet0728_cache packet0728_pair

theorem packet0729_membership : packet0729 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0729_shape : checkStripShape packet0729.row = true := by
  decide +kernel

private theorem packet0729_cache : checkStripCache packet0729 = true := by
  decide +kernel

private theorem packet0729_pair (i : Fin 7) : checkEdgePair packet0729 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0729_ok : checkStripPacket packet0729 = true :=
  checkStripPacket_intro packet0729_shape packet0729_cache packet0729_pair

theorem packet0730_membership : packet0730 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0730_shape : checkStripShape packet0730.row = true := by
  decide +kernel

private theorem packet0730_cache : checkStripCache packet0730 = true := by
  decide +kernel

private theorem packet0730_pair (i : Fin 7) : checkEdgePair packet0730 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0730_ok : checkStripPacket packet0730 = true :=
  checkStripPacket_intro packet0730_shape packet0730_cache packet0730_pair

theorem packet0731_membership : packet0731 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0731_shape : checkStripShape packet0731.row = true := by
  decide +kernel

private theorem packet0731_cache : checkStripCache packet0731 = true := by
  decide +kernel

private theorem packet0731_pair (i : Fin 7) : checkEdgePair packet0731 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0731_ok : checkStripPacket packet0731 = true :=
  checkStripPacket_intro packet0731_shape packet0731_cache packet0731_pair

theorem packet0732_membership : packet0732 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0732_shape : checkStripShape packet0732.row = true := by
  decide +kernel

private theorem packet0732_cache : checkStripCache packet0732 = true := by
  decide +kernel

private theorem packet0732_pair (i : Fin 7) : checkEdgePair packet0732 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0732_ok : checkStripPacket packet0732 = true :=
  checkStripPacket_intro packet0732_shape packet0732_cache packet0732_pair

theorem packet0733_membership : packet0733 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0733_shape : checkStripShape packet0733.row = true := by
  decide +kernel

private theorem packet0733_cache : checkStripCache packet0733 = true := by
  decide +kernel

private theorem packet0733_pair (i : Fin 7) : checkEdgePair packet0733 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0733_ok : checkStripPacket packet0733 = true :=
  checkStripPacket_intro packet0733_shape packet0733_cache packet0733_pair

theorem packet0734_membership : packet0734 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0734_shape : checkStripShape packet0734.row = true := by
  decide +kernel

private theorem packet0734_cache : checkStripCache packet0734 = true := by
  decide +kernel

private theorem packet0734_pair (i : Fin 7) : checkEdgePair packet0734 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0734_ok : checkStripPacket packet0734 = true :=
  checkStripPacket_intro packet0734_shape packet0734_cache packet0734_pair

theorem packet0735_membership : packet0735 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0735_shape : checkStripShape packet0735.row = true := by
  decide +kernel

private theorem packet0735_cache : checkStripCache packet0735 = true := by
  decide +kernel

private theorem packet0735_pair (i : Fin 7) : checkEdgePair packet0735 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0735_ok : checkStripPacket packet0735 = true :=
  checkStripPacket_intro packet0735_shape packet0735_cache packet0735_pair

theorem packet0736_membership : packet0736 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0736_shape : checkStripShape packet0736.row = true := by
  decide +kernel

private theorem packet0736_cache : checkStripCache packet0736 = true := by
  decide +kernel

private theorem packet0736_pair (i : Fin 7) : checkEdgePair packet0736 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0736_ok : checkStripPacket packet0736 = true :=
  checkStripPacket_intro packet0736_shape packet0736_cache packet0736_pair

theorem packet0737_membership : packet0737 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0737_shape : checkStripShape packet0737.row = true := by
  decide +kernel

private theorem packet0737_cache : checkStripCache packet0737 = true := by
  decide +kernel

private theorem packet0737_pair (i : Fin 7) : checkEdgePair packet0737 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0737_ok : checkStripPacket packet0737 = true :=
  checkStripPacket_intro packet0737_shape packet0737_cache packet0737_pair

theorem packet0738_membership : packet0738 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0738_shape : checkStripShape packet0738.row = true := by
  decide +kernel

private theorem packet0738_cache : checkStripCache packet0738 = true := by
  decide +kernel

private theorem packet0738_pair (i : Fin 7) : checkEdgePair packet0738 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0738_ok : checkStripPacket packet0738 = true :=
  checkStripPacket_intro packet0738_shape packet0738_cache packet0738_pair

theorem packet0739_membership : packet0739 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0739_shape : checkStripShape packet0739.row = true := by
  decide +kernel

private theorem packet0739_cache : checkStripCache packet0739 = true := by
  decide +kernel

private theorem packet0739_pair (i : Fin 7) : checkEdgePair packet0739 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0739_ok : checkStripPacket packet0739 = true :=
  checkStripPacket_intro packet0739_shape packet0739_cache packet0739_pair

theorem packet0740_membership : packet0740 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0740_shape : checkStripShape packet0740.row = true := by
  decide +kernel

private theorem packet0740_cache : checkStripCache packet0740 = true := by
  decide +kernel

private theorem packet0740_pair (i : Fin 7) : checkEdgePair packet0740 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0740_ok : checkStripPacket packet0740 = true :=
  checkStripPacket_intro packet0740_shape packet0740_cache packet0740_pair

theorem packet0741_membership : packet0741 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0741_shape : checkStripShape packet0741.row = true := by
  decide +kernel

private theorem packet0741_cache : checkStripCache packet0741 = true := by
  decide +kernel

private theorem packet0741_pair (i : Fin 7) : checkEdgePair packet0741 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0741_ok : checkStripPacket packet0741 = true :=
  checkStripPacket_intro packet0741_shape packet0741_cache packet0741_pair

theorem packet0742_membership : packet0742 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0742_shape : checkStripShape packet0742.row = true := by
  decide +kernel

private theorem packet0742_cache : checkStripCache packet0742 = true := by
  decide +kernel

private theorem packet0742_pair (i : Fin 7) : checkEdgePair packet0742 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0742_ok : checkStripPacket packet0742 = true :=
  checkStripPacket_intro packet0742_shape packet0742_cache packet0742_pair

theorem packet0743_membership : packet0743 ∈ packets030 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0743_shape : checkStripShape packet0743.row = true := by
  decide +kernel

private theorem packet0743_cache : checkStripCache packet0743 = true := by
  decide +kernel

private theorem packet0743_pair (i : Fin 7) : checkEdgePair packet0743 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0743_ok : checkStripPacket packet0743 = true :=
  checkStripPacket_intro packet0743_shape packet0743_cache packet0743_pair

theorem packets030_checked : packets030.all checkStripPacket = true := by
  simp only [packets030, List.all_cons, List.all_nil, Bool.true_and, packet0720_ok,
    packet0721_ok, packet0722_ok, packet0723_ok, packet0724_ok, packet0725_ok,
    packet0726_ok, packet0727_ok, packet0728_ok, packet0729_ok, packet0730_ok,
    packet0731_ok, packet0732_ok, packet0733_ok, packet0734_ok, packet0735_ok,
    packet0736_ok, packet0737_ok, packet0738_ok, packet0739_ok, packet0740_ok,
    packet0741_ok, packet0742_ok, packet0743_ok]

theorem packets030_valid : packets030.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
