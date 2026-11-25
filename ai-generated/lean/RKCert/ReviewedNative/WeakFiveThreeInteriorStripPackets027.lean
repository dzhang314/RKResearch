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

def packet0648 : StripRowPacket :=
  ⟨⟨⟨6,11,4,13⟩,
    ![521,1605,3035,4588,6044,7205,7928],![537,1642,3093,4666,6138,7307,8013]⟩,
    ⟨49264155584832329402243,6752215440589849971220480⟩,
    ⟨42454664041232481433,4653996147298426373120⟩⟩

def packet0649 : StripRowPacket :=
  ⟨⟨⟨6,10,3,7⟩,
    ![532,1633,3078,4645,6112,7277,7984],![553,1682,3158,4756,6252,7440,8192]⟩,
    ⟨4583503089983523257609,534683009900566531164160⟩,
    ⟨162096927687131,13677976610721280⟩⟩

def packet0650 : StripRowPacket :=
  ⟨⟨⟨6,11,3,7⟩,
    ![527,1624,3070,4639,6109,7276,7984],![547,1672,3149,4749,6247,7437,8192]⟩,
    ⟨29758072449588973789097,3376107720294924985610240⟩,
    ⟨900563759,74057636224⟩⟩

def packet0651 : StripRowPacket :=
  ⟨⟨⟨6,12,4,8⟩,
    ![462,1445,2770,4253,5702,6936,7802],![487,1504,2858,4349,5785,6989,7823]⟩,
    ⟨-5962531682465328279,20852340343535237596928⟩,
    ⟨1996899419311906386231,1275160656494432130801664⟩⟩

def packet0652 : StripRowPacket :=
  ⟨⟨⟨6,12,4,9⟩,
    ![477,1486,2834,4324,5763,6974,7816],![500,1539,2915,4421,5854,7038,7842]⟩,
    ⟨2753831410726345349185,2168643395727664710080512⟩,
    ⟨97452466561092058643,31210225858255331872768⟩⟩

def packet0653 : StripRowPacket :=
  ⟨⟨⟨6,13,4,8⟩,
    ![459,1438,2763,4247,5698,6934,7802],![483,1497,2849,4343,5780,6987,7822]⟩,
    ⟨-318220581819871331203859,1147911967555808265669647360⟩,
    ⟨34231847634557500657087,21340605494001016492994560⟩⟩

def packet0654 : StripRowPacket :=
  ⟨⟨⟨6,13,4,9⟩,
    ![474,1479,2827,4319,5760,6973,7815],![495,1531,2907,4414,5850,7035,7841]⟩,
    ⟨12076795785636979724696117,9183295740446466125357178880⟩,
    ⟨88693385713244472802043,27742787142201321440892928⟩⟩

def packet0655 : StripRowPacket :=
  ⟨⟨⟨6,12,4,10⟩,
    ![490,1521,2891,4395,5830,7020,7833],![510,1568,2966,4489,5926,7094,7867]⟩,
    ⟨3063883058214542419693,1084321697863832355040256⟩,
    ⟨41764514937761312840179,8926124595461024915611648⟩⟩

def packet0656 : StripRowPacket :=
  ⟨⟨⟨6,12,4,11⟩,
    ![500,1550,2942,4462,5900,7074,7856],![518,1593,3011,4551,5999,7160,7901]⟩,
    ⟨9501700822131824329587,2168643395727664710080512⟩,
    ⟨13914406109762574227115,2231531148865256228902912⟩⟩

def packet0657 : StripRowPacket :=
  ⟨⟨⟨6,13,4,10⟩,
    ![486,1514,2884,4389,5827,7019,7833],![505,1560,2958,4482,5922,7092,7866]⟩,
    ⟨13349678112916465049511553,4591647870223233062678589440⟩,
    ⟨1328853695015641947498729,277427871422013214408929280⟩⟩

def packet0658 : StripRowPacket :=
  ⟨⟨⟨6,13,4,11⟩,
    ![496,1543,2935,4456,5897,7072,7856],![514,1585,3002,4544,5994,7157,7900]⟩,
    ⟨8264383333205776094670019,1836659148089293225071435776⟩,
    ⟨442693383224709791744257,69356967855503303602232320⟩⟩

def packet0659 : StripRowPacket :=
  ⟨⟨⟨6,14,4,8⟩,
    ![455,1432,2757,4242,5694,6932,7801],![479,1490,2842,4336,5776,6984,7822]⟩,
    ⟨-881991823931168861521,3275774760560921005544960⟩,
    ⟨19495703886214970518495871,11878586471125139346398371840⟩⟩

def packet0660 : StripRowPacket :=
  ⟨⟨⟨6,14,4,9⟩,
    ![470,1473,2820,4313,5756,6971,7815],![492,1524,2899,4408,5845,7033,7840]⟩,
    ⟨462889905010337355396723,340680575098335784576675840⟩,
    ⟨19420230854252053413988579,5939293235562569673199185920⟩⟩

def packet0661 : StripRowPacket :=
  ⟨⟨⟨6,15,4,8⟩,
    ![453,1427,2750,4236,5690,6930,7800],![476,1483,2834,4330,5772,6982,7821]⟩,
    ⟨-1810070498822286009,6911105005862140328960⟩,
    ⟨698420440075319721,416315055438384593920⟩⟩

def packet0662 : StripRowPacket :=
  ⟨⟨⟨6,15,4,9⟩,
    ![467,1467,2813,4308,5753,6969,7814],![488,1517,2892,4401,5841,7031,7840]⟩,
    ⟨77457437780449697407,55288840046897122631680⟩,
    ⟨10699381541126429,3202423503372189184⟩⟩

def packet0663 : StripRowPacket :=
  ⟨⟨⟨6,14,4,10⟩,
    ![483,1507,2877,4383,5823,7017,7832],![502,1553,2950,4475,5917,7090,7865]⟩,
    ⟨101750695970951627239163,34068057509833578457667584⟩,
    ⟨11637043906158648627491689,2375717294225027869279674368⟩⟩

def packet0664 : StripRowPacket :=
  ⟨⟨⟨6,14,4,11⟩,
    ![493,1537,2928,4451,5893,7071,7855],![510,1578,2994,4538,5990,7155,7899]⟩,
    ⟨1572124014408695189386537,340680575098335784576675840⟩,
    ⟨19382494338270594861734933,2969646617781284836599592960⟩⟩

def packet0665 : StripRowPacket :=
  ⟨⟨⟨6,15,4,10⟩,
    ![480,1501,2870,4378,5820,7015,7832],![498,1546,2942,4469,5913,7088,7865]⟩,
    ⟨84697719775738841443,27644420023448561315840⟩,
    ⟨189401705510686529,37846823221671326720⟩⟩

def packet0666 : StripRowPacket :=
  ⟨⟨⟨6,15,4,11⟩,
    ![490,1531,2921,4445,5890,7069,7855],![506,1571,2987,4532,5986,7153,7899]⟩,
    ⟨52266688264501133673,11057768009379424526336⟩,
    ⟨693979480222166967,104078763859596148480⟩⟩

def packet0667 : StripRowPacket :=
  ⟨⟨⟨6,12,4,12⟩,
    ![509,1576,2987,4525,5971,7135,7886],![526,1615,3050,4608,6068,7231,7947]⟩,
    ⟨3218908881958640954947,542160848931916177520128⟩,
    ⟨69550733940339280976741,8926124595461024915611648⟩⟩

def packet0668 : StripRowPacket :=
  ⟨⟨⟨6,12,4,13⟩,
    ![516,1598,3027,4582,6040,7204,7928],![532,1633,3084,4658,6133,7304,8012]⟩,
    ⟨16249570233537303309989,2168643395727664710080512⟩,
    ⟨41721921720814132522511,4463062297730512457805824⟩⟩

def packet0669 : StripRowPacket :=
  ⟨⟨⟨6,13,4,12⟩,
    ![505,1569,2980,4519,5968,7134,7886],![521,1607,3041,4601,6064,7229,7947]⟩,
    ⟨13986119276556207711919271,2295823935111616531339294720⟩,
    ⟨2212693370782036386455327,277427871422013214408929280⟩⟩

def packet0670 : StripRowPacket :=
  ⟨⟨⟨6,13,4,13⟩,
    ![512,1590,3019,4576,6037,7203,7928],![527,1625,3075,4652,6129,7302,8011]⟩,
    ⟨70567037546420781222004073,9183295740446466125357178880⟩,
    ⟨1327306604332616802966813,138713935711006607204464640⟩⟩

def packet0671 : StripRowPacket :=
  ⟨⟨⟨6,12,3,7⟩,
    ![522,1616,3062,4633,6105,7275,7985],![542,1663,3139,4741,6242,7435,8192]⟩,
    ⟨891977497238183763645,98574699805802941367296⟩,
    ⟨225318964702349,18081668826377728⟩⟩

def packets027 : List StripRowPacket :=
  [packet0648, packet0649, packet0650, packet0651, packet0652, packet0653,
   packet0654, packet0655, packet0656, packet0657, packet0658, packet0659,
   packet0660, packet0661, packet0662, packet0663, packet0664, packet0665,
   packet0666, packet0667, packet0668, packet0669, packet0670, packet0671]

theorem packet0648_membership : packet0648 ∈ packets027 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0648_shape : checkStripShape packet0648.row = true := by
  decide +kernel

private theorem packet0648_cache : checkStripCache packet0648 = true := by
  decide +kernel

private theorem packet0648_pair (i : Fin 7) : checkEdgePair packet0648 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0648_ok : checkStripPacket packet0648 = true :=
  checkStripPacket_intro packet0648_shape packet0648_cache packet0648_pair

theorem packet0649_membership : packet0649 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0649_shape : checkStripShape packet0649.row = true := by
  decide +kernel

private theorem packet0649_cache : checkStripCache packet0649 = true := by
  decide +kernel

private theorem packet0649_pair (i : Fin 7) : checkEdgePair packet0649 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0649_ok : checkStripPacket packet0649 = true :=
  checkStripPacket_intro packet0649_shape packet0649_cache packet0649_pair

theorem packet0650_membership : packet0650 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0650_shape : checkStripShape packet0650.row = true := by
  decide +kernel

private theorem packet0650_cache : checkStripCache packet0650 = true := by
  decide +kernel

private theorem packet0650_pair (i : Fin 7) : checkEdgePair packet0650 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0650_ok : checkStripPacket packet0650 = true :=
  checkStripPacket_intro packet0650_shape packet0650_cache packet0650_pair

theorem packet0651_membership : packet0651 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0651_shape : checkStripShape packet0651.row = true := by
  decide +kernel

private theorem packet0651_cache : checkStripCache packet0651 = true := by
  decide +kernel

private theorem packet0651_pair (i : Fin 7) : checkEdgePair packet0651 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0651_ok : checkStripPacket packet0651 = true :=
  checkStripPacket_intro packet0651_shape packet0651_cache packet0651_pair

theorem packet0652_membership : packet0652 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0652_shape : checkStripShape packet0652.row = true := by
  decide +kernel

private theorem packet0652_cache : checkStripCache packet0652 = true := by
  decide +kernel

private theorem packet0652_pair (i : Fin 7) : checkEdgePair packet0652 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0652_ok : checkStripPacket packet0652 = true :=
  checkStripPacket_intro packet0652_shape packet0652_cache packet0652_pair

theorem packet0653_membership : packet0653 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0653_shape : checkStripShape packet0653.row = true := by
  decide +kernel

private theorem packet0653_cache : checkStripCache packet0653 = true := by
  decide +kernel

private theorem packet0653_pair (i : Fin 7) : checkEdgePair packet0653 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0653_ok : checkStripPacket packet0653 = true :=
  checkStripPacket_intro packet0653_shape packet0653_cache packet0653_pair

theorem packet0654_membership : packet0654 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0654_shape : checkStripShape packet0654.row = true := by
  decide +kernel

private theorem packet0654_cache : checkStripCache packet0654 = true := by
  decide +kernel

private theorem packet0654_pair (i : Fin 7) : checkEdgePair packet0654 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0654_ok : checkStripPacket packet0654 = true :=
  checkStripPacket_intro packet0654_shape packet0654_cache packet0654_pair

theorem packet0655_membership : packet0655 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0655_shape : checkStripShape packet0655.row = true := by
  decide +kernel

private theorem packet0655_cache : checkStripCache packet0655 = true := by
  decide +kernel

private theorem packet0655_pair (i : Fin 7) : checkEdgePair packet0655 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0655_ok : checkStripPacket packet0655 = true :=
  checkStripPacket_intro packet0655_shape packet0655_cache packet0655_pair

theorem packet0656_membership : packet0656 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0656_shape : checkStripShape packet0656.row = true := by
  decide +kernel

private theorem packet0656_cache : checkStripCache packet0656 = true := by
  decide +kernel

private theorem packet0656_pair (i : Fin 7) : checkEdgePair packet0656 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0656_ok : checkStripPacket packet0656 = true :=
  checkStripPacket_intro packet0656_shape packet0656_cache packet0656_pair

theorem packet0657_membership : packet0657 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0657_shape : checkStripShape packet0657.row = true := by
  decide +kernel

private theorem packet0657_cache : checkStripCache packet0657 = true := by
  decide +kernel

private theorem packet0657_pair (i : Fin 7) : checkEdgePair packet0657 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0657_ok : checkStripPacket packet0657 = true :=
  checkStripPacket_intro packet0657_shape packet0657_cache packet0657_pair

theorem packet0658_membership : packet0658 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0658_shape : checkStripShape packet0658.row = true := by
  decide +kernel

private theorem packet0658_cache : checkStripCache packet0658 = true := by
  decide +kernel

private theorem packet0658_pair (i : Fin 7) : checkEdgePair packet0658 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0658_ok : checkStripPacket packet0658 = true :=
  checkStripPacket_intro packet0658_shape packet0658_cache packet0658_pair

theorem packet0659_membership : packet0659 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0659_shape : checkStripShape packet0659.row = true := by
  decide +kernel

private theorem packet0659_cache : checkStripCache packet0659 = true := by
  decide +kernel

private theorem packet0659_pair (i : Fin 7) : checkEdgePair packet0659 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0659_ok : checkStripPacket packet0659 = true :=
  checkStripPacket_intro packet0659_shape packet0659_cache packet0659_pair

theorem packet0660_membership : packet0660 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0660_shape : checkStripShape packet0660.row = true := by
  decide +kernel

private theorem packet0660_cache : checkStripCache packet0660 = true := by
  decide +kernel

private theorem packet0660_pair (i : Fin 7) : checkEdgePair packet0660 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0660_ok : checkStripPacket packet0660 = true :=
  checkStripPacket_intro packet0660_shape packet0660_cache packet0660_pair

theorem packet0661_membership : packet0661 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0661_shape : checkStripShape packet0661.row = true := by
  decide +kernel

private theorem packet0661_cache : checkStripCache packet0661 = true := by
  decide +kernel

private theorem packet0661_pair (i : Fin 7) : checkEdgePair packet0661 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0661_ok : checkStripPacket packet0661 = true :=
  checkStripPacket_intro packet0661_shape packet0661_cache packet0661_pair

theorem packet0662_membership : packet0662 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0662_shape : checkStripShape packet0662.row = true := by
  decide +kernel

private theorem packet0662_cache : checkStripCache packet0662 = true := by
  decide +kernel

private theorem packet0662_pair (i : Fin 7) : checkEdgePair packet0662 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0662_ok : checkStripPacket packet0662 = true :=
  checkStripPacket_intro packet0662_shape packet0662_cache packet0662_pair

theorem packet0663_membership : packet0663 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0663_shape : checkStripShape packet0663.row = true := by
  decide +kernel

private theorem packet0663_cache : checkStripCache packet0663 = true := by
  decide +kernel

private theorem packet0663_pair (i : Fin 7) : checkEdgePair packet0663 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0663_ok : checkStripPacket packet0663 = true :=
  checkStripPacket_intro packet0663_shape packet0663_cache packet0663_pair

theorem packet0664_membership : packet0664 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0664_shape : checkStripShape packet0664.row = true := by
  decide +kernel

private theorem packet0664_cache : checkStripCache packet0664 = true := by
  decide +kernel

private theorem packet0664_pair (i : Fin 7) : checkEdgePair packet0664 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0664_ok : checkStripPacket packet0664 = true :=
  checkStripPacket_intro packet0664_shape packet0664_cache packet0664_pair

theorem packet0665_membership : packet0665 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0665_shape : checkStripShape packet0665.row = true := by
  decide +kernel

private theorem packet0665_cache : checkStripCache packet0665 = true := by
  decide +kernel

private theorem packet0665_pair (i : Fin 7) : checkEdgePair packet0665 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0665_ok : checkStripPacket packet0665 = true :=
  checkStripPacket_intro packet0665_shape packet0665_cache packet0665_pair

theorem packet0666_membership : packet0666 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0666_shape : checkStripShape packet0666.row = true := by
  decide +kernel

private theorem packet0666_cache : checkStripCache packet0666 = true := by
  decide +kernel

private theorem packet0666_pair (i : Fin 7) : checkEdgePair packet0666 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0666_ok : checkStripPacket packet0666 = true :=
  checkStripPacket_intro packet0666_shape packet0666_cache packet0666_pair

theorem packet0667_membership : packet0667 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0667_shape : checkStripShape packet0667.row = true := by
  decide +kernel

private theorem packet0667_cache : checkStripCache packet0667 = true := by
  decide +kernel

private theorem packet0667_pair (i : Fin 7) : checkEdgePair packet0667 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0667_ok : checkStripPacket packet0667 = true :=
  checkStripPacket_intro packet0667_shape packet0667_cache packet0667_pair

theorem packet0668_membership : packet0668 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0668_shape : checkStripShape packet0668.row = true := by
  decide +kernel

private theorem packet0668_cache : checkStripCache packet0668 = true := by
  decide +kernel

private theorem packet0668_pair (i : Fin 7) : checkEdgePair packet0668 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0668_ok : checkStripPacket packet0668 = true :=
  checkStripPacket_intro packet0668_shape packet0668_cache packet0668_pair

theorem packet0669_membership : packet0669 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0669_shape : checkStripShape packet0669.row = true := by
  decide +kernel

private theorem packet0669_cache : checkStripCache packet0669 = true := by
  decide +kernel

private theorem packet0669_pair (i : Fin 7) : checkEdgePair packet0669 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0669_ok : checkStripPacket packet0669 = true :=
  checkStripPacket_intro packet0669_shape packet0669_cache packet0669_pair

theorem packet0670_membership : packet0670 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0670_shape : checkStripShape packet0670.row = true := by
  decide +kernel

private theorem packet0670_cache : checkStripCache packet0670 = true := by
  decide +kernel

private theorem packet0670_pair (i : Fin 7) : checkEdgePair packet0670 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0670_ok : checkStripPacket packet0670 = true :=
  checkStripPacket_intro packet0670_shape packet0670_cache packet0670_pair

theorem packet0671_membership : packet0671 ∈ packets027 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0671_shape : checkStripShape packet0671.row = true := by
  decide +kernel

private theorem packet0671_cache : checkStripCache packet0671 = true := by
  decide +kernel

private theorem packet0671_pair (i : Fin 7) : checkEdgePair packet0671 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0671_ok : checkStripPacket packet0671 = true :=
  checkStripPacket_intro packet0671_shape packet0671_cache packet0671_pair

theorem packets027_checked : packets027.all checkStripPacket = true := by
  simp only [packets027, List.all_cons, List.all_nil, Bool.true_and, packet0648_ok,
    packet0649_ok, packet0650_ok, packet0651_ok, packet0652_ok, packet0653_ok,
    packet0654_ok, packet0655_ok, packet0656_ok, packet0657_ok, packet0658_ok,
    packet0659_ok, packet0660_ok, packet0661_ok, packet0662_ok, packet0663_ok,
    packet0664_ok, packet0665_ok, packet0666_ok, packet0667_ok, packet0668_ok,
    packet0669_ok, packet0670_ok, packet0671_ok]

theorem packets027_valid : packets027.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
