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

def packet0216 : StripRowPacket :=
  ⟨⟨⟨8,4,6,18⟩,
    ![460,1383,2663,4137,5609,6882,7784],![488,1417,2695,4163,5627,6893,7790]⟩,
    ⟨-29787058294043366631972879319,7518195074150581579519742525440⟩,
    ⟨-1683045868597400711177661053,471100404390448278992892329984⟩⟩

def packet0217 : StripRowPacket :=
  ⟨⟨⟨8,4,6,19⟩,
    ![474,1401,2680,4151,5618,6887,7786],![501,1436,2713,4177,5637,6898,7791]⟩,
    ⟨-613316222380306362366321559759,165400291631312794749434335559680⟩,
    ⟨-1953975892019132086105027479,588875505488060348741115412480⟩⟩

def packet0218 : StripRowPacket :=
  ⟨⟨⟨8,5,6,18⟩,
    ![454,1377,2658,4133,5607,6881,7784],![481,1411,2690,4159,5625,6892,7789]⟩,
    ⟨-115466044221937349030283604443,28826593493738487724247352279040⟩,
    ⟨-5246595011617746928050793480243,1450958070828439567023527350435840⟩⟩

def packet0219 : StripRowPacket :=
  ⟨⟨⟨8,5,6,19⟩,
    ![468,1396,2676,4147,5616,6886,7785],![494,1429,2708,4173,5635,6897,7791]⟩,
    ⟨-23265767427232058326830794383,6208804752497520432914814337024⟩,
    ⟨-243556373023613834510882132129,72547903541421978351176367521792⟩⟩

def packet0220 : StripRowPacket :=
  ⟨⟨⟨8,6,6,16⟩,
    ![420,1334,2619,4104,5588,6871,7781],![448,1367,2649,4127,5604,6881,7786]⟩,
    ⟨-117214676798501167702959533,25626047178883372136932290560⟩,
    ⟨-21177379471780618735108667779387,5060489166599135951878995124551680⟩⟩

def packet0221 : StripRowPacket :=
  ⟨⟨⟨8,6,6,17⟩,
    ![435,1353,2636,4117,5596,6876,7782],![462,1386,2667,4141,5613,6886,7787]⟩,
    ⟨-1767781177363178682582916941,410016754862133954190916648960⟩,
    ⟨-109156566435116729310697850044353,27832690416295247735334473185034240⟩⟩

def packet0222 : StripRowPacket :=
  ⟨⟨⟨8,7,6,16⟩,
    ![416,1329,2615,4100,5585,6870,7780],![442,1361,2644,4123,5602,6880,7786]⟩,
    ⟨-4313751715111103560125465361,932620870253380628841662242816⟩,
    ⟨-29751577455915884284993503,7024333952012097732992121856⟩⟩

def packet0223 : StripRowPacket :=
  ⟨⟨⟨8,7,6,17⟩,
    ![431,1348,2632,4113,5594,6874,7782],![456,1380,2662,4137,5611,6885,7787]⟩,
    ⟨-65040873142154474667624559393,14921933924054090061466595885056⟩,
    ⟨-13937939070822227495587513,3512166976006048866496060928⟩⟩

def packet0224 : StripRowPacket :=
  ⟨⟨⟨8,6,6,18⟩,
    ![449,1372,2653,4130,5605,6880,7784],![475,1405,2685,4155,5622,6891,7789]⟩,
    ⟨-830063762975169340959240677,205008377431066977095458324480⟩,
    ⟨-40735018310176022231319210920831,11133076166518099094133789274013696⟩⟩

def packet0225 : StripRowPacket :=
  ⟨⟨⟨8,6,6,19⟩,
    ![462,1390,2671,4144,5614,6885,7785],![487,1423,2703,4170,5632,6896,7791]⟩,
    ⟨-1552473874537498681254045767,410016754862133954190916648960⟩,
    ⟨-47259262557881690922949102279901,13916345208147623867667236592517120⟩⟩

def packet0226 : StripRowPacket :=
  ⟨⟨⟨8,7,5,9⟩,
    ![444,1366,2649,4127,5603,6879,7783],![481,1417,2698,4166,5630,6894,7790]⟩,
    ⟨-2348527647789665091278525885,573920535540541925441022918656⟩,
    ⟨-3015559939137699550442259,878041744001512216624015232⟩⟩

def packet0227 : StripRowPacket :=
  ⟨⟨⟨8,4,6,20⟩,
    ![486,1419,2698,4165,5628,6892,7787],![513,1454,2731,4192,5647,6903,7793]⟩,
    ⟨-28565858114582932941461988725,8270014581565639737471716777984⟩,
    ⟨-1030939684738007590421702081,336500288850320199280637378560⟩⟩

def packet0228 : StripRowPacket :=
  ⟨⟨⟨8,4,6,21⟩,
    ![498,1437,2716,4179,5638,6897,7789],![524,1472,2750,4207,5657,6909,7795]⟩,
    ⟨-529318102203010955292157989241,165400291631312794749434335559680⟩,
    ⟨-3308626009127788960741859609,1177751010976120697482230824960⟩⟩

def packet0229 : StripRowPacket :=
  ⟨⟨⟨8,5,5,10⟩,
    ![480,1414,2693,4161,5626,6891,7787],![516,1465,2744,4203,5655,6908,7794]⟩,
    ⟨-352006286608261174016008201897,100893077228084707034865732976640⟩,
    ⟨-2060096179090668107275670483627,725479035414219783511763675217920⟩⟩

def packet0230 : StripRowPacket :=
  ⟨⟨⟨8,4,5,11⟩,
    ![509,1455,2734,4194,5648,6902,7791],![543,1506,2787,4239,5679,6920,7798]⟩,
    ⟨-243659521057181625877538101991,82700145815656397374717167779840⟩,
    ⟨-947307774201857954291491,411801052788853390728052736⟩⟩

def packet0231 : StripRowPacket :=
  ⟨⟨⟨8,5,5,11⟩,
    ![502,1449,2729,4191,5646,6901,7790],![536,1499,2781,4235,5677,6919,7798]⟩,
    ⟨-599762836879483252852047576487,201786154456169414069731465953280⟩,
    ⟨-38287014271481769760057264681,16488159895777722352540083527680⟩⟩

def packet0232 : StripRowPacket :=
  ⟨⟨⟨8,6,5,10⟩,
    ![474,1408,2689,4158,5624,6890,7787],![509,1458,2739,4200,5653,6906,7794]⟩,
    ⟨-72241011156232934029480509,20500837743106697709545832448⟩,
    ⟨-11411497685201433483014079867893,3976098630899321105047781883576320⟩⟩

def packet0233 : StripRowPacket :=
  ⟨⟨⟨8,7,5,10⟩,
    ![469,1403,2684,4155,5621,6889,7786],![503,1452,2734,4196,5650,6905,7794]⟩,
    ⟨-13275852560821231946118975061,3730483481013522515366648971264⟩,
    ⟨-10186540442279368907950559,3512166976006048866496060928⟩⟩

def packet0234 : StripRowPacket :=
  ⟨⟨⟨8,6,5,11⟩,
    ![496,1443,2725,4187,5643,6900,7790],![528,1492,2776,4231,5675,6918,7798]⟩,
    ⟨-614756460149489339630369503,205008377431066977095458324480⟩,
    ⟨-3262122123852834345814945679535,1391634520814762386766723659251712⟩⟩

def packet0235 : StripRowPacket :=
  ⟨⟨⟨8,7,5,11⟩,
    ![491,1438,2720,4184,5641,6899,7790],![522,1486,2771,4228,5672,6917,7797]⟩,
    ⟨-22572550822019281597855063739,7460966962027045030733297942528⟩,
    ⟨-4155420564003969807066041,1756083488003024433248030464⟩⟩

def packet0236 : StripRowPacket :=
  ⟨⟨⟨8,0,6,24⟩,
    ![564,1516,2790,4238,5677,6917,7795],![594,1555,2830,4272,5701,6931,7802]⟩,
    ⟨-165856710012811393,69606697670353885184⟩,
    ⟨-114769531874545399,57817306957404307456⟩⟩

def packet0237 : StripRowPacket :=
  ⟨⟨⟨8,0,6,25⟩,
    ![573,1533,2809,4254,5688,6923,7797],![603,1572,2849,4288,5713,6938,7804]⟩,
    ⟨-5981651566930736039,2784267906814155407360⟩,
    ⟨-1264575696442237579,722716336967553843200⟩⟩

def packet0238 : StripRowPacket :=
  ⟨⟨⟨8,1,5,12⟩,
    ![553,1509,2785,4235,5675,6916,7795],![591,1562,2842,4284,5710,6937,7804]⟩,
    ⟨-8466279737706920905115864862773,3536484535260592146338067607961600⟩,
    ⟨-12875732945944056588680927195607,7323810478866938551974616493424640⟩⟩

def packet0239 : StripRowPacket :=
  ⟨⟨⟨8,0,5,13⟩,
    ![582,1549,2827,4270,5699,6929,7799],![619,1603,2886,4323,5738,6952,7808]⟩,
    ⟨-2664517366674508179,1392133953407077703680⟩,
    ⟨-462244396231538881,361358168483776921600⟩⟩

def packets009 : List StripRowPacket :=
  [packet0216, packet0217, packet0218, packet0219, packet0220, packet0221,
   packet0222, packet0223, packet0224, packet0225, packet0226, packet0227,
   packet0228, packet0229, packet0230, packet0231, packet0232, packet0233,
   packet0234, packet0235, packet0236, packet0237, packet0238, packet0239]

theorem packet0216_membership : packet0216 ∈ packets009 :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem packet0216_shape : checkStripShape packet0216.row = true := by
  decide +kernel

private theorem packet0216_cache : checkStripCache packet0216 = true := by
  decide +kernel

private theorem packet0216_pair (i : Fin 7) : checkEdgePair packet0216 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0216_ok : checkStripPacket packet0216 = true :=
  checkStripPacket_intro packet0216_shape packet0216_cache packet0216_pair

theorem packet0217_membership : packet0217 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

private theorem packet0217_shape : checkStripShape packet0217.row = true := by
  decide +kernel

private theorem packet0217_cache : checkStripCache packet0217 = true := by
  decide +kernel

private theorem packet0217_pair (i : Fin 7) : checkEdgePair packet0217 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0217_ok : checkStripPacket packet0217 = true :=
  checkStripPacket_intro packet0217_shape packet0217_cache packet0217_pair

theorem packet0218_membership : packet0218 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

private theorem packet0218_shape : checkStripShape packet0218.row = true := by
  decide +kernel

private theorem packet0218_cache : checkStripCache packet0218 = true := by
  decide +kernel

private theorem packet0218_pair (i : Fin 7) : checkEdgePair packet0218 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0218_ok : checkStripPacket packet0218 = true :=
  checkStripPacket_intro packet0218_shape packet0218_cache packet0218_pair

theorem packet0219_membership : packet0219 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))

private theorem packet0219_shape : checkStripShape packet0219.row = true := by
  decide +kernel

private theorem packet0219_cache : checkStripCache packet0219 = true := by
  decide +kernel

private theorem packet0219_pair (i : Fin 7) : checkEdgePair packet0219 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0219_ok : checkStripPacket packet0219 = true :=
  checkStripPacket_intro packet0219_shape packet0219_cache packet0219_pair

theorem packet0220_membership : packet0220 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))

private theorem packet0220_shape : checkStripShape packet0220.row = true := by
  decide +kernel

private theorem packet0220_cache : checkStripCache packet0220 = true := by
  decide +kernel

private theorem packet0220_pair (i : Fin 7) : checkEdgePair packet0220 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0220_ok : checkStripPacket packet0220 = true :=
  checkStripPacket_intro packet0220_shape packet0220_cache packet0220_pair

theorem packet0221_membership : packet0221 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))

private theorem packet0221_shape : checkStripShape packet0221.row = true := by
  decide +kernel

private theorem packet0221_cache : checkStripCache packet0221 = true := by
  decide +kernel

private theorem packet0221_pair (i : Fin 7) : checkEdgePair packet0221 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0221_ok : checkStripPacket packet0221 = true :=
  checkStripPacket_intro packet0221_shape packet0221_cache packet0221_pair

theorem packet0222_membership : packet0222 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))

private theorem packet0222_shape : checkStripShape packet0222.row = true := by
  decide +kernel

private theorem packet0222_cache : checkStripCache packet0222 = true := by
  decide +kernel

private theorem packet0222_pair (i : Fin 7) : checkEdgePair packet0222 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0222_ok : checkStripPacket packet0222 = true :=
  checkStripPacket_intro packet0222_shape packet0222_cache packet0222_pair

theorem packet0223_membership : packet0223 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))

private theorem packet0223_shape : checkStripShape packet0223.row = true := by
  decide +kernel

private theorem packet0223_cache : checkStripCache packet0223 = true := by
  decide +kernel

private theorem packet0223_pair (i : Fin 7) : checkEdgePair packet0223 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0223_ok : checkStripPacket packet0223 = true :=
  checkStripPacket_intro packet0223_shape packet0223_cache packet0223_pair

theorem packet0224_membership : packet0224 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))

private theorem packet0224_shape : checkStripShape packet0224.row = true := by
  decide +kernel

private theorem packet0224_cache : checkStripCache packet0224 = true := by
  decide +kernel

private theorem packet0224_pair (i : Fin 7) : checkEdgePair packet0224 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0224_ok : checkStripPacket packet0224 = true :=
  checkStripPacket_intro packet0224_shape packet0224_cache packet0224_pair

theorem packet0225_membership : packet0225 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))

private theorem packet0225_shape : checkStripShape packet0225.row = true := by
  decide +kernel

private theorem packet0225_cache : checkStripCache packet0225 = true := by
  decide +kernel

private theorem packet0225_pair (i : Fin 7) : checkEdgePair packet0225 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0225_ok : checkStripPacket packet0225 = true :=
  checkStripPacket_intro packet0225_shape packet0225_cache packet0225_pair

theorem packet0226_membership : packet0226 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))

private theorem packet0226_shape : checkStripShape packet0226.row = true := by
  decide +kernel

private theorem packet0226_cache : checkStripCache packet0226 = true := by
  decide +kernel

private theorem packet0226_pair (i : Fin 7) : checkEdgePair packet0226 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0226_ok : checkStripPacket packet0226 = true :=
  checkStripPacket_intro packet0226_shape packet0226_cache packet0226_pair

theorem packet0227_membership : packet0227 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))

private theorem packet0227_shape : checkStripShape packet0227.row = true := by
  decide +kernel

private theorem packet0227_cache : checkStripCache packet0227 = true := by
  decide +kernel

private theorem packet0227_pair (i : Fin 7) : checkEdgePair packet0227 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0227_ok : checkStripPacket packet0227 = true :=
  checkStripPacket_intro packet0227_shape packet0227_cache packet0227_pair

theorem packet0228_membership : packet0228 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))

private theorem packet0228_shape : checkStripShape packet0228.row = true := by
  decide +kernel

private theorem packet0228_cache : checkStripCache packet0228 = true := by
  decide +kernel

private theorem packet0228_pair (i : Fin 7) : checkEdgePair packet0228 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0228_ok : checkStripPacket packet0228 = true :=
  checkStripPacket_intro packet0228_shape packet0228_cache packet0228_pair

theorem packet0229_membership : packet0229 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))

private theorem packet0229_shape : checkStripShape packet0229.row = true := by
  decide +kernel

private theorem packet0229_cache : checkStripCache packet0229 = true := by
  decide +kernel

private theorem packet0229_pair (i : Fin 7) : checkEdgePair packet0229 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0229_ok : checkStripPacket packet0229 = true :=
  checkStripPacket_intro packet0229_shape packet0229_cache packet0229_pair

theorem packet0230_membership : packet0230 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))

private theorem packet0230_shape : checkStripShape packet0230.row = true := by
  decide +kernel

private theorem packet0230_cache : checkStripCache packet0230 = true := by
  decide +kernel

private theorem packet0230_pair (i : Fin 7) : checkEdgePair packet0230 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0230_ok : checkStripPacket packet0230 = true :=
  checkStripPacket_intro packet0230_shape packet0230_cache packet0230_pair

theorem packet0231_membership : packet0231 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))

private theorem packet0231_shape : checkStripShape packet0231.row = true := by
  decide +kernel

private theorem packet0231_cache : checkStripCache packet0231 = true := by
  decide +kernel

private theorem packet0231_pair (i : Fin 7) : checkEdgePair packet0231 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0231_ok : checkStripPacket packet0231 = true :=
  checkStripPacket_intro packet0231_shape packet0231_cache packet0231_pair

theorem packet0232_membership : packet0232 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))

private theorem packet0232_shape : checkStripShape packet0232.row = true := by
  decide +kernel

private theorem packet0232_cache : checkStripCache packet0232 = true := by
  decide +kernel

private theorem packet0232_pair (i : Fin 7) : checkEdgePair packet0232 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0232_ok : checkStripPacket packet0232 = true :=
  checkStripPacket_intro packet0232_shape packet0232_cache packet0232_pair

theorem packet0233_membership : packet0233 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))

private theorem packet0233_shape : checkStripShape packet0233.row = true := by
  decide +kernel

private theorem packet0233_cache : checkStripCache packet0233 = true := by
  decide +kernel

private theorem packet0233_pair (i : Fin 7) : checkEdgePair packet0233 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0233_ok : checkStripPacket packet0233 = true :=
  checkStripPacket_intro packet0233_shape packet0233_cache packet0233_pair

theorem packet0234_membership : packet0234 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))

private theorem packet0234_shape : checkStripShape packet0234.row = true := by
  decide +kernel

private theorem packet0234_cache : checkStripCache packet0234 = true := by
  decide +kernel

private theorem packet0234_pair (i : Fin 7) : checkEdgePair packet0234 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0234_ok : checkStripPacket packet0234 = true :=
  checkStripPacket_intro packet0234_shape packet0234_cache packet0234_pair

theorem packet0235_membership : packet0235 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))

private theorem packet0235_shape : checkStripShape packet0235.row = true := by
  decide +kernel

private theorem packet0235_cache : checkStripCache packet0235 = true := by
  decide +kernel

private theorem packet0235_pair (i : Fin 7) : checkEdgePair packet0235 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0235_ok : checkStripPacket packet0235 = true :=
  checkStripPacket_intro packet0235_shape packet0235_cache packet0235_pair

theorem packet0236_membership : packet0236 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))

private theorem packet0236_shape : checkStripShape packet0236.row = true := by
  decide +kernel

private theorem packet0236_cache : checkStripCache packet0236 = true := by
  decide +kernel

private theorem packet0236_pair (i : Fin 7) : checkEdgePair packet0236 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0236_ok : checkStripPacket packet0236 = true :=
  checkStripPacket_intro packet0236_shape packet0236_cache packet0236_pair

theorem packet0237_membership : packet0237 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))

private theorem packet0237_shape : checkStripShape packet0237.row = true := by
  decide +kernel

private theorem packet0237_cache : checkStripCache packet0237 = true := by
  decide +kernel

private theorem packet0237_pair (i : Fin 7) : checkEdgePair packet0237 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0237_ok : checkStripPacket packet0237 = true :=
  checkStripPacket_intro packet0237_shape packet0237_cache packet0237_pair

theorem packet0238_membership : packet0238 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0238_shape : checkStripShape packet0238.row = true := by
  decide +kernel

private theorem packet0238_cache : checkStripCache packet0238 = true := by
  decide +kernel

private theorem packet0238_pair (i : Fin 7) : checkEdgePair packet0238 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0238_ok : checkStripPacket packet0238 = true :=
  checkStripPacket_intro packet0238_shape packet0238_cache packet0238_pair

theorem packet0239_membership : packet0239 ∈ packets009 :=
  List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))))))))))))))))))))))))))))))))))))))))

private theorem packet0239_shape : checkStripShape packet0239.row = true := by
  decide +kernel

private theorem packet0239_cache : checkStripCache packet0239 = true := by
  decide +kernel

private theorem packet0239_pair (i : Fin 7) : checkEdgePair packet0239 i = true := by
  fin_cases i <;> decide +kernel

private theorem packet0239_ok : checkStripPacket packet0239 = true :=
  checkStripPacket_intro packet0239_shape packet0239_cache packet0239_pair

theorem packets009_checked : packets009.all checkStripPacket = true := by
  simp only [packets009, List.all_cons, List.all_nil, Bool.true_and, packet0216_ok,
    packet0217_ok, packet0218_ok, packet0219_ok, packet0220_ok, packet0221_ok,
    packet0222_ok, packet0223_ok, packet0224_ok, packet0225_ok, packet0226_ok,
    packet0227_ok, packet0228_ok, packet0229_ok, packet0230_ok, packet0231_ok,
    packet0232_ok, packet0233_ok, packet0234_ok, packet0235_ok, packet0236_ok,
    packet0237_ok, packet0238_ok, packet0239_ok]

theorem packets009_valid : packets009.all (fun p => p.row.rect.validAt 8 6) = true := by
  decide +kernel

end RKCert.ReviewedNative.ThreeInteriorPencil
