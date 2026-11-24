module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.N6K1J2W1
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000
noncomputable section

namespace At0
private def m : Array Nat := #[65302194596872192, 966022120070971583, 1026820715040668672, 803892533685911552, 113716095675793408, 136443895448862720]
private def l : Array Nat := #[1, 1024, 1048576, 1073741824, 1099511627776, 1125899906842624]
private def u : Array Nat := #[966022120070971583, 1026820715040668672, 803892533685911552, 113716095675793408, 136443895448862720, 65302194596872192]
private def swaps : List (Fin 6×Fin 6) := [(4, 5), (3, 4), (2, 3), (1, 2), (0, 1)]
private theorem evaluated : (rowMatrix 1009 6 m).det=(12:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 12 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[977, 640, 645, 963, 327, 142, 334]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (0:ZMod 1009)=(12:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 0 m coefficients 12
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[430093764413883197, 729583139634869548, 128352590249635840, 622623538930515968, 93235609623068672, 538510008959107072]
private def l : Array Nat := #[1, 1695, 1735680, 1777336320, 1819992391680, 1863672209080320]
private def u : Array Nat := #[430093764413883197, 689050742988534784, 140737489224597504, 478508350540087296, 512070052845977600, 632755747645554688]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(657:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 657 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[1001, 240, 827, 728, 1002, 881, 334]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (1:ZMod 1009)=(657:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 1 m coefficients 657
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

namespace At2
private def m : Array Nat := #[1093248809544187975, 1124774006935854489, 772367336168907776, 363665746574704640, 252280083618725888, 16212298951557120]
private def l : Array Nat := #[1, 1584, 1622016, 1660944384, 1700807049216, 1741626418397184]
private def u : Array Nat := #[1093248809544187975, 91197892454325248, 823032831976407040, 694680318757568512, 890664891638087680, 5629499534213120]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(635:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 635 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[306, 824, 583, 426, 108, 876, 442]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (2:ZMod 1009)=(635:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 2 m coefficients 635
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At2

namespace At3
private def m : Array Nat := #[1006554516717306609, 271341877549843974, 883831427661568000, 823033640972713984, 220378970288291840, 727900886843523072]
private def l : Array Nat := #[1, 1424, 1458176, 1493172224, 1529008357376, 1565704557953024]
private def u : Array Nat := #[1006554516717306609, 941252322121204736, 409827566880292864, 480760068749393920, 1042285346085142528, 1068479011593650176]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(410:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 410 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[158, 169, 764, 768, 434, 31, 187]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (3:ZMod 1009)=(410:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 3 m coefficients 410
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At3

namespace At4
private def m : Array Nat := #[829788231343014745, 359162070283675251, 651896046961150976, 269090998589587456, 873515382504161280, 706628635380940800]
private def l : Array Nat := #[1, 1146, 1173504, 1201668096, 1230508130304, 1260040325431296]
private def u : Array Nat := #[829788231343014745, 231935380810458112, 756604738296872960, 1118019527691468800, 799205315416424448, 1016687615878889472]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(545:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 545 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[760, 88, 786, 727, 179, 556, 351]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (4:ZMod 1009)=(545:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 4 m coefficients 545
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At4

namespace At5
private def m : Array Nat := #[909727124728840575, 396316767208996576, 506654958481539072, 369295581459251200, 448530066150785024, 86377633478082560]
private def l : Array Nat := #[1, 1674, 1714176, 1755316224, 1797443813376, 1840582464897024]
private def u : Array Nat := #[909727124728840575, 946881821655038976, 763360137240903680, 631630258981830656, 1133076419237117952, 9007199254740992]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(209:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 209 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[975, 175, 46, 186, 238, 330, 363]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (5:ZMod 1009)=(209:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 5 m coefficients 209
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At5

namespace At6
private def m : Array Nat := #[940126422213591380, 280349076804162381, 399694467286512640, 945756287706071040, 575709593661865984, 410756653416185856]
private def l : Array Nat := #[1, 1071, 1096704, 1123024896, 1149977493504, 1177576953348096]
private def u : Array Nat := #[940126422213591380, 399694466929479680, 926615623687995392, 564076218400374784, 192902718023532544, 449234062830206976]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(881:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 881 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[405, 586, 722, 202, 846, 263, 444]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (6:ZMod 1009)=(881:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 6 m coefficients 881
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At6

namespace At7
private def m : Array Nat := #[628252148018184920, 320881473450894266, 873698328474216448, 335518954923491328, 1128953175471030272, 588768685464748032]
private def l : Array Nat := #[1, 1333, 1364992, 1397751808, 1431297851392, 1465648999825408]
private def u : Array Nat := #[628252148018184920, 452611762551480320, 748723438813708288, 730709821224910848, 274394121827778560, 113715890591105024]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(744:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 744 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 739, 858, 886, 697, 432, 431]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (7:ZMod 1009)=(744:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 7 m coefficients 744
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At7

namespace At8
private def m : Array Nat := #[693554342615056922, 790381734604073014, 726205440477681664, 1090997587460227072, 277562972321087488, 621556122205028352]
private def l : Array Nat := #[1, 1628, 1667072, 1707081728, 1748051689472, 1790004930019328]
private def u : Array Nat := #[693554342615056922, 1079738010662627328, 647392446998642688, 861314006407708672, 347368708563271680, 198158383604301824]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(516:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 516 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 996, 941, 935, 556, 126, 325]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (8:ZMod 1009)=(516:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 8 m coefficients 516
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At8

namespace At9
private def m : Array Nat := #[115967690404791051, 399694466929929379, 841047231228447744, 307371511183835136, 217029476691738624, 1119323727796895744]
private def l : Array Nat := #[1, 1054, 1079296, 1105199104, 1131723882496, 1158885255675904]
private def u : Array Nat := #[115967690404791051, 328762772798843904, 66428095320555520, 586594687909888000, 795741853788930048, 1129277606563151872]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(933:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 933 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[736, 264, 763, 834, 265, 791, 545]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (9:ZMod 1009)=(933:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 9 m coefficients 933
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At9

namespace At10
private def m : Array Nat := #[319755573543305658, 547187354725968144, 1040331514386333696, 665407319823089664, 867429204466073600, 980957886022680576]
private def l : Array Nat := #[1, 1956, 2002944, 2051014656, 2100239007744, 2150644743929856]
private def u : Array Nat := #[319755573543305658, 175640385467901952, 932245123329163264, 878202401931132928, 326996957123837952, 1129277606563151872]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(403:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 403 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[637, 614, 694, 647, 242, 776, 879]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (10:ZMod 1009)=(403:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 10 m coefficients 403
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At10

namespace At11
private def m : Array Nat := #[850054429666181656, 605734149881880957, 666532745413260288, 1027947190872440832, 208881230094008320, 936041736516403200]
private def l : Array Nat := #[1, 1949, 1995776, 2043674624, 2092722814976, 2142948162535424]
private def u : Array Nat := #[850054429666181656, 440226863576014848, 156500087613161472, 541558430716919808, 258420416899448832, 1008806316530991104]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(973:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 973 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[337, 756, 303, 469, 410, 42, 150]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (11:ZMod 1009)=(973:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 11 m coefficients 973
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At11

namespace At12
private def m : Array Nat := #[636133447366082612, 184647584722244074, 1107885508388169728, 406449922718564352, 576518453041561600, 905762285799079936]
private def l : Array Nat := #[1, 1926, 1972224, 2019557376, 2068026753024, 2117659395096576]
private def u : Array Nat := #[636133447366082612, 88946092640620544, 400820366890500096, 124974945494106112, 316435048427421696, 676665844012417024]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(245:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 245 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[874, 568, 381, 512, 592, 708, 633]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (12:ZMod 1009)=(245:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 12 m coefficients 245
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At12

namespace At13
private def m : Array Nat := #[758856537211929584, 446982263017554519, 528047057366768640, 264587561067872256, 961501571428909056, 355317078120464384]
private def l : Array Nat := #[1, 1434, 1468416, 1503657984, 1539745775616, 1576699674230784]
private def u : Array Nat := #[758856537211929584, 588845651279724544, 1076360311998513152, 873699410041634816, 595583458533703680, 866942928268820480]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(239:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 239 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[799, 535, 294, 825, 354, 407, 70]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (13:ZMod 1009)=(239:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 13 m coefficients 239
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At13

namespace At14
private def m : Array Nat := #[95701492081623417, 1106759608426686148, 597852850929471488, 350155276571115520, 762649513025339392, 186551938861498368]
private def l : Array Nat := #[1, 1885, 1930240, 1976565760, 2024003338240, 2072579418357760]
private def u : Array Nat := #[95701492081623417, 502151358452196352, 1074108511523176448, 273594082163425280, 357324786352783360, 750975237864030208]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(694:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 694 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[959, 134, 756, 648, 314, 650, 544]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (14:ZMod 1009)=(694:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 14 m coefficients 694
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At14

namespace At15
private def m : Array Nat := #[209417382672728241, 1090997009730684721, 721701840472556544, 287104667153858560, 730904530346049536, 920758524890316800]
private def l : Array Nat := #[1, 1878, 1923072, 1969225728, 2016487145472, 2064882836963328]
private def u : Array Nat := #[209417382672728241, 605734149881512960, 319755573728903168, 999799307328552960, 63245008341303296, 468374361246531584]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(58:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 58 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[537, 210, 923, 427, 881, 937, 915]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (15:ZMod 1009)=(58:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 15 m coefficients 58
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At15

namespace At16
private def m : Array Nat := #[629378047925027224, 627126248111760286, 692428443136980992, 982911057731256320, 408025361306091520, 618011296717078528]
private def l : Array Nat := #[1, 1051, 1076224, 1102053376, 1128502657024, 1155586720792576]
private def u : Array Nat := #[629378047925027224, 674414044199149568, 659777345837596672, 209417820759392256, 433920064878542848, 273593677362757632]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(516:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 516 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[493, 262, 907, 436, 442, 813, 61]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (16:ZMod 1009)=(516:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 16 m coefficients 516
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At16

namespace At17
private def m : Array Nat := #[891712726219358269, 244320279784911898, 899594025631246336, 1042583379261784064, 515729255460503552, 130632976496066560]
private def l : Array Nat := #[1, 1256, 1286144, 1317011456, 1348619730944, 1380986604486656]
private def u : Array Nat := #[891712726219358269, 124974889659593728, 306244774725156864, 427842030098448384, 91264962663546880, 557320453887098880]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(509:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 509 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[280, 729, 629, 42, 60, 788, 834]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (17:ZMod 1009)=(509:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 17 m coefficients 509
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At17

namespace At18
private def m : Array Nat := #[711568741124538513, 129478489287050375, 576460752455605248, 421086720993263616, 540591529425633280, 183670118885097472]
private def l : Array Nat := #[1, 1686, 1726464, 1767899136, 1810328715264, 1853776604430336]
private def u : Array Nat := #[711568741124538513, 524669356588811264, 871446528048234496, 628252303710748672, 425749593972539392, 179018085187977216]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(276:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 276 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[952, 186, 56, 640, 557, 103, 605]
theorem checked : (nodeMomentNorm 6 1 2 1).eval₂ order15Reduce (18:ZMod 1009)=(276:ZMod 1009) :=
  nodeMomentNorm_eval_sparse axes6K1 2 1 (by decide) 18 m coefficients 276
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At18


def candidate : List Nat := [12, 535, 705, 649, 714, 854, 874, 419, 914, 687, 734, 102, 978, 994, 360, 403, 115, 408, 290]
private def values : Fin 19 → Nat := fun i => (#[12, 657, 635, 410, 545, 209, 881, 744, 516, 933, 403, 973, 245, 239, 694, 58, 516, 509, 276] : Array Nat)[i.val]!

theorem exactReduction : (nodeMomentNorm 6 1 2 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=18)
    (by decide) ((nodeMomentNorm_degree (by decide) (by decide) 2 1).trans (by decide)) (by decide) values
  · intro i
    rw [eval_map]
    fin_cases i
    · exact At0.checked
    · exact At1.checked
    · exact At2.checked
    · exact At3.checked
    · exact At4.checked
    · exact At5.checked
    · exact At6.checked
    · exact At7.checked
    · exact At8.checked
    · exact At9.checked
    · exact At10.checked
    · exact At11.checked
    · exact At12.checked
    · exact At13.checked
    · exact At14.checked
    · exact At15.checked
    · exact At16.checked
    · exact At17.checked
    · exact At18.checked
  · decide +kernel

end

end RKCert.FixedPolynomial.FixedReplay.N6K1J2W1
